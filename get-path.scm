(begin
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;           Supporting procedures           ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;;Lookup procedure for a 2-dimensional table, used to store edges
  (define (lookup key-1 key-2 table) ;;for node table
    (let ((subtable (assoc key-1 (cdr table))))
      (if subtable
	  (let ((record (assoc key-2 (cdr subtable))))
	    (if record
		(cdr record)
		#f))
	  #f)))

  ;;Insert two keys and a value into a 2-dimensional table
  (define (insert! key-1 key-2 value table)
    (let ((subtable (assoc key-1 (cdr table))))
      (if subtable
	  (let ((record (assoc key-2 (cdr subtable))))
	    (if record
		(set-cdr! record value)
		(set-cdr! subtable
			  (cons (cons key-2 value)
				(cdr subtable)))))
	  (set-cdr! table
		    (cons (list key-1
				(cons key-2 value))
			  (cdr table)))))
    'insert-successful)

  ;;Anchor location for table
  (define (make-table)
    (list '*table*))

  ;;Read contents of a file
  ;;Store every 3 numbers as an element
  ;;pa1.in node format per line: n1 n2 cost
  (define (read-file)
    (let ((expr (read)))
      (if (eof-object? expr)
	  '()
	  (cons expr (read-file)))))

  ;;Store contents of pa1.in into the list pa1-contents
  (define pa1-contents (with-input-from-file "node-input.in" read-file))

  ;;--------------------------------------------------------
  ;;The supporting procedures above are credited to
  ;;Carl Offner and Bill Campbell               
  ;;--------------------------------------------------------
  
  (define pa1-end-node (- (car pa1-contents) 1))

  ;;Format pa1 into a list of lists containing 3 elements each
  (define (format-to-3 data-list)
    (define (f-t-3-iter data-list format-3-list)
      (if (null? data-list)
	  format-3-list
	  (f-t-3-iter (cdddr data-list)
		      (cons (list (car data-list)
					 (cadr data-list)
					 (caddr data-list))
			    format-3-list))))
    (f-t-3-iter data-list '()))

  (define pa1 (format-to-3 (cdr pa1-contents)))

  (define node-table (make-table))

  ;;Return the list with a lower cost
  ;;Param syntax: car is cost, cdr is list of nodes
  (define (get-min list1 list2)
    (if (<= (car list1) (car list2))
	list1
	list2))

  ;;Insert pa1 nodes into my node-table
  (define (fill-with-nodes some-table)
    (define (f-w-n-iter data-list my-table)
      (if (null? data-list)
	  'node-table-filled
	  (begin (insert! (caar data-list) ;;from-node
			  (cadar data-list) ;;to-node
			  (caddar data-list) ;;move cost
			  my-table)
		 (f-w-n-iter (cdr data-list) my-table))))
    (f-w-n-iter pa1 some-table))
  
  (fill-with-nodes node-table)

  ;;detected nodes that have not been expanded yet
  (define unexpanded-f-paths '())

  ;;return a new unexpanded-path with obj removed. set! handled by called
  (define (remove-from-unexpanded obj my-list)
    (if (null? my-list)
	'()
	(if (equal? obj (car my-list))
	    (remove-from-unexpanded obj (cdr my-list))
	    (cons (car my-list)
		  (remove-from-unexpanded obj (cdr my-list))))))

  ;;add an object to the rightnost (end) of a list
  ;;used to add nodes onto a cumulative path
  (define (cons-to-end obj my-list)
    (if (null? my-list) ;;input 5 (list 0 1 3)
	(cons obj '())
	(cons (car my-list) (cons-to-end obj (cdr my-list)))))

  ;;return #t if obj is found in the list
  (define (found-in-list? obj my-list)
    (if (null? my-list)
	#f
	(if (equal? obj (car my-list))
	    #t
	    (found-in-list? obj (cdr my-list)))))
  
  ;;return lowest (f = g + h) of node and node-list
  (define (get-lowest node node-list) ;;input and output: (g h . path)
    (define (g-l-iter node-list lowest)
      (if (null? node-list)
	  (if (equal? lowest node)
	      lowest
	      (begin (set! unexpanded-f-paths ;;new lowest was from unexpanded paths. remove it from there
			   (remove-from-unexpanded lowest unexpanded-f-paths))
		     lowest))
	  (if (> (+ (car lowest) (cadr lowest))
		 (+ (caar node-list) (cadar node-list)))
	      (begin (set! unexpanded-f-paths ;;add this current lowest node to unexpanded-f-paths
			   (cons lowest ;;did i add the path and cost before putting it in?
				 unexpanded-f-paths))
		     (g-l-iter (cdr node-list) (car node-list))) ;;keep node from unexpanded
	      (g-l-iter (cdr node-list) lowest)))) ;;initial-node is still lowest
      (g-l-iter node-list node))

  ;;input list of nodes, return last one
  (define (get-last-element obj)
    (define (g-l-e-iter obj last)
      (if (null? obj)
	  last
	  (g-l-e-iter (cdr obj) (car obj))))
    (g-l-e-iter obj '()))

    
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;            A* search procedures           ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;;h function: ignoring cost, h is the shortest amount
  ;;of moves required to reach the goal node.
  ;;Will return 10000000 if there's no path to the goal node.
  ;;Reaching a node that has already been visited (blacklist) means
  ;;it is in a loop, and should return 10000000.
  (define (calculate-h my-node) ;;input a node like 3, output a number
    (define (calculate-h-blacklist my-node blacklist)
      (define (c-h-iter children-list saved-min blacklist)
	(if (null? children-list)
	    saved-min
	    (if (found-in-list? (caar children-list) blacklist)
		(c-h-iter (cdr children-list) saved-min blacklist) ;;found. skip it
		(let ((possible-min (+ 1 (calculate-h-blacklist (caar children-list)
								(cons (caar children-list)
								      blacklist))))) ;;not found. add it then recurse
		  (if (>= saved-min possible-min)
		      (c-h-iter (cdr children-list)
				possible-min
				(cons (caar children-list) blacklist))
		      (c-h-iter (cdr children-list)
				saved-min
				(cons (caar children-list) blacklist)))))))
      (if (equal? my-node pa1-end-node)
	  0
	  (let ((children (let ((maybe-false (assoc my-node (cdr node-table))))
			    (if maybe-false
				(cdr maybe-false)
				#f))))
	    (if children ;;if has children
		(c-h-iter children 10000000 blacklist)
		10000000)))) ;;dead-end, return infinity
    (calculate-h-blacklist my-node (list my-node)))

  ;;this is the main function that recurses through nodes
  ;;to compile a shortest path, and eventually returns
  ;;an unformatted result: (g h . path)
  (define (get-path current-node g h path)
    (define (do-subnodes subnode-list)
      (define (d-s-iter subnode-list lowest-f-path)
	(if (null? subnode-list)
	    (cons (cdr lowest-f-path) ;;return as (g h . path)
		  (cons (calculate-h (car lowest-f-path))
			(cons-to-end (car lowest-f-path) path)))
	    (let ((subnode-h (calculate-h (caar subnode-list))))
	      (let ((subnode-f (+ (cdar subnode-list) ;;subnode-list's f = g + h
				  subnode-h)))
		(let ((unexpanded-before-set unexpanded-f-paths))
		  (let ((lowest-h (calculate-h (car lowest-f-path))))
		    (if (< (+ (cdr lowest-f-path) ;;if my-node-f is lower than subnode-f
			      lowest-h)
			   subnode-f)
			(begin (set! unexpanded-f-paths
				     (cons (cons (+ (cdar subnode-list)
						    g)
						 (cons subnode-h
						       (cons-to-end (caar subnode-list) path))) ;;add itself to path
					   unexpanded-before-set)) ;;save subnode to unexpanded-f-paths
			       (d-s-iter (cdr subnode-list) lowest-f-path))
			(begin (set! unexpanded-f-paths
				     (cons (cons (+ (cdr lowest-f-path)
						    g)
						 (cons lowest-h
						       (cons-to-end (car lowest-f-path) path))) ;;add itself to path
					   unexpanded-before-set)) ;;add my-node to unexpanded-f-paths
			       (d-s-iter (cdr subnode-list) (car subnode-list))))))))))
      (d-s-iter (cdr subnode-list) (car subnode-list)))
    (let ((subnodes (let ((maybe-false (assoc current-node (cdr node-table)))) ;;get list of children
		      (if maybe-false
			  (cdr maybe-false)
			  maybe-false))))
      (if subnodes ;;check if current-node has children
	  (let ((lowest-f-subnode (do-subnodes subnodes)))
	    (let ((unexpanded-before-set unexpanded-f-paths)) ;;save it for use before set!-ing it in get-lowest
	      (let ((lowest-of-unexpanded (get-lowest lowest-f-subnode
						      unexpanded-before-set)))
		(if (equal? lowest-of-unexpanded lowest-f-subnode)
		    (get-path (get-last-element (cddr lowest-of-unexpanded))
			      (+ (car lowest-of-unexpanded)
				 g)
			      (cadr lowest-of-unexpanded)
			      (cddr lowest-of-unexpanded))
		    (get-path (get-last-element (cddr lowest-of-unexpanded))
			      (+ (car lowest-of-unexpanded)
				 g)
			      (cadr lowest-of-unexpanded)
			      (cddr lowest-of-unexpanded))))))
	  (if (equal? current-node pa1-end-node) ;;current-node doesn't have children, it's a dead end or the goal node
	      (let ((unexpanded-before-set unexpanded-f-paths))
		(let ((current-g-h-path (cons g (cons h  path))))
			 (let ((lowest-of-unexpanded (get-lowest current-g-h-path ;;get-lowest handles saving in unexpanded-f-paths
								 unexpanded-before-set)))
			   (if (equal? lowest-of-unexpanded current-g-h-path)
			       current-g-h-path
			       (get-path (get-last-element (cddr lowest-of-unexpanded))
					 (car lowest-of-unexpanded)
					 (cadr lowest-of-unexpanded)
					 (cddr lowest-of-unexpanded))))))
	      (list 10000000))))) ;;current-node is a dead-end

  (define a-star-unformatted-output (get-path 0 0 (calculate-h 0) (list 0)))
  (define a-star-path (cddr a-star-unformatted-output))
  (define (print-a-star-formatted path-list) ;;format and print output
    (if (null? path-list)
  	'()
  	(if (equal? (car path-list) pa1-end-node)
  	    (begin (display (car path-list))
  		   (print-a-star-formatted (cdr path-list)))
  	    (begin (display (car path-list))
  		   (display ">")
  		   (print-a-star-formatted (cdr path-list)))))))
