sig pid{}

sig freeNode{
   id: one pid,
startF : lone pid,
endF : lone pid,
    freenext : lone freeNode
}
one sig freeHead in freeNode {}   
                  
fact{
    all n : freeNode | n not in n.^freenext      
    no freenext.freeHead                          
    all n : freeNode - freeHead | some freenext.n     
}
sig readyNode{
  id: one pid,
startR : lone pid,
endR : lone pid,
   readynext : lone readyNode
}
one sig readyHead in readyNode {}                     
fact{
    all n : readyNode | n not in n.^readynext        
    no readynext.readyHead                         
    all n : readyNode - readyHead | some readynext.n    
}

sig blockedNode{
   id: one pid,
startB : lone pid,
endB : lone pid,
   blockednext : lone blockedNode
}
one sig blockedHead in blockedNode {}  
                  
fact{
    all n : blockedNode | n not in n.^blockednext        
    no blockednext.blockedHead                           
    all n : blockedNode - blockedHead | some blockednext.n      
}

fact noshareidbetweenchain{
freeNode.id &  readyNode.id = none
freeNode.id &  blockedNode.id = none
blockedNode.id & readyNode.id = none
}

fact noshareidbetweenNode{
freeNode.id & freeNode.freenext.id = none
readyNode.id & readyNode.readynext.id = none
blockedNode.id & blockedNode.blockednext.id = none
}

pred pushReadyfromFree (beforeFNode,afterFNode:freeNode, beforeRNode,afterRNode:readyNode ) {
       afterRNode. id = beforeRNode. id+beforeFNode.endF
      afterFNode. id = beforeFNode. id - beforeFNode.endF
}


