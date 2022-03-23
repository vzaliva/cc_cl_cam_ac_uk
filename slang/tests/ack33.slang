let ack( xy : int * int) : int = 
	let x : int = fst xy
	and y : int = snd xy in
    	if x = 0
    	then y + 1 
    	else if y = 0 
            then ack (x-1, 1)
            else 
         		let inner : int = ack (x, y-1)
         		in ack (x-1, inner) end
            end 
        end
    end
in 
    ack (3, 3)
end 