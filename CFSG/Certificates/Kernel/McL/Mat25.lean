module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KC.McL.Mat

#kc_repo #kc_nat_items_gz CFSG.KC.McL.Mat
  "CFSG/Certificates/Kernel/McL/Data/Mat25.items.gz" 560 7728989391319353569
  sl[5] sh[5]

#kc_repo #kc_json_gz CFSG.KC.McL.Mat
  "CFSG/Certificates/Kernel/McL/Data/Mat25.json.gz" 601 3767851922313897618
  (c0 : Nat) (rowMask : Nat) (ident : Nat) (m625 : Nat)

@[expose] noncomputable def mulStep (A B acc k k25 : Nat) : Nat :=
  Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c0) rowMask)
    (Nat.mul (Nat.land (Nat.shiftRight B k25) rowMask) c0))

@[expose] noncomputable def mul25 (A B : Nat) : Nat :=
  mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (nat_lit 0) (nat_lit 0) (nat_lit 0)) (nat_lit 1) (nat_lit 25)) (nat_lit 2) (nat_lit 50)) (nat_lit 3) (nat_lit 75)) (nat_lit 4) (nat_lit 100)) (nat_lit 5) (nat_lit 125)) (nat_lit 6) (nat_lit 150)) (nat_lit 7) (nat_lit 175)) (nat_lit 8) (nat_lit 200)) (nat_lit 9) (nat_lit 225)) (nat_lit 10) (nat_lit 250)) (nat_lit 11) (nat_lit 275)) (nat_lit 12) (nat_lit 300)) (nat_lit 13) (nat_lit 325)) (nat_lit 14) (nat_lit 350)) (nat_lit 15) (nat_lit 375)) (nat_lit 16) (nat_lit 400)) (nat_lit 17) (nat_lit 425)) (nat_lit 18) (nat_lit 450)) (nat_lit 19) (nat_lit 475)) (nat_lit 20) (nat_lit 500)) (nat_lit 21) (nat_lit 525)) (nat_lit 22) (nat_lit 550)) (nat_lit 23) (nat_lit 575)) (nat_lit 24) (nat_lit 600)
@[expose] noncomputable def sp4 (x : Nat) : Nat :=
  Nat.lor (Nat.land x sl4) (Nat.shiftLeft (Nat.land x sh4) (nat_lit 384))
@[expose] noncomputable def sp3 (x : Nat) : Nat :=
  Nat.lor (Nat.land x sl3) (Nat.shiftLeft (Nat.land x sh3) (nat_lit 192))
@[expose] noncomputable def sp2 (x : Nat) : Nat :=
  Nat.lor (Nat.land x sl2) (Nat.shiftLeft (Nat.land x sh2) (nat_lit 96))
@[expose] noncomputable def sp1 (x : Nat) : Nat :=
  Nat.lor (Nat.land x sl1) (Nat.shiftLeft (Nat.land x sh1) (nat_lit 48))
@[expose] noncomputable def sp0 (x : Nat) : Nat :=
  Nat.lor (Nat.land x sl0) (Nat.shiftLeft (Nat.land x sh0) (nat_lit 24))
@[expose] noncomputable def spreadS (x : Nat) : Nat := Nat.mul (sp0 (sp1 (sp2 (sp3 (sp4 x))))) rowMask
@[expose] noncomputable def fold (s t : Nat) : Nat := Nat.xor t (Nat.shiftRight t s)

@[expose] noncomputable def vecmul (x M : Nat) : Nat :=
  Nat.land (fold (nat_lit 25) (fold (nat_lit 50) (fold (nat_lit 100) (fold (nat_lit 200) (fold (nat_lit 400)
    (Nat.land (spreadS (Nat.land x rowMask)) M)))))) rowMask

end CFSG.KC.McL.Mat

end
