module

public import Certificates.Data.TabBFiveCentA2
public import Certificates.Certificate17561

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBFiveCent

open CFSG.YGroups CFSG.HardMathSupport.Dickson.I271.TabBFiveCentNative
open CFSG.Certificates.CosetEnumeration (evalWord)

@[expose] noncomputable def dFive : YGroup 4 3 2 := evalWord (yGen 4 3 2) fiveWord.toList

section Certified


theorem card_centralizer_rho_dFive_le :
    Nat.card ↥(Subgroup.centralizer {rho432F dFive} ⊓ rho432F.range) ≤ 25200 ∧
      orderOf (rho432F dFive) = 5 ∧
      ∃ e : YGroup 4 3 2, orderOf (rho432F e) = 7 ∧
        rho432F e * rho432F dFive = rho432F dFive * rho432F e :=
  Certificates.certificate17561

end Certified

end CFSG.HardMathSupport.Dickson.I271.TabBFiveCent

end
