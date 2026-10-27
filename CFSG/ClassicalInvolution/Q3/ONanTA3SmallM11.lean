module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallGood
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import Certificates.Certificate9740

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 Check

theorem m11_goodCheck :
    goodCheck 100 (elemsT Q) = true :=
  Certificates.certificate9740

theorem concreteLeaf_m11 :
    ConcreteLeaf (Equiv.Perm (Fin 11)) Q.originalSubgroup Q.originalSubgroup := by
  intro X hPX hXA R S t hd hc hE2
  have hX : X = Q.originalSubgroup := le_antisymm hXA hPX
  subst hX
  refine Or.inr (good_of_goodCheck (ι := Q.originalSubgroup.subtype) Subtype.val_injective
    (fun m => ?_) m11_goodCheck hd hc.1)
  rw [mem_elemsT Q Q_ok m]
  exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

section Leaf


theorem smallSimpleLeaf_m11_of_check :
    SmallSimpleLeaf SmallM11 :=
  smallSimpleLeaf_m11 concreteLeaf_m11

end Leaf

end CFSG.ClassicalInvolution.Q3.TA3
