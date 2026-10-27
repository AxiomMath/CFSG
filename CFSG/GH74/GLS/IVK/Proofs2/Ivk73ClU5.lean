module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClBridge
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint Subgroup

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem ivk73_u5 (p f : ℕ)
    (hp : p.Prime) (hf : 1 ≤ f) (hmod : p ^ f % 4 = 1) :
    Ivk73Empty (fun X _ => LieModel X .PSU 5 p f) := by
  intro N _ _ L K Q h hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
    have := Nat.even_iff.1 h2
    omega
  obtain ⟨u, hu2, huC⟩ := h.exists_involution
  have hcomp := h.isComponentOf_centralizer hu2 huC
  have := h.normal
  exact ComponentClassification.OddClassSelector.su_family_false (W := L) h.simple h.exists_noncomm
    h.centralizer_eq_bot hu2 h.K_le hcomp h.smallSource hp hp2 hf (le_refl 5) hm

end CFSG.GH74.GLS.IVK
