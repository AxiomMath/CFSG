module

public import CFSG.CGT.PushingUpLit.BHS.FourOneC

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))}

theorem four_six (h : Hyp41 P D) {A B : Subgroup (MulAut V)} (hA : A ∈ D) (hB : B ∈ D)
    (hne : A ≠ B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    fixV A ⊔ fixV B = ⊤ ∧ IsQuadratic (A ⊔ B) :=
  ⟨h.sup_fixV_eq_top hA hB hne hcomm, h.isQuadratic_sup hA hB hne hcomm⟩

theorem four_seven (h : Hyp41 P D) {T : Subgroup (MulAut V)} (hT : IsSylowOf 2 T P) :
    IsElemAbelian2 (⨆ A ∈ dInter D T, A) ∧ IsQuadratic (⨆ A ∈ dInter D T, A) :=
  ⟨h.four_seven_isElemAbelian2 hT, h.four_seven_isQuadratic hT⟩

end CFSG.CGT.PushingUpLit.BHS
