module

public import CFSG.CGT.PushingUpLit.BHS.FourTwoB
public import CFSG.CGT.PushingUpLit.BHS.FourTwoC

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem four_nine (h : Hyp42 P D T M) {H : Subgroup (MulAut V)} (hHP : H ≤ P)
    (hT : dInter D T ⊆ dInter D H) (hM : ¬ dInter D H ⊆ dInter D M) :
    ∃ T₀ : Subgroup (MulAut V), dInter D T₀ = dInter D T ∧
      Hyp42 H (dInter D H) T₀ (M ⊓ H) := by
  have hE₂ : IsPGroup 2 (⨆ A ∈ dInter D T, A : Subgroup (MulAut V)) :=
    h.syl.2.1.to_le (iSup₂_le fun A hA => hA.2)
  have hEH : (⨆ A ∈ dInter D T, A : Subgroup (MulAut V)) ≤ H :=
    iSup₂_le fun A hA => (hT hA).2
  obtain ⟨T₀, hT₀, hET₀⟩ := Glauberman.exists_isSylowOf_ge hE₂ hEH
  have hE : ∀ A ∈ dInter D T, A ≤ T₀ := fun A hA =>
    (le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ dInter D T) => B) A hA
      le_rfl).trans hET₀
  have hd := h.dInter_eq_of_le (hT₀.1.trans hHP) hT₀.2.1 hE
  exact ⟨T₀, hd, h.restrict_dInter hHP hT₀ hd hM⟩

theorem four_ten (h : Hyp42 P D T M) {D₀ : Set (Subgroup (MulAut V))} (hD₀ : D₀ ⊆ D)
    (hnorm : ∀ A ∈ D₀, ∀ g ∈ P, conjSub g A ∈ D₀) (hcore : ¬ D₀ ⊆ dCore P D M) :
    ∃ T₀ : Subgroup (MulAut V),
      Hyp42 (⨆ A ∈ D₀, A) D₀ T₀ (M ⊓ ⨆ A ∈ D₀, A) :=
  ⟨_, h.restrict_normalSet hD₀ hnorm hcore⟩

end CFSG.CGT.PushingUpLit.BHS
