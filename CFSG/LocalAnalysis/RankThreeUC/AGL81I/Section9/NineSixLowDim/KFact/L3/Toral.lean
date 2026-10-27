module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Conj
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Diag
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Levi

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

theorem closure_fixSetThree_of_commute {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) {A : Subgroup (GL (Fin 3) (ZMod q))} (hA : IsElemModScalars p A)
    (hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) :
    Subgroup.closure (fixSetThree p A) = CFSG.Open.StatedSL 3 (ZMod q) := by
  obtain ⟨ζ, P, hζ, h₁, h₂⟩ := exists_conj_diag_of_commute hp hp2 hpq hA hc
  exact closure_fixSetThree_eq_of_le_conj P le_rfl (closure_fixSetThree_of_diag hp hpq hζ h₁ h₂)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
