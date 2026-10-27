module

public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4NonToral

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem model_sup_centralizer_eq_top {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    {n e : ℕ} (hadm : StatedLieAdmissible t n p e) (ht : t = .G2 ∨ t = .trialityD4)
    (h5 : t = .G2 → 5 ≤ p ^ e) {r r' : (modelUniv t n p e Fact.out).K} (hr : r * r = 1)
    (hr' : r' * r' = 1) (hr1 : r ≠ 1) (hr1' : r' ≠ 1) (hne : r ≠ r') (hc : r * r' = r' * r) :
    Subgroup.centralizer ({r} : Set (modelUniv t n p e Fact.out).K) ⊔
      Subgroup.centralizer ({r'} : Set (modelUniv t n p e Fact.out).K) = ⊤ := by
  rcases ht with rfl | rfl
  · obtain ⟨hk, -⟩ := hadm.2.2
    subst hk
    exact G2D4Models.g2CentralizersGenerate_of_nonToral G2D4Models.g2NonToralGenerate_all hp2
      (h5 rfl) hadm r r' hr hr' hr1 hr1' hne hc
  · have hk : n = 0 := hadm.2.2
    subst hk
    exact G2D4Models.sup_centralizer_eq_top_model_td4 hp2 hadm hr hr' hr1 hr1' hne hc

end CFSG.ClassicalInvolution.NDB.G2S
