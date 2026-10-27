module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporWit
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporW

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem fiveSpor_J3 :
    FiveSporClauseFor .J3 := by
  intro S _ _ _ hna ⟨e⟩ σ P h hex ⟨eP⟩
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ1 := h.ne_one
  have eP' : Nonempty (↥P ⧸ pPrimeCore 2 ↥P ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hex.symm).trans eP⟩
  let θ : S ≃* j3P := e.trans j3PermEquiv
  obtain ⟨eR, heR, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, ⟨E⟩⟩ := exists_fixed_equiv eR heR hcover θ hσσ hσ1
  have hcardC : Nat.card (fixedSubgroup σ) = r.centOrder := by
    rw [Nat.card_congr E.toEquiv]
    exact (hrows r hr).2.2.2.2.1
  simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr
  ·
    obtain ⟨x, hx, hx5, y, hy, hxy⟩ := j3_fiveWit
    have hrep : r.rep = j3CentTbl 9 := by rw [hr]
    rw [hrep] at E
    have hC : Nat.card (fixedSubgroup σ) = 60 * 2 ^ 5 := by
      rw [hcardC, hr] <;> decide
    exact false_of_five_witness_of_equiv h.2.1 h.2.2.1 eP' hC E hx hy hx5 hxy
  ·
    subst hr
    exact false_of_not_dvd_fixed_card h eP (by rw [hcardC]; decide)

end CFSG.ComponentClassification.SolMax.FiveCat.Spor
