module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddCl
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClDisp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpBase

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent)
open CFSG.ComponentClassification.CatFC

section SpCentral

variable {r : ℕ} {K : Type} [Field K]

theorem spScalars_le_center' : spScalars r K ≤ center (StatedSp r K) := by
  have h := ker_proj_le_center (r := r) (K := K)
  rwa [ker_proj] at h

variable [Finite K]

theorem card_fixed_conjAut_dvd_spCent (A : gsp r K) :
    Nat.card (fixedSubgroup (conjAut r K A)) ∣ Nat.card (spCent r K A) := by
  have hinv := map_eq_of_forall_mem (conjSp r K) (spScalars r K)
    (fun A _ hz => conjSp_mem_spScalars A hz) A
  exact card_fixed_onQuotient_dvd (spScalars r K) spScalars_le_center' (conjSp r K A) hinv

end SpCentral

section Constraints

variable {r : ℕ} {K : Type} [Field K] [Finite K] {A : gsp r K}
  {J : Subgroup ↥(fixedSubgroup (conjAut r K A))}

theorem U42Hyp.spCent_constraints (hr : 1 ≤ r) (h : U42Hyp (conjAut r K A) J) :
    25920 ∣ Nat.card (spCent r K A) ∧ Nat.card (spCent r K A) ∣ 103680 := by
  refine ⟨h.dvd_card.trans (card_fixed_conjAut_dvd_spCent A), ?_⟩
  have h1 := h.card_dvd_mul (spCentFix A)
  have h2 := card_ker_spCentFix_le hr A
  have h3 : 0 < Nat.card ↥(spCentFix A).ker := Nat.card_pos
  have h4 : Nat.card ↥(spCentFix A).ker = 1 ∨ Nat.card ↥(spCentFix A).ker = 2 := by omega
  rcases h4 with h4 | h4 <;> rw [h4] at h1
  · exact h1.trans (by norm_num)
  · exact h1

end Constraints

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
