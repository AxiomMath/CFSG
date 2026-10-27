module

public import CFSG.ClassicalInvolution.Q3.Q3E6TRow
public import CFSG.ClassicalInvolution.Q3.Q3E6TRowOrth
public import CFSG.ClassicalInvolution.Q3.Q3E8BRowExc
public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.Uniform.U8Final
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpLayerCount
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.NonClassical (TE6Layer te6Core te6Card_of_layer
  card_te6Layer_eq te6Shape_of_layer)
open CFSG.ClassicalInvolution.Q3.Q3W (modelFacts_isFundTag noTE6Config3_of_hasLayer3)
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem te6Row3 : TE6Row3 := by
  intro t n hft hG2 hD4 hadm R₀ hR₀ k hkR hkc φ hφ h0
  have hk : R₀ ≤ Subgroup.centralizer ({k} : Set _) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hkc r hr).symm
  have h0' : φ ⟨R₀, hR₀, hk⟩ = none := h0 _ rfl
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund' : ModelFacts.IsFundTag t := modelFacts_isFundTag hft
  have hfin : Finite (modelUniv t n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv hp2 Nat.prime_three hfund' hadm
  have hcount : Nat.card {S : Subgroup (modelUniv t n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D ∧ Commutes S R₀} =
        te6Core 3 + 1 := by
    have h1 := te6Card_of_layer hR₀ hkR hk φ hφ h0'
    have h2 := card_te6Layer_eq (p := 3) (f := 1) hp2 le_rfl (by norm_num)
    rw [pow_one] at h2
    omega
  have hnc : NonClassical.NoTE6Config
      (fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D) → False := fun hN => by
    obtain ⟨R₁, hP, hT⟩ := te6Shape_of_layer hp2 le_rfl hR₀ hkR hk φ hφ h0'
    exact hN R₀ hR₀ R₁ hP hT
  cases t with
  | PSL => exact (hnc (NonClassical.noTE6Config_psl_model hp2 hadm)).elim
  | PSU => exact (hnc (NonClassical.noTE6Config_psu_model hp2 hadm)).elim
  | PSp => exact (hnc (NonClassical.noTE6Config_psp_model hp2 hadm)).elim
  | POmegaOdd => exact (te6_false_odd3 hadm hR₀ hcount).elim
  | POmegaPlus => exact (te6_false_plus3 hadm hR₀ hcount).elim
  | POmegaMinus => exact ⟨rfl, te6_eq_minus3 hadm hR₀ hcount⟩
  | G2 => exact absurd rfl hG2
  | F4 =>
    exact (hnc (noTE6Config3_of_hasLayer3 hft hadm hG2 hD4
      (Uniform.excLayer3 .F4 n (Or.inl rfl) hadm))).elim
  | E6 =>
    exact (hnc (noTE6Config3_of_hasLayer3 hft hadm hG2 hD4
      (Uniform.excLayer3 .E6 n (Or.inr (Or.inl rfl)) hadm))).elim
  | E7 =>
    exact (hnc (noTE6Config3_of_hasLayer3 hft hadm hG2 hD4
      (Uniform.excLayer3 .E7 n (Or.inr (Or.inr (Or.inl rfl))) hadm))).elim
  | E8 =>
    exact (hnc (noTE6Config3_of_hasLayer3 hft hadm hG2 hD4
      (Uniform.excLayer3 .E8 n (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm))).elim
  | twistedE6 =>
    exact (hnc (noTE6Config3_of_hasLayer3 hft hadm hG2 hD4
      (Uniform.excLayer3 .twistedE6 n (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm))).elim
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 => exact hft.elim
  | twistedG2 => exact hft.elim
  | twistedF4 => exact hft.elim
  | Tits => exact hft.elim

end CFSG.ClassicalInvolution.Q3.Q3E6T
