module

public import CFSG.LocalAnalysis.GL83PartI.I713.Chain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic

public section

namespace GL83.I713

open CFSG.Open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {p : ℕ}

theorem relIndex_coordinateG_D_dvd_two (K : Type) [Field K] [Finite K] :
    (coordinateG K).relIndex (coordinateD K) ∣ 2 := by
  have h := CFSG.LocalAnalysis.ComponentInitial.card_pgl_quotient_psl_dvd K
  rw [Nat.card_congr (pglQuotientEquivCoordinateDG K).toEquiv] at h
  rw [Subgroup.relIndex, Subgroup.index]
  exact h.trans (Nat.gcd_dvd_left 2 _)

theorem pRank_outer_coordinateG_le_one {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hp2 : p ≠ 2) : pRank p (⊤ : Subgroup (Outer (coordinateG K))) ≤ 1 := by
  set φ := coordinateConjugation K
  have hsurj : Function.Surjective φ := coordinateConjugation_surjective K
  have hinj : Function.Injective φ := coordinateConjugation_injective K
  set DE := (coordinateD K).subgroupOf (coordinateE K) with hDE
  set GE := (coordinateG K).subgroupOf (coordinateE K) with hGE
  have : (DE.map φ).Normal := (coordinateD_normal_in_E K).map φ hsurj
  have hGD : GE ≤ DE := fun x hx => coordinateG_le_D K hx
  have hID : CFSG.ComponentClassification.OuterAutomorphisms.inner (coordinateG K) ≤ DE.map φ := by
    rw [← coordinateConjugation_G_image K]
    exact Subgroup.map_mono hGD
  obtain ⟨⟨c, hc⟩⟩ := coordinateED_isCyclic K
  obtain ⟨e₀, rfl⟩ := QuotientGroup.mk_surjective c
  have hcyc : ∃ g ∈ (⊤ : Subgroup (MulAut (coordinateG K))), ∀ x ∈ (⊤ : Subgroup _),
      ∃ k : ℤ, g ^ k * x ∈ DE.map φ := by
    refine ⟨φ e₀, Subgroup.mem_top _, fun x _ => ?_⟩
    obtain ⟨e, rfl⟩ := hsurj x
    obtain ⟨k, hk⟩ := hc (QuotientGroup.mk e)
    refine ⟨-k, e₀ ^ (-k) * e, ?_, by simp only [map_mul, map_zpow]⟩
    beta_reduce at hk
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
    simpa [zpow_neg] using hk
  have hDI : Nat.Coprime
      ((CFSG.ComponentClassification.OuterAutomorphisms.inner (coordinateG K)).relIndex (DE.map φ))
      p := by
    rw [← coordinateConjugation_G_image K, Subgroup.relIndex_map_map_of_injective _ _ hinj,
      Subgroup.relIndex_subgroupOf (coordinateD_le_E K)]
    refine Nat.Coprime.coprime_dvd_left (relIndex_coordinateG_D_dvd_two K) ?_
    exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  exact pRank_outer_le_one_of_chain hp hID le_top hcyc hDI
    (by rw [Subgroup.index_top]; exact Nat.coprime_one_left p)

theorem outClauseFor_projectiveSL_two (K : Type) [Field K] [Finite K] :
    OutClauseFor (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 K) := by
  let eT : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 K ≃* coordinateG K :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 K)).trans
      (pslEquivCoordinateG K)
  refine OutClauseFor.of_mulEquiv eT fun p hp hp2 _ => ?_
  exact pRank_outer_coordinateG_le_one hp hp2

end GL83.I713
