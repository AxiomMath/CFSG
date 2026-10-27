module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTParamMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

theorem eq_one_of_irreducible_of_card_two {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  have hc : c ≠ 0 := fun h0 => hirr 0 (by rw [h0]; ring)
  have hc1 : c = 1 := (eq_zero_or_eq_one_of_natCard_two hK c).resolve_left hc
  refine ⟨(eq_zero_or_eq_one_of_natCard_two hK b).resolve_left fun h0 => hirr 1 ?_, hc1⟩
  rw [h0, hc1, one_pow, zero_mul, add_zero, CharTwo.add_self_eq_zero]

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def IsNsOmPlusParam {r : ℕ} (hK : Nat.card K = 2) (hr : 2 ≤ r) (hr3 : 3 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G) (k : Fin (r + 1))
    (Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))) : Prop :=
  (∀ g, t * ((Φ g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) * t⁻¹ =
    ((Φ (kOmegaBetaC K r g) : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G)) ∧
  ∀ x : StatedSp r K,
    ((Φ (q2OmIota hr hK hr3 x) : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
      ((e.symm (complSpEquiv k x) : L) : G)

@[expose] def IsNsOmMinusParam {r : ℕ} (hK : Nat.card K = 2) (hr3 : 3 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G) (k : Fin (r + 1))
    (Φ : StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))) : Prop :=
  (∀ g, t * ((Φ g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) * t⁻¹ =
    ((Φ (kOmMBetaC K r 1 1 g) : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G)) ∧
  ∀ x : StatedSp r K,
    ((Φ (q2OmMIota hr3 (q2Omega_irreducible_one_one hK) hK x) :
      centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
        ((e.symm (complSpEquiv k x) : L) : G)

variable [Finite G]

theorem exists_isNsOmPlusParam (hset : SeitzSetting G L) {r : ℕ} (hK : Nat.card K = 2)
    (hr : 2 ≤ r) (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (r + 1))
    (h : NsKindSp e t k .omegaPlus) : ∃ Φ, IsNsOmPlusParam hK hr hr3 e t k Φ :=
  exists_q2OmParam hset hK hr hr3 e htC ht k h

theorem exists_isNsOmMinusParam (hset : SeitzSetting G L) {r : ℕ} (hK : Nat.card K = 2)
    (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (r + 1))
    (h : NsKindSp e t k .omegaMinus) : ∃ Φ, IsNsOmMinusParam hK hr3 e t k Φ := by
  obtain ⟨b, c, hirr, Φ, h3, h1⟩ := exists_q2OmMParam hset hK hr3 e htC ht k h
  obtain ⟨rfl, rfl⟩ := eq_one_of_irreducible_of_card_two hK hirr
  exact ⟨Φ, h3, h1⟩

end Param

@[expose] def SpTwoOmegaPlusParamCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hr : 4 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (r + 1), NsKindSp e t k .omegaPlus) →
      ∀ Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmPlusParam hK (by omega) (by omega) e t k (Φ k)) →
        NsOmegaCTData e .omegaPlus

@[expose] def SpTwoOmegaMinusParamCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hr : 4 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (r + 1), NsKindSp e t k .omegaMinus) →
      ∀ Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmMinusParam hK (by omega) e t k (Φ k)) →
        NsOmegaCTData e .omegaMinus

section Reduction

theorem spTwoOmegaCTDataInput_omegaPlus_of_paramCT (h : SpTwoOmegaPlusParamCTInput) :
    SpTwoOmegaCTDataInput .omegaPlus := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  choose Φ hΦ using fun k => exists_isNsOmPlusParam hset hK (by omega) (by omega) e htC ht k
    (hroot k)
  exact h G L hset n K hK hn e t ht hKt hroot Φ hΦ

theorem spTwoOmegaCTDataInput_omegaMinus_of_paramCT (h : SpTwoOmegaMinusParamCTInput) :
    SpTwoOmegaCTDataInput .omegaMinus := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  choose Φ hΦ using fun k => exists_isNsOmMinusParam hset hK (by omega) e htC ht k (hroot k)
  exact h G L hset n K hK hn e t ht hKt hroot Φ hΦ

theorem spTwoOmegaKindInput_omegaPlus_of_paramCT (h : SpTwoOmegaPlusParamCTInput) :
    SpTwoOmegaKindInput .omegaPlus :=
  spTwoOmegaKindInput_of_ctData (spTwoOmegaCTDataInput_omegaPlus_of_paramCT h)

theorem spTwoOmegaKindInput_omegaMinus_of_paramCT (h : SpTwoOmegaMinusParamCTInput) :
    SpTwoOmegaKindInput .omegaMinus :=
  spTwoOmegaKindInput_of_ctData (spTwoOmegaCTDataInput_omegaMinus_of_paramCT h)

end Reduction

end CFSG.SeitzReduction.SymplecticPilot
