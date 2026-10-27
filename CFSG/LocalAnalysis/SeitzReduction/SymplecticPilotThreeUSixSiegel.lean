module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSixStd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeShortRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeNodePairs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.SeitzReduction.LinearPilot (upperUnit upperUnit_add upperUnit_inv map_upperUnit
  upperUnit_zero coe_upperUnit)
open CFSG.SeitzReduction.F4Pilot (statedSpMap ordSL)
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)
open scoped MatrixGroups

section FieldData

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K')

theorem barRingEquiv_eq_self_iff {K : Type} [Field K] (ι₀ : K ≃+* h.fixedField) (x : K') :
    UnitaryPilot.barRingEquiv h x = x ↔
      x ∈ Set.range (h.fixedField.subtype.comp (ι₀ : K →+* h.fixedField)) := by
  constructor
  · intro hx
    have hx' : x ∈ h.fixedField := by
      rw [UnitaryFieldData.mem_fixedField, ← UnitaryPilot.barRingEquiv_apply]
      exact hx
    exact ⟨ι₀.symm ⟨x, hx'⟩, by simp⟩
  · rintro ⟨c, rfl⟩
    rw [UnitaryPilot.barRingEquiv_apply]
    exact (ι₀ c).2

end FieldData

section Trivial

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem orderOf_upperUnit_of_ne_zero {F : Type} [Field F] [CharP F 2] {c : F} (hc : c ≠ 0) :
    orderOf (upperUnit c) = 2 := by
  have hx2 : upperUnit c * upperUnit c = 1 := by
    rw [← upperUnit_add, CharTwo.add_self_eq_zero, upperUnit_zero]
  have hx1 : upperUnit c ≠ 1 := by
    intro h1
    have h2 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp [coe_upperUnit] at h2
    exact hc h2
  exact orderOf_eq_prime (by rw [sq, hx2]) hx1

theorem false_of_siegel_normal_of_fieldHom (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {F : Type} [Field F] [CharP F 2]
    {σ : F ≃+* F} (hσ : σ ≠ 1) {ψ : SL(2, F) →* G} (hψ : Function.Injective ψ)
    (hψt : ∀ A, t * ψ A * t⁻¹ = ψ (SpecialLinearGroup.map σ.toRingHom A)) {j : Fin 3}
    (hj : j.val + 1 < 3) (hψM : ψ.range ≤ pieceCore e ({j} : Finset (Fin 3)))
    (htX : t ∈ centralizer (modelToG e (siegelTorus K 3) : Set G))
    (hnorm : (((modelToG e (siegelLevi K 3)).subgroupOf
      (centralizer (modelToG e (siegelTorus K 3) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K 3) : Set G))))).Normal) : False := by
  have hcen := mk_mem_center_of_siegel_normal hset hKc hf (by norm_num) e htC ht htX hnorm
  obtain ⟨ω, hω⟩ : ∃ ω : F, σ ω ≠ ω := by
    by_contra hall
    push Not at hall
    exact hσ (RingEquiv.ext hall)
  have hc : σ ω - ω ≠ 0 := sub_ne_zero.2 hω
  have hw : t * ψ (upperUnit ω) * t⁻¹ * (ψ (upperUnit ω))⁻¹ = ψ (upperUnit (σ ω - ω)) := by
    rw [hψt, map_upperUnit, ← map_inv, ← map_mul, upperUnit_inv, ← upperUnit_add, sub_eq_add_neg]
    rfl
  have hyM : ψ (upperUnit ω) ∈ pieceCore e ({j} : Finset (Fin 3)) := hψM ⟨_, rfl⟩
  refine false_of_mk_mem_center_of_orderOf_commutator htX
    (pieceCore_singleton_le_centralizer_siegelTorus e hj hyM) ?_ hcen
  rw [hw, orderOf_injective ψ hψ, orderOf_upperUnit_of_ne_zero hc]

end Trivial

section Field

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

theorem nonempty_siegelFieldParam_of_std (hcat : LinearPilot.SLmCatalogueClausesAt 3)
    (hdet : LinearPilot.SLmEvenTypeDetAt 3) (hsplit : OddCentralSplit (siegelLevi K 3))
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] (h : UnitaryFieldData 2 f K')
    [CharP h.fixedField 2] {C₀ : GL (Fin (2 * 2)) K'} (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
    (ι₀ : K ≃+* h.fixedField) (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G)
    (hrange : Φ.range = neighbourCore e 0)
    (hker : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))
    (hN1 : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι₀ : K →+* h.fixedField) 2 x)) =
        ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G))
    (hN3 : ∀ x, t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x)) :
    Nonempty (SiegelFieldParam e t (h.fixedField.subtype.comp (ι₀ : K →+* h.fixedField))
      (UnitaryPilot.barRingEquiv h)) := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  set ψ : SL(2, K') →* G := Φ.comp (lambdaU h hC₀) with hψdef
  have hψinj : Function.Injective ψ :=
    injective_comp_of_ker_le_center (lambdaU_injective h hC₀) center_SL_two_eq_bot_of_charTwo
      hker
  have hψM : ψ.range = pieceCore e ({1} : Finset (Fin 3)) := by
    rw [pieceCore_one_eq_map_lambdaU_of_std hKc hf e h hC₀ ι₀ Φ hrange hker hN1, hψdef,
      MonoidHom.range_comp]
  have hψt : ∀ A, t * ψ A * t⁻¹ =
      ψ (SpecialLinearGroup.map (UnitaryPilot.barRingEquiv h).toRingHom A) := fun A => by
    change t * Φ (lambdaU h hC₀ A) * t⁻¹ = Φ (lambdaU h hC₀ _)
    rw [hN3, primeFormFieldSU_lambdaU h hC₀ hC]
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf le_rfl e htC ht hsplit
    (h.fixedField.subtype.comp (ι₀ : K →+* h.fixedField)) (barRingEquiv_ne_one (h := h))
    (UnitaryPilot.barRingEquiv_mul_self h) (barRingEquiv_eq_self_iff h ι₀) with
    ⟨htX, hnorm⟩ | hS | hS'
  · exact (false_of_siegel_normal_of_fieldHom hset hKc hf e htC ht (barRingEquiv_ne_one (h := h))
      hψinj hψt (j := 1) (by decide) hψM.le htX hnorm).elim
  · exact hS
  · exfalso
    obtain ⟨S⟩ := hS'
    have h1 := S.natCard_pieceCore_singleton hK4 le_rfl (j := 1) (by decide)
    have hSL : Nat.card SL(2, K') = ordSL 2 (Nat.card K') :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)
    have h2 : Nat.card (pieceCore e ({1} : Finset (Fin 3))) = ordSL 2 (Nat.card K') := by
      rw [← hψM, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, hSL]
    have hK' : Nat.card K' = Nat.card K ^ 2 := by rw [h.card_eq_sq, hKc]
    have hlt := ordSL_two_sq_lt_ordSL_two_sq (q := Nat.card K) (by omega)
    rw [← hK', ← h2, h1] at hlt
    exact lt_irrefl _ hlt

end Field

section Pairs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {e : L ≃* StatedSp 3 K} {t : G} {ι : K →+* F} {σ : F ≃+* F}

theorem SiegelFieldParam.exists_linearPair_three (S : SiegelFieldParam e t ι σ)
    (hK : 4 ≤ Nat.card K) :
    ∃ W, LinearBlockStandardPair F W (pieceCore e ({0} : Finset (Fin 3)))
      (pieceCore e ({1} : Finset (Fin 3))) := by
  set θ : SL(3, F) →* G := S.Φ.comp (siegelLeviEquiv (K := F) (n := 3)).toMonoidHom with hθ
  have hker : θ.ker ≤ center SL(3, F) := by
    intro x hx
    have hz := S.ker_le (show siegelLeviEquiv x ∈ S.Φ.ker from hx)
    refine mem_center_iff.2 fun g => (siegelLeviEquiv (K := F) (n := 3)).injective ?_
    rw [map_mul, map_mul]
    exact mem_center_iff.1 hz (siegelLeviEquiv g)
  have hB : ∀ (H : Subgroup SL(3, F)) (J : Subgroup (StatedSp 3 F)),
      H.map (siegelLeviEquiv (K := F) (n := 3)).toMonoidHom = J.subgroupOf (siegelLevi F 3) →
        H.map θ = (J.subgroupOf (siegelLevi F 3)).map S.Φ := by
    intro H J hHJ
    rw [← hHJ, Subgroup.map_map]
  have h0 : pieceCore e ({0} : Finset (Fin 3)) =
      ((simpleRootSL2 F (0 : Fin 3)).subgroupOf (siegelLevi F 3)).map S.Φ := by
    rw [S.pieceCore_singleton_eq_map hK (j := 0) (by decide),
      siegelBlock_pair_eq_simpleRootSL2' (j := (0 : Fin 3)) (by decide)]
  have h1 : pieceCore e ({1} : Finset (Fin 3)) =
      ((simpleRootSL2 F (1 : Fin 3)).subgroupOf (siegelLevi F 3)).map S.Φ := by
    rw [S.pieceCore_singleton_eq_map hK (j := 1) (by decide),
      siegelBlock_pair_eq_simpleRootSL2' (j := (1 : Fin 3)) (by decide)]
  refine ⟨θ.range, linearBlockStandardPair_range_of_map hker ?_ ?_⟩
  · rw [h0]
    exact hB _ _ (map_range_blockSL_siegelLeviEquiv (j := 0) (by decide) (by omega) (by decide))
  · rw [h1]
    exact hB _ _ (map_range_blockSL_siegelLeviEquiv (j := 1) (by decide) (by omega) (by decide))

variable [CharP K 2] [Finite K]

theorem commute_pieceCore_zero_two_of_siegelFieldParam (hset : SeitzSetting G L)
    (hK : 4 ≤ Nat.card K) (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (S : SiegelFieldParam e t ι σ)
    (h2 : pieceCore e ({2} : Finset (Fin 3)) = modelToG e (simpleRootSL2 K 2)) :
    ∀ x ∈ pieceCore e ({0} : Finset (Fin 3)), ∀ y ∈ pieceCore e ({2} : Finset (Fin 3)),
      x * y = y * x := by
  have hO := range_le_centralizer_longRootSp2_two_of_field hset hK e htC ht ι hσ1 hσσ hfix
    (ψ := S.rootHom (j := (0 : Fin 3)) (by decide)) (S.range_rootHom (by decide) hK).le
    (S.rootHom_map (by decide)) (S.conj_rootHom (by decide))
  rw [S.range_rootHom (by decide) hK] at hO
  intro x hx y hy
  rw [h2, simpleRootSL2_of_not_lt (by decide)] at hy
  exact (mem_centralizer_iff.1 (hO hx) y hy).symm

end Pairs

end CFSG.SeitzReduction.SymplecticPilot
