module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogStandard
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogLift

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear upperUnit)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore ordSL)
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)
open scoped MatrixGroups

section SwapHom

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]

@[expose] noncomputable def neighbourSwapHom (e : L ≃* StatedSp 3 K) {k : Fin 3}
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k) :
    SL(2, F) × SL(2, F) →* G :=
  (neighbourCore e k).subtype.comp (Φ.toMonoidHom.comp swapPairSL)

theorem neighbourSwapHom_apply (e : L ≃* StatedSp 3 K) {k : Fin 3}
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k)
    (p : SL(2, F) × SL(2, F)) :
    neighbourSwapHom e Φ p = ((Φ (swapPairSL p) : neighbourCore e k) : G) :=
  rfl

theorem neighbourSwapHom_injective (e : L ≃* StatedSp 3 K) {k : Fin 3}
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k) :
    Function.Injective (neighbourSwapHom e Φ) :=
  (neighbourCore e k).subtype_injective.comp (Φ.injective.comp swapPairSL_injective)

theorem conj_neighbourSwapHom [CharP F 2] (e : L ≃* StatedSp 3 K) {k : Fin 3}
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k) {t : G}
    (hN3 : ∀ y : Matrix.SpecialLinearGroup (Fin (2 * 2)) F,
      t * (Φ y : G) * t⁻¹ = (Φ ((slFourEquivProj F).symm
        ((conjAut (2 * 2) F (spBlockSwapGL 2 F) * dualAut (2 * 2) F) (proj (2 * 2) F y))) : G))
    (p : SL(2, F) × SL(2, F)) :
    t * neighbourSwapHom e Φ p * t⁻¹ = neighbourSwapHom e Φ p.swap := by
  rw [neighbourSwapHom_apply, hN3, slFourEquivProj_symm_graph_swapPairSL]
  rfl

theorem range_neighbourSwapHom [Finite F] (e : L ≃* StatedSp 3 K) {k : Fin 3}
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k) :
    (neighbourSwapHom e Φ).range =
      ((blockSpecialLinear (K := F) (twBlockSL 0) ⊔
        blockSpecialLinear (K := F) (twBlockSL 0)ᶜ).map Φ.toMonoidHom).map
          (neighbourCore e k).subtype := by
  rw [neighbourSwapHom, MonoidHom.range_comp, MonoidHom.range_comp, range_swapPairSL]

theorem range_neighbourSwapHom_two [Finite G] [CharP K 2] [Finite F] [CharP F 2]
    (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) (σ : K ≃+* F)
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 2)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 x)) : neighbourCore e 2) : G) =
        ((e.symm (complSpEquiv 2 x : complSp K 2) : L) : G)) :
    (neighbourSwapHom e Φ).range = pieceCore e ({0} : Finset (Fin 3)) := by
  rw [range_neighbourSwapHom, pieceCore_zero_eq_of_standard hK e σ Φ hN1]

end SwapHom

section Kinds

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F]

theorem false_of_siegel_normal_of_swapHom [CharP F 2] (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {ψ : SL(2, F) × SL(2, F) →* G}
    (hψ : Function.Injective ψ) (hψt : ∀ p, t * ψ p * t⁻¹ = ψ p.swap)
    (hψM : ψ.range ≤ pieceCore e ({0} : Finset (Fin 3)))
    (htX : t ∈ centralizer (modelToG e (siegelTorus K 3) : Set G))
    (hnorm : (((modelToG e (siegelLevi K 3)).subgroupOf
      (centralizer (modelToG e (siegelTorus K 3) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K 3) : Set G))))).Normal) : False := by
  have hcen := mk_mem_center_of_siegel_normal hset hKc hf (by norm_num) e htC ht htX hnorm
  set x : SL(2, F) := upperUnit 1 with hxdef
  have hx2 : x * x = 1 := by
    rw [hxdef, ← LinearPilot.upperUnit_add, CharTwo.add_self_eq_zero, LinearPilot.upperUnit_zero]
  have hx1 : x ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [hxdef, LinearPilot.coe_upperUnit] at h1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
  have hw : ψ (x, x) = t * ψ (x, 1) * t⁻¹ * (ψ (x, 1))⁻¹ := by
    rw [hψt, Prod.swap_prod_mk, ← map_inv, ← map_mul, Prod.inv_mk, inv_one, Prod.mk_mul_mk,
      one_mul, mul_one, hxinv]
  have hyM : ψ (x, 1) ∈ pieceCore e ({0} : Finset (Fin 3)) := hψM ⟨_, rfl⟩
  refine false_of_mk_mem_center_of_orderOf_commutator htX
    (pieceCore_singleton_le_centralizer_siegelTorus e (j := 0) (by decide) hyM) ?_ hcen
  rw [← hw, orderOf_injective ψ hψ (x, x), Prod.orderOf_mk, hord, Nat.lcm_self]

theorem false_of_siegelFieldParam_of_swapHom [Finite K] [CharP K 2] [Finite F]
    (hK : 4 ≤ Nat.card K) (hFK : Nat.card F = Nat.card K) {F' : Type} [Field F'] [Finite F']
    (hF' : Nat.card F' = Nat.card K ^ 2) {e : L ≃* StatedSp 3 K} {t : G} {ι : K →+* F'}
    {σ' : F' ≃+* F'} (S : SiegelFieldParam e t ι σ') {ψ : SL(2, F) × SL(2, F) →* G}
    (hψ : Function.Injective ψ) (hψM : ψ.range = pieceCore e ({0} : Finset (Fin 3))) : False := by
  have hSL : Nat.card SL(2, F) = ordSL 2 (Nat.card F) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)
  have h1 : Nat.card (pieceCore e ({0} : Finset (Fin 3))) = ordSL 2 (Nat.card K) ^ 2 := by
    rw [← hψM, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, Nat.card_prod, hSL, hFK, sq]
  have h2 := S.natCard_pieceCore_singleton hK (by norm_num) (j := 0) (by decide)
  have hlt := ordSL_two_sq_lt_ordSL_two_sq (q := Nat.card K) (by omega)
  rw [h1, hF'] at h2
  omega

end Kinds

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nonempty_siegelSwapParam_of_swapHom (hcat : LinearPilot.SLmCatalogueClausesAt 3)
    (hdet : LinearPilot.SLmEvenTypeDetAt 3) (hsplit : OddCentralSplit (siegelLevi K 3))
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hFK : Nat.card F = Nat.card K)
    {ψ : SL(2, F) × SL(2, F) →* G} (hψ : Function.Injective ψ)
    (hψt : ∀ p, t * ψ p * t⁻¹ = ψ p.swap) (hψM : ψ.range = pieceCore e ({0} : Finset (Fin 3))) :
    Nonempty (SiegelSwapParam e t) := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F', _, _, ι, σ', hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  have hF' : Nat.card F' = Nat.card K ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix, hKc, ← pow_mul,
      mul_comm]
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf le_rfl e htC ht hsplit ι
    hσ1 hσσ hfix with ⟨htX, hnorm⟩ | hS' | hS
  · exact (false_of_siegel_normal_of_swapHom hset hKc hf e htC ht hψ hψt hψM.le htX hnorm).elim
  · obtain ⟨S⟩ := hS'
    exact (false_of_siegelFieldParam_of_swapHom hq hFK hF' S hψ hψM).elim
  · exact hS

theorem nonempty_siegelSwapParam_of_standard
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hsplit : OddCentralSplit (siegelLevi K 3)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hk : RootKindSp e t f 2 .linearEven) (hstd : SpThreeStandard e) :
    Nonempty (SiegelSwapParam e t) := by
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F, _, _, _, σ, Φ, hF, hN1, hN3⟩ := exists_mulEquiv_of_spThreeLinearNormalized hKc hf
    (spThreeLinearNormalized_of_standard hset hKc hf e htC ht 2 hk hstd)
  have hFK : Nat.card F = Nat.card K := by rw [hF, hKc]
  exact nonempty_siegelSwapParam_of_swapHom hcat hdet hsplit hset hKc hf e htC ht hFK
    (neighbourSwapHom_injective e Φ) (conj_neighbourSwapHom e Φ hN3)
    (range_neighbourSwapHom_two hK e σ Φ hN1)

end Swap

end CFSG.SeitzReduction.SymplecticPilot
