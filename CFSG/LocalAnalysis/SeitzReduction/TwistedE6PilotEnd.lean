module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotKinds
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.UnitaryPilot (SUmNotOddLieInputAt)
open CFSG.SeitzReduction.OmegaPilot (OmegaNotOddLieInputAt)

section Swap


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem false_of_swapRow_2E6_of_hr8 (hGLS : GLS3OddLieAutComponentsInput)
    (hOm : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hX : HR8SwapKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
      (modelToG e (su6Levi σ))) : False := by
  have hf : 1 ≤ f := by omega
  have : CharP K 2 := charP_two_of_card hf hK
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  rcases hr8FieldKind_or_hr8SwapKind_Y hGLS hOm hMinn hMcomp hset hf2 hk hK hσ e htC ht with
    hY | hY
  · exact not_hr8FieldKind_Y_of_hr8SwapKind_X hGLS hOm hMinn hMcomp hset hf2 hk hK hσ e htC ht hX hY
  · obtain ⟨htX, Kc, hKc, hDKK, hne, hcomm, hZ, hφ⟩ := hX
    obtain ⟨htY, KY, hKY, hDKY, hneY, hcommY, -, hφY⟩ := hY
    exact false_of_swapRow_2E6_of_components' hset hf2 hk hK hσ e ht hKt rfl htX rfl hKc hDKK hne
      hcomm hZ hφ rfl htY rfl hKY hDKY hneY hcommY hφY

end Swap

section FieldModel


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}

structure FieldRowModel2E6 (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G)
    (A : Subgroup Kˣ) (G₀ : Subgroup G) : Prop where
  perfect : ⁅G₀, G₀⁆ = G₀
  odd_card_center : Odd (Nat.card (center G₀))
  le : L ≤ G₀
  neighbourCore_X_le : neighbourCore e A .X ≤ G₀
  neighbourCore_Y_le : neighbourCore e A .Y ≤ G₀
  normalizer_mem : t ∈ normalizer (G₀ : Set G)
  quotient : ∃ Ψ : G₀ ⧸ center G₀ ≃* adjointGroup Tag.E6 K,
    (∀ (x : L) (hx : (x : G) ∈ G₀),
      ((Ψ (QuotientGroup.mk ⟨(x : G), hx⟩) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        ((e x : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K)) ∧
    ∀ y : adjointGroup Tag.E6 K,
      ((EPilot.normalizerQuotMulAut Ψ ⟨t, normalizer_mem⟩ y : adjointGroup Tag.E6 K) :
        ModGL Tag.E6 K) = twistHom TwistTag.E6 K σ y.1

theorem normalizerQuotMulAut_eq_exactNormalAut {G₀ : Subgroup G}
    (Ψ : G₀ ⧸ center G₀ ≃* adjointGroup Tag.E6 K) {t : G} (htN : t ∈ normalizer (G₀ : Set G))
    (hΨt : ∀ y : adjointGroup Tag.E6 K,
      ((EPilot.normalizerQuotMulAut Ψ ⟨t, htN⟩ y : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        twistHom TwistTag.E6 K σ y.1)
    {σE : K ≃+* K} (hσE : σE.toRingHom = σ) :
    EPilot.normalizerQuotMulAut Ψ ⟨t, htN⟩ = exactNormalAut Tag.E6 K 1 σE 1 := by
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  rw [hΨt y, coe_exactNormalAut, rootDiagUnit_one, one_mul, inv_one, mul_one, hσE]
  simp only [exactQ, pow_one]
  rfl

theorem false_of_fieldRowModel_2E6 [IsSimpleGroup G] [Finite K]
    {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G} {A : Subgroup Kˣ} {G₀ : Subgroup G}
    (h : FieldRowModel2E6 e t A G₀) (ht : orderOf t = 2)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  obtain ⟨σE, hσE⟩ := exists_ringEquiv_toRingHom_eq σ
  obtain ⟨Ψ, -, hΨt⟩ := h.quotient
  have hA := normalizerQuotMulAut_eq_exactNormalAut Ψ h.normalizer_mem hΨt hσE
  exact EPilot.false_of_simple_of_E6_conj_graph_quot K Ψ h.normalizer_mem ht
    ⟨1, 1, 1, σE, by rw [hA, one_mul, inv_one, mul_one, map_one, one_mul]⟩ huniq

end FieldModel

section Assembly


@[expose] def CTFieldFamilyInput2E6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → ∀ (hf2 : 2 ≤ f), Nat.card k = 2 ^ f →
    ∀ (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
      (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 →
      FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t
        (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .X)) →
      FieldNeighbourIso2E6 e t
        (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
        (subsystemGroup TwistTag.E6.tag K C2E6Std.setD) (d4LeviTwist (apply_apply_eq hK hσ))
        (omegaMinusLevi σ) →
      ∃ G₀ : Subgroup G, FieldRowModel2E6 e t (Units.map (algebraMap k K).toMonoidHom).range G₀

@[expose] def UniqueFieldInput2E6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → 2 ≤ f → Nat.card k = 2 ^ f →
    Nat.card K = (2 ^ f) ^ 2 → ∀ (σ : K →+* K), (∀ c, σ c = c ^ 2 ^ f) →
    ∀ (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 → ∀ G₀ : Subgroup G,
      FieldRowModel2E6 e t (Units.map (algebraMap k K).toMonoidHom).range G₀ →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem false_of_fieldRow_2E6_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hSU : SUmNotOddLieInputAt 6) (hOm : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hCT : CTFieldFamilyInput2E6)
    (hU : UniqueFieldInput2E6) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hX : HR8FieldKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
      (modelToG e (su6Levi σ)))
    (hY : HR8FieldKind t (modelToG e (shortRootTorus (algebraMap k K)))
      (modelToG e (omegaMinusLevi σ))) : False := by
  obtain ⟨⟨ΦX⟩, ⟨ΦY⟩⟩ := fieldRowData_2E6 hGLS hSU hOm hMinn hMcomp hset hf2 hk hK hσ e htC ht hX hY
  obtain ⟨G₀, hG₀⟩ := hCT G L f k K hset hf2 hk hK σ hσ e t htC ht ΦX ΦY
  have huniq := hU G L f k K hset hf2 hk hK σ hσ e t htC ht G₀ hG₀
  have := hset.standardSetting.simple
  have := finite_of_card hK
  exact false_of_fieldRowModel_2E6 hG₀ ht huniq

theorem false_of_seitzSetting_twistedE6_of_mulEquiv (hGLS : GLS3OddLieAutComponentsInput)
    (hSU : SUmNotOddLieInputAt 6) (hOm : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hCT : CTFieldFamilyInput2E6)
    (hU : UniqueFieldInput2E6) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) : False := by
  obtain ⟨t, htC, ht⟩ := F4Pilot.exists_orderOf_eq_two_mem_centralizer hset.standardSetting
  rcases kinds_2E6 hGLS hSU hOm hMinn hMcomp hset hf2 hk hK hσ e htC ht with ⟨hX, hY⟩ | ⟨hX, -⟩
  · exact false_of_fieldRow_2E6_of_inputs hGLS hSU hOm hMinn hMcomp hCT hU hset hf2 hk hK hσ e htC
      ht hX hY
  · exact false_of_swapRow_2E6_of_hr8 hGLS hOm hMinn hMcomp hset hf2 hk hK hσ e htC ht hX

end Assembly

section Final

open CFSG.LieType.Chevalley (fixSubfield)

theorem natCard_fixSubfield_of_card_sq {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {σE : K ≃+* K}
    (hσE : σE.toRingHom = σ) : Nat.card (fixSubfield σE) = 2 ^ f := by
  have hσEc : ∀ c, σE c = σ c := fun c => by rw [← hσE]; rfl
  have hσ2 : σE ^ 2 = 1 := by
    apply RingEquiv.ext
    intro c
    change σE (σE c) = c
    rw [hσEc, hσEc]
    exact apply_apply_eq hK hσ c
  have hσ1 : σE ≠ 1 := by
    obtain ⟨c, hc⟩ := exists_apply_ne hf hK hσ
    intro h
    apply hc
    rw [← hσEc, h]
    rfl
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, hcard⟩ := CFSG.LieType.Chevalley.ringEquiv_sq_eq_one_facts Nat.prime_two
    (by omega) hK' hσ2 hσ1
  rw [show 2 * f / 2 = f by omega] at hcard
  exact hcard


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}

theorem false_of_seitzSetting_twistedE6_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hSU : SUmNotOddLieInputAt 6) (hOm : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hCT : CTFieldFamilyInput2E6)
    (hU : UniqueFieldInput2E6) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hL : LieModel L .twistedE6 0 2 f) : False := by
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_lieModel hL
  obtain ⟨σE, hσE⟩ := exists_ringEquiv_toRingHom_eq σ
  exact false_of_seitzSetting_twistedE6_of_mulEquiv (k := fixSubfield σE) hGLS hSU hOm hMinn
    hMcomp hCT hU hset hf2 (natCard_fixSubfield_of_card_sq hf hK hσ hσE) hK hσ e

end Final

end CFSG.SeitzReduction.TwistedE6Pilot
