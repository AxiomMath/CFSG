module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalComponentFree
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSocleSelector
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
public import CFSG.Sporadic.Schreier.TitsComponent

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup CFSG.Blueprint

theorem faithful_suzuki_socle_involution_component_exclusion {A : Type} [Group A] [Finite A]
    {W : Subgroup A} [W.Normal] (hWsimple : IsSimpleGroup W)
    (hWnonab : ∃ x y : W, x * y ≠ y * x) (hCW : centralizer (W : Set A) = ⊥) {a : A}
    (ha : orderOf a = 2) {L : Subgroup A} (hLW : L ≤ W)
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A))) (ℓ e : ℕ) :
    ¬ SuzukiModel W ℓ e := by
  rintro ⟨-, m, hm, K, _, _, he, hK, ⟨φ⟩⟩
  have hK' : Nat.card K = 2 ^ (2 * m + 1) := by rw [hK, he]
  have hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
    LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  have : IsSimpleGroup (suzukiGroup m K) := φ.symm.isSimpleGroup
  have hZ : center (suzukiGroup m K) = ⊥ := by
    refine OutcomeLocal.center_eq_bot_of_isSimpleGroup ?_
    obtain ⟨x, y, hxy⟩ := hWnonab
    exact ⟨φ x, φ y, fun h => hxy (φ.injective (by rw [map_mul, map_mul, h]))⟩
  have hconj := OutcomeLocal.conj_injective_of_center_eq_bot hZ
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hCW φ hZ
  have hρa2 : orderOf (ρ a) = 2 := by rw [orderOf_injective ρ hinj a, ha]
  have hP : IsPGroup 2 (zpowers (ρ a)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hρa2, pow_one]
  have hin : ρ a ∈ ComponentClassification.OuterAutomorphisms.inner (suzukiGroup m K) :=
    (ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order hm hK').2
      _ hP (mem_zpowers _)
  obtain ⟨t, ht⟩ := hin
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective _ hconj t, ht, hρa2]
  have hW : W.map ρ = (MulAut.conj : suzukiGroup m K →* MulAut (suzukiGroup m K)).range :=
    OutcomeLocal.map_eq_range_conj φ hρW
  have hWle : (MulAut.conj : suzukiGroup m K →* MulAut (suzukiGroup m K)).range ≤ ρ.range :=
    hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      (MulAut.conj : suzukiGroup m K →* MulAut (suzukiGroup m K)).range ⊓
        centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      ((MulAut.conj : suzukiGroup m K →* MulAut (suzukiGroup m K)).range ⊓
        centralizer {MulAut.conj t}) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rw [hCWimg, ← ht] at this
    exact this
  have hsol := Sporadic.Schreier.Tits.suzuki_involution_centralizer_solvable hK' t ht2
  exact UnbalancingLocal.ComponentFree.no_component_of_mulEquiv
    (UnbalancingLocal.ComponentFree.centralizerRangeEquiv hconj t).symm
    (fun B => Sporadic.Schreier.Tits.not_isComponent_of_solvable B inferInstance) _
    ((LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL₁.1).mp hL₁)

end CFSG.ComponentClassification.UnbalancedCorr
