module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_normalized {H S : Subgroup G} (hSN : S ≤ normalizer (H : Set G))
    (hS : IsPGroup 2 S) :
    ∃ P : Sylow 2 ↥H, S ≤ normalizer (((P : Subgroup ↥H).map H.subtype : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥S →* MulAut ↥H := H.normalizerMonoidHom.comp (Subgroup.inclusion hSN)
  let _ : MulDistribMulAction ↥S ↥H := MulDistribMulAction.compHom ↥H φ
  have hcard : ¬ 2 ∣ Nat.card (Sylow 2 ↥H) := by
    intro hd
    have h1 := card_sylow_modEq_one 2 ↥H
    have h0 : Nat.card (Sylow 2 ↥H) ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr hd
    have h01 := h0.symm.trans h1
    exact absurd h01 (by decide)
  obtain ⟨P, hP⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥H) hcard
  refine ⟨P, le_normalizer_of_forall_conj_mem fun s hs g hg => ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hg
  have hfix : (⟨s, hs⟩ : ↥S) • P = P := hP ⟨s, hs⟩
  have h1 : (⟨s, hs⟩ : ↥S) • x ∈ (((⟨s, hs⟩ : ↥S) • P : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul x _ _ hx
  rw [hfix] at h1
  refine ⟨_, h1, ?_⟩
  change ((H.normalizerMonoidHom ⟨s, hSN hs⟩) x : G) = s * (x : G) * s⁻¹
  exact Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨s, hSN hs⟩ x

end CFSG.ComponentClassification.Sol76T13
