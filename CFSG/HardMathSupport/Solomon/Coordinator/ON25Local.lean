module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25K0
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

section

theorem on25_exists_conj {A : Subgroup GM} (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) {a : GM}
    (ha : a ∈ A) (haz : a ∉ zpowers zG) :
    ∃ n : GM, centralizer {a} = zpowers a ⊔ K0G.map (MulAut.conj n).toMonoidHom ∧
      zpowers a ⊓ K0G.map (MulAut.conj n).toMonoidHom = ⊥ := by
  obtain ⟨P, hAP⟩ := (isPGroup_of_E27 hA).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hP : (MulAut.conj g).toMonoidHom a ∈ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hAP ha)
  have hz : (MulAut.conj g).toMonoidHom a ∉ zpowers zG := conj_not_mem_zpowers haz g
  obtain ⟨w, hw, c, hwc⟩ := exists_word_conj_x0 hP hz
  set n := g⁻¹ * wordN w
  have han : a = n * (xG 0 ^ 1 * zG ^ c) * n⁻¹ := by
    rw [pow_one, ← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  obtain ⟨h1, h2⟩ := centralizer_conj n (α := 1) (by norm_num) c
  rw [← han] at h1 h2
  exact ⟨n, h1, h2⟩

theorem on25_z_mem_K (n : GM) : zG ∈ K0G.map (MulAut.conj n).toMonoidHom :=
  ⟨zG, zG_mem_K0, conj_zG n⟩

theorem on25_card_K (n : GM) : Nat.card (K0G.map (MulAut.conj n).toMonoidHom) = 1080 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  exact centralizer_x0_eq.2

noncomputable def on25_KEquiv (n : GM) :
    ↥K0G ≃* ↥(K0G.map (MulAut.conj n).toMonoidHom) :=
  K0G.equivMapOfInjective _ (MulAut.conj n).injective

theorem on25_K_quasisimple (n : GM) :
    CFSG.Open.IsQuasisimple ↥(K0G.map (MulAut.conj n).toMonoidHom) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (on25_KEquiv n)
    on25_K0_quasisimple

theorem on25_card_center_K (n : GM) :
    Nat.card (Subgroup.center ↥(K0G.map (MulAut.conj n).toMonoidHom)) = 3 := by
  have hc : (Subgroup.center ↥K0G).map (on25_KEquiv n).toMonoidHom =
      Subgroup.center ↥(K0G.map (MulAut.conj n).toMonoidHom) :=
    Subgroup.map_center_eq (on25_KEquiv n)
  rw [← hc, Subgroup.card_map_of_injective (on25_KEquiv n).injective]
  exact on25_card_center_K0

theorem on25_center_K_pgroup (n : GM) :
    IsPGroup 3 (Subgroup.center ↥(K0G.map (MulAut.conj n).toMonoidHom)) :=
  IsPGroup.of_card (n := 1) (by rw [on25_card_center_K, pow_one])

theorem on25_card_zG : Nat.card (zpowers zG) = 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime relG.xcube relG.x1

theorem on25_card_center_GM : Nat.card (center GM) = 3 := by
  rw [center_GM]
  exact on25_card_zG

end

end CFSG.HardMathSupport.Solomon.Coordinator
