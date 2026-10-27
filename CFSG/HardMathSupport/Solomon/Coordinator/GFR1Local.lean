module

public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25K0
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

section

set_option linter.unusedSectionVars false


theorem gfr1_K0_isHatSix : IsHatSix ↥K0G := by
  refine ⟨on25_K0_perfect, on25_card_center_K0, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq on25_center_K0).trans
    ((QuotientGroup.quotientKerEquivRange actK).trans (MulEquiv.subgroupCongr range_actK))

theorem gfr1_exists_conj {a : GM} (ha3 : a ^ 3 = 1) (haz : a ∉ zpowers zG) :
    ∃ n : GM, centralizer {a} = zpowers a ⊔ K0G.map (MulAut.conj n).toMonoidHom ∧
      zpowers a ⊓ K0G.map (MulAut.conj n).toMonoidHom = ⊥ := by
  have ha1 : a ≠ 1 := fun h => haz (h ▸ one_mem _)
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hpg : IsPGroup 3 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨P, hAP⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hP : (MulAut.conj g).toMonoidHom a ∈ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hAP (mem_zpowers a))
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

end

end CFSG.HardMathSupport.Solomon.Coordinator
