module

public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LieType.SeitzGeneration.ExcPlanePair
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.LieType.SeitzGeneration
open scoped commutatorElement

theorem two_le_pRank_three_of_extraspecial {G : Type*} [Group G] [Finite G] {x y : G}
    (hx : x ^ 3 = 1) (hz : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set z := ⁅x, y⁆ with hzdef
  have hxy : x * y = z * y * x := by rw [hzdef, commutatorElement_def]; group
  have hP : ∀ n : ℕ, x ^ n * y = z ^ n * y * x ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : x * z ^ n = z ^ n * x := (hzx.symm.pow_right n).eq
      calc x ^ (n + 1) * y = x * (x ^ n * y) := by rw [pow_succ', mul_assoc]
        _ = x * (z ^ n * y * x ^ n) := by rw [ih]
        _ = (x * z ^ n) * y * x ^ n := by simp only [mul_assoc]
        _ = z ^ n * x * y * x ^ n := by rw [hc]
        _ = z ^ n * (x * y) * x ^ n := by simp only [mul_assoc]
        _ = z ^ n * (z * y * x) * x ^ n := by rw [hxy]
        _ = z ^ (n + 1) * y * x ^ (n + 1) := by rw [pow_succ, pow_succ']; simp only [mul_assoc]
  have hz3 : z ^ 3 = 1 := by
    have h := hP 3
    rw [hx, mul_one] at h
    have h' : z ^ 3 * y = 1 * y := by rw [one_mul]; rw [one_mul] at h; exact h.symm
    exact mul_right_cancel h'
  have hx1 : x ≠ 1 := fun h => hz (by rw [hzdef, h]; simp)
  have hox : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz
  have hind : z ∉ Subgroup.zpowers x := by
    intro hm
    have hxy' : Commute x y → False := fun h => hz (commutatorElement_eq_one_iff_commute.2 h)
    rcases CFSG.SectionRank.eq_one_or_of_mem_zpowers_three hx hm with h | h | h
    · exact hz h
    · exact hxy' (h ▸ hzy)
    · have hc : Commute (x ^ 2) y := h ▸ hzy
      have h4 : Commute ((x ^ 2) ^ 2) y := hc.pow_left 2
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hx, one_mul] at h4
      exact hxy' h4
  have hcard := card_closure_pair_sq Nat.prime_three hzx.symm hox hoz hind
  have hE := isElemAbelian_closure_pair (p := 3) hzx.symm hx hz3
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard

set_option linter.unusedSectionVars false


theorem pRank_three_ne_one_tits {S : Type} [Group S] [Finite S]
    (hv : (LieTypeIndex.tits).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  have hmod := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩
  obtain ⟨K, _, _, _, hK, ⟨φ⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hmod
  obtain ⟨x, y, h, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.Tits_sylow3_cubic_witness hK
  have := two_le_pRank_three_of_extraspecial hx hz hzx hzy
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank
