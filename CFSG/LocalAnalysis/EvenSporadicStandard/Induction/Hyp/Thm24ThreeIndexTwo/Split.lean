module

public import CFSG.GH74.GLS.C3.Layer1.U1aRank

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo

open Subgroup

theorem involution_split_of_index_two {H : Type} [Group H] {N : Subgroup H} (hN : N.index = 2)
    {C : Subgroup H} {x y : H} (hx : x ∈ C) (hy : y ∈ C) (hx2 : orderOf x = 2)
    (hy2 : orderOf y = 2) (hxy : x ≠ y) (hcomm : x * y = y * x) :
    (x ∈ N ∧ y ∈ N) ∨
      ∃ a ∈ C, ∃ b ∈ C, orderOf a = 2 ∧ orderOf b = 2 ∧ a ∈ N ∧ b ∉ N := by
  by_cases hxN : x ∈ N
  · by_cases hyN : y ∈ N
    · exact Or.inl ⟨hxN, hyN⟩
    · exact Or.inr ⟨x, hx, y, hy, hx2, hy2, hxN, hyN⟩
  · by_cases hyN : y ∈ N
    · exact Or.inr ⟨y, hy, x, hx, hy2, hx2, hyN, hxN⟩
    · refine Or.inr ⟨x * y, C.mul_mem hx hy, x, hx, ?_, hx2, ?_, hxN⟩
      · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hx2' : x ^ 2 = 1 := by simpa [hx2] using pow_orderOf_eq_one x
        have hy2' : y ^ 2 = 1 := by simpa [hy2] using pow_orderOf_eq_one y
        have hsq : (x * y) ^ 2 = 1 := by
          rw [Commute.mul_pow hcomm 2, hx2', hy2', mul_one]
        have hne1 : x * y ≠ 1 := by
          intro h
          apply hxy
          have hx_eq : x = (x * y) * y := by rw [mul_assoc, ← pow_two, hy2', mul_one]
          rw [h] at hx_eq
          simpa using hx_eq
        exact orderOf_eq_prime hsq hne1
      · rw [Subgroup.mul_mem_iff_of_index_two hN (a := x) (b := y)]
        exact ⟨fun hx' => absurd hx' hxN, fun hy' => absurd hy' hyN⟩

theorem two_le_pRank_centralizer_subgroupOf {H : Type} [Group H] [Finite H] {N A : Subgroup H}
    {x y : H} (hxN : x ∈ N) (hyN : y ∈ N) (hx : x ∈ centralizer (A : Set H))
    (hy : y ∈ centralizer (A : Set H)) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y)
    (hcomm : x * y = y * x) :
    2 ≤ CFSG.pRank 2 ↥(centralizer ((A.subgroupOf N : Subgroup ↥N) : Set ↥N)) := by
  have hxmem : (⟨x, hxN⟩ : ↥N) ∈
      centralizer ((A.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hx (g : H)
      (Subgroup.mem_subgroupOf.1 hg))
  have hymem : (⟨y, hyN⟩ : ↥N) ∈
      centralizer ((A.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hy (g : H)
      (Subgroup.mem_subgroupOf.1 hg))
  have hx2' : orderOf (⟨x, hxN⟩ : ↥N) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hx2
  have hy2' : orderOf (⟨y, hyN⟩ : ↥N) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hy2
  have hcomm' : (⟨x, hxN⟩ : ↥N) * ⟨y, hyN⟩ = ⟨y, hyN⟩ * ⟨x, hxN⟩ :=
    Subtype.ext hcomm
  have hne' : (⟨x, hxN⟩ : ↥N) ≠ ⟨y, hyN⟩ :=
    fun h => hxy (congrArg Subtype.val h)
  exact CFSG.GH74.GLS.C3.Layer1.U1a.two_le_pRank_of_commute
    hxmem hymem hx2' hy2' hcomm' hne'

end CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo
