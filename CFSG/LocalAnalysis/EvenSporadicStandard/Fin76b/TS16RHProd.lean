module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UTool

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem card_sup_commuting {G : Type} [Group G] [Finite G] {S E : Subgroup G}
    (hSE : S ≤ centralizer (E : Set G)) (hdisj : ∀ x ∈ S, x ∈ E → x = 1) :
    Nat.card ↥(S ⊔ E) = Nat.card ↥S * Nat.card ↥E := by
  have hK := card_ker_mul_card_range S E hSE
  have hker : (mulHom S E hSE).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨s, e⟩ hp
    have h1 : (s : G) * e = 1 := hp
    have hs : (s : G) = (e : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hs1 : (s : G) = 1 := hdisj s s.2 (by rw [hs]; exact inv_mem e.2)
    have he1 : (e : G) = 1 := by rw [hs1, one_mul] at h1; exact h1
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext hs1) (Subtype.ext he1)
  have hrange : (mulHom S E hSE).range = S ⊔ E :=
    le_antisymm (range_mulHom_le S E hSE) (sup_le_range_mulHom S E hSE)
  rw [hker, hrange, Subgroup.card_bot, one_mul] at hK
  exact hK

theorem elemAbelian8_of_card4 {G : Type} [Group G] [Finite G] {z c d : G}
    (hz2 : z * z = 1) (hc2 : c * c = 1) (hd2 : d * d = 1)
    (hzc : z * c = c * z) (hzd : z * d = d * z) (hcd : c * d = d * c)
    (hK : Nat.card ↥(Subgroup.closure ({c, d} : Set G)) = 4)
    (hz : z ∉ Subgroup.closure ({c, d} : Set G)) :
    IsElemAbelian 2 (Subgroup.closure ({z, c, d} : Set G)) ∧
      Nat.card ↥(Subgroup.closure ({z, c, d} : Set G)) = 8 := by
  have hpair : ({z, c, d} : Set G).Pairwise Commute := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hab
      | exact Commute.refl _
      | exact hzc
      | exact hzd
      | exact hcd
      | exact hzc.symm
      | exact hzd.symm
      | exact hcd.symm
  have hcomm : IsMulCommutative (Subgroup.closure ({z, c, d} : Set G)) :=
    Subgroup.isMulCommutative_closure hpair
  refine ⟨⟨hcomm, ?_⟩, ?_⟩
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [pow_two]; exact hz2
      · rw [pow_two]; exact hc2
      · rw [pow_two]; exact hd2
    | one => simp
    | mul x y hx hy hx2 hy2 =>
      have hxy : x * y = y * x := by
        have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      calc (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
            rw [pow_two, pow_two, pow_two]
            calc x * y * (x * y) = x * (y * x) * y := by group
              _ = x * (x * y) * y := by rw [hxy]
              _ = x * x * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    | inv x hx hx2 =>
      rw [inv_pow]
      simp [hx2]
  · have hsup : Subgroup.closure ({z, c, d} : Set G) =
        zpowers z ⊔ Subgroup.closure ({c, d} : Set G) := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro y (rfl | rfl | rfl)
        · exact mem_sup_left (mem_zpowers y)
        · exact mem_sup_right (subset_closure (by simp))
        · exact mem_sup_right (subset_closure (by simp))
      · refine sup_le (zpowers_le.2 (subset_closure (by simp))) ?_
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact subset_closure (by simp)
        · exact subset_closure (by simp)
    have hzK : zpowers z ≤ centralizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G) := by
      rw [zpowers_le]
      have hK' : Subgroup.closure ({c, d} : Set G) ≤ centralizer ({z} : Set G) := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact mem_centralizer_singleton_iff.2 hzc.symm
        · exact mem_centralizer_singleton_iff.2 hzd.symm
      exact mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hK' hy)
    have hdisj : ∀ x ∈ zpowers z, x ∈ Subgroup.closure ({c, d} : Set G) → x = 1 := by
      intro x hx hxK
      rcases mem_zpowers_sq_eq_one hz2 hx with h | h
      · exact h
      · exact absurd (h ▸ hxK) hz
    have hzcard : Nat.card ↥(zpowers z) = 2 := by
      have hz1 : z ≠ 1 := fun h => hz (h ▸ one_mem _)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    rw [hsup, card_sup_commuting hzK hdisj, hzcard, hK]

end CFSG.EvenSporadicStandard.Fin76b
