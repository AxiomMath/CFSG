module

public import CFSG.RankThree.PartTwo.Sec11.Wreath

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G]

private theorem closure_swap12 (x y z : G) : closure {x, y, z} = closure {y, x, z} := by
  rw [show ({x, y, z} : Set G) = {y, x, z} from Set.insert_comm x y ({z} : Set G)]

private theorem closure_swap23 (x y z : G) : closure {x, y, z} = closure {x, z, y} := by
  congr 1
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem closure_eq_of_odd_zpow {x y z c : G} (hx4 : x ^ 4 = 1)
    {i j k : ℤ} (hi : Odd i) (hc : c = x ^ i * y ^ j * z ^ k) :
    closure {x, y, z} = closure {c, y, z} := by
  have hx4z : x ^ (4 : ℤ) = 1 := by rw [zpow_ofNat, hx4]
  have hzz : z ^ k * z ^ (-k) = 1 := by rw [← zpow_add]; simp
  have hyy : y ^ j * y ^ (-j) = 1 := by rw [← zpow_add]; simp
  have hxi : x ^ i ∈ closure {c, y, z} := by
    have heq : x ^ i = c * z ^ (-k) * y ^ (-j) := by
      rw [hc]; group
    rw [heq]
    exact mul_mem (mul_mem (subset_closure (by simp)) (zpow_mem (subset_closure (by simp)) _))
      (zpow_mem (subset_closure (by simp)) _)
  have hxmem : x ∈ closure {c, y, z} := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, i * i = 1 + 4 * m := by
      obtain ⟨n, rfl⟩ := hi
      exact ⟨n * n + n, by ring⟩
    have hxii : (x ^ i) ^ i = x := by
      rw [← zpow_mul, hm, zpow_add, zpow_one, zpow_mul, hx4z, one_zpow, mul_one]
    rw [← hxii]
    exact zpow_mem hxi i
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxmem
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · rw [hc]
      exact mul_mem (mul_mem (zpow_mem (subset_closure (by simp)) i)
        (zpow_mem (subset_closure (by simp)) j)) (zpow_mem (subset_closure (by simp)) k)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)

theorem fzc_sy2_three_gen {s : Finset G} (hs : s.card ≤ 3) :
    ∃ b₁ b₂ b₃ : G, closure (s : Set G) = closure {b₁, b₂, b₃} := by
  classical
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with h | h | h | h
  · refine ⟨1, 1, 1, ?_⟩
    rw [Finset.card_eq_zero.mp h]
    simp [Subgroup.closure_singleton_one]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, a, a, by simp⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, b, b, by simp⟩
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    exact ⟨a, b, c, by simp⟩

theorem fzc_sy2_exchange {B : Subgroup G} (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB4 : ∀ b ∈ B, b ^ 4 = 1) {b₁ b₂ b₃ : G} (hgen : closure {b₁, b₂, b₃} = B) {c : G}
    (hc : c ∈ B) (hcsq : ∀ b ∈ B, b ^ 2 ≠ c) : ∃ u v : G, closure {c, u, v} = B := by
  have hb1 : b₁ ∈ B := by rw [← hgen]; exact subset_closure (by simp)
  have hb2 : b₂ ∈ B := by rw [← hgen]; exact subset_closure (by simp)
  have hb3 : b₃ ∈ B := by rw [← hgen]; exact subset_closure (by simp)
  have h12 : Commute b₁ b₂ := hBc b₁ hb1 b₂ hb2
  have h13 : Commute b₁ b₃ := hBc b₁ hb1 b₃ hb3
  have h23 : Commute b₂ b₃ := hBc b₂ hb2 b₃ hb3
  obtain ⟨i, j, k, hcjk⟩ := CFSG.RankThree.PartTwo.Sec11.exists_zpow_triple_of_mem_closure
    h12 h13 h23 (show c ∈ closure {b₁, b₂, b₃} by rw [hgen]; exact hc)
  have hodd : Odd i ∨ Odd j ∨ Odd k := by
    by_contra h
    rw [not_or, not_or] at h
    obtain ⟨hi, hj, hk⟩ := h
    rw [Int.not_odd_iff_even] at hi hj hk
    obtain ⟨i', hi'⟩ := (even_iff_exists_two_mul).mp hi
    obtain ⟨j', hj'⟩ := (even_iff_exists_two_mul).mp hj
    obtain ⟨k', hk'⟩ := (even_iff_exists_two_mul).mp hk
    have hXY : Commute (b₁ ^ i') (b₂ ^ j') := h12.zpow_zpow i' j'
    have hXZ : Commute (b₁ ^ i') (b₃ ^ k') := h13.zpow_zpow i' k'
    have hYZ : Commute (b₂ ^ j') (b₃ ^ k') := h23.zpow_zpow j' k'
    have e3 : (b₁ ^ i') ^ (2 : ℤ) = b₁ ^ i := by
      rw [← zpow_mul, show i' * 2 = i by omega]
    have e4 : (b₂ ^ j') ^ (2 : ℤ) = b₂ ^ j := by
      rw [← zpow_mul, show j' * 2 = j by omega]
    have e5 : (b₃ ^ k') ^ (2 : ℤ) = b₃ ^ k := by
      rw [← zpow_mul, show k' * 2 = k by omega]
    have hsq : (b₁ ^ i' * b₂ ^ j' * b₃ ^ k') ^ (2 : ℤ) = b₁ ^ i * b₂ ^ j * b₃ ^ k := by
      have hXYZ : Commute (b₁ ^ i' * b₂ ^ j') (b₃ ^ k') := hXZ.mul_left hYZ
      rw [hXYZ.mul_zpow 2, hXY.mul_zpow 2, e3, e4, e5]
    have hbB : b₁ ^ i' * b₂ ^ j' * b₃ ^ k' ∈ B :=
      mul_mem (mul_mem (zpow_mem hb1 i') (zpow_mem hb2 j')) (zpow_mem hb3 k')
    have hbsq : (b₁ ^ i' * b₂ ^ j' * b₃ ^ k') ^ 2 = c := by
      rw [show (b₁ ^ i' * b₂ ^ j' * b₃ ^ k') ^ 2
            = (b₁ ^ i' * b₂ ^ j' * b₃ ^ k') ^ (2 : ℤ) from (zpow_ofNat _ 2).symm,
        hsq]
      exact hcjk.symm
    exact hcsq _ hbB hbsq
  rcases hodd with hi | hj | hk
  · have h1 : closure {b₁, b₂, b₃} = closure {c, b₂, b₃} :=
      closure_eq_of_odd_zpow (hB4 b₁ hb1) hi hcjk
    exact ⟨b₂, b₃, by rw [← h1, hgen]⟩
  · have hcjk' : c = b₂ ^ j * b₁ ^ i * b₃ ^ k := by
      rw [hcjk, (h12.zpow_zpow i j).eq]
    have h1 : closure {b₂, b₁, b₃} = closure {c, b₁, b₃} :=
      closure_eq_of_odd_zpow (hB4 b₂ hb2) hj hcjk'
    exact ⟨b₁, b₃, by rw [← h1, ← closure_swap12 b₁ b₂ b₃, hgen]⟩
  · have hcjk' : c = b₃ ^ k * b₁ ^ i * b₂ ^ j := by
      rw [hcjk]
      rw [show b₁ ^ i * b₂ ^ j * b₃ ^ k = b₁ ^ i * (b₂ ^ j * b₃ ^ k) from by group]
      rw [(h23.zpow_zpow j k).eq]
      rw [show b₁ ^ i * (b₃ ^ k * b₂ ^ j) = (b₁ ^ i * b₃ ^ k) * b₂ ^ j from by group]
      rw [(h13.zpow_zpow i k).eq]
    have h1 : closure {b₃, b₁, b₂} = closure {c, b₁, b₂} :=
      closure_eq_of_odd_zpow (hB4 b₃ hb3) hk hcjk'
    exact ⟨b₁, b₂,
      by rw [← h1, closure_swap12 b₃ b₁ b₂, closure_swap23 b₁ b₃ b₂, hgen]⟩

end CFSG.OddStandard.SmallF3.FritzII
