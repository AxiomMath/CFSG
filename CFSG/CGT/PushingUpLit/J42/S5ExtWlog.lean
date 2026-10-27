module

public import CFSG.GH74.Defs

public section

namespace CFSG.CGT.PushingUpLit.SolK

section Adj

variable {K : Type*} [Group K] (z : K) (hz : ∀ k : K, k * z = z * k) (hzz : z * z = 1)

def s5ext_adj (A : Subgroup K) : Subgroup K where
  carrier := {x | x ∈ A ∨ x * z ∈ A}
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (A.mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact A.mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc, hz y, ← mul_assoc]; exact A.mul_mem hx hy)
    · refine Or.inl ?_
      have h := A.mul_mem hx hy
      rwa [hz y, mul_assoc x z, ← mul_assoc z z y, hzz, one_mul] at h
  one_mem' := Or.inl A.one_mem
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (A.inv_mem hx)
    · refine Or.inr ?_
      have h := A.inv_mem hx
      rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hzz, ← hz] at h

theorem s5ext_mem_adj (A : Subgroup K) (x : K) :
    x ∈ s5ext_adj z hz hzz A ↔ x ∈ A ∨ x * z ∈ A :=
  Iff.rfl

theorem s5ext_adj_isPGroup {A : Subgroup K} (hA : IsPGroup 2 A) :
    IsPGroup 2 (s5ext_adj z hz hzz A) := by
  rintro ⟨x, hx | hx⟩
  · obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  · obtain ⟨k, hk⟩ := hA ⟨x * z, hx⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 : (x * z) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc : Commute x z := hz x
    have h2 : (x * z) ^ 2 ^ (k + 1) = x ^ 2 ^ (k + 1) * z ^ 2 ^ (k + 1) := hc.mul_pow _
    have h3 : z ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ' (2 : ℕ) k, pow_mul z 2 (2 ^ k), sq, hzz, one_pow]
    have h4 : (x * z) ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ (2 : ℕ) k, pow_mul (x * z) (2 ^ k) 2, h1, one_pow]
    rw [h4, h3, mul_one] at h2
    simpa using h2.symm

end Adj

theorem s5ext_sectionalTwoRankLE_of_central {K : Type*} [Group K] [Finite K] (z : K)
    (hz : ∀ k : K, k * z = z * k) (hzz : z * z = 1) {r : ℕ}
    (h : ∀ H : Subgroup K, IsPGroup 2 H → z ∈ H →
      ∃ s : Finset K, s.card ≤ r ∧ Subgroup.closure (s : Set K) = H) :
    CFSG.GH74.SectionalTwoRankLE K r := by
  classical
  intro H hH
  by_cases hzH : z ∈ H
  · exact h H hH hzH
  have hz' : z ∈ s5ext_adj z hz hzz H :=
    (s5ext_mem_adj z hz hzz H z).2 (Or.inr (by rw [hzz]; exact H.one_mem))
  obtain ⟨s, hs, hsH⟩ := h (s5ext_adj z hz hzz H) (s5ext_adj_isPGroup z hz hzz hH) hz'
  let f : K → K := fun x => if x ∈ H then x else x * z
  refine ⟨s.image f, Finset.card_image_le.trans hs, ?_⟩
  have hfH : ∀ x ∈ s, f x ∈ H := by
    intro x hx
    have hx' : x ∈ s5ext_adj z hz hzz H := by
      rw [← hsH]; exact Subgroup.subset_closure (Finset.mem_coe.2 hx)
    by_cases hxH : x ∈ H
    · simp only [f, ite_eq_left hxH]; exact hxH
    · simp only [f, ite_eq_right hxH]; exact ((s5ext_mem_adj z hz hzz H x).1 hx').resolve_left hxH
  have hCH : Subgroup.closure ((s.image f : Finset K) : Set K) ≤ H := by
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact hfH x hx
  refine le_antisymm hCH ?_
  set C := Subgroup.closure ((s.image f : Finset K) : Set K)
  have hsC : (s : Set K) ⊆ s5ext_adj z hz hzz C := by
    intro x hx
    have hfC : f x ∈ C :=
      Subgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx))
    by_cases hxH : x ∈ H
    · refine (s5ext_mem_adj z hz hzz C x).2 (Or.inl ?_)
      simpa only [f, ite_eq_left hxH] using hfC
    · refine (s5ext_mem_adj z hz hzz C x).2 (Or.inr ?_)
      simpa only [f, ite_eq_right hxH] using hfC
  have hle : s5ext_adj z hz hzz H ≤ s5ext_adj z hz hzz C := by
    rw [← hsH]; exact (Subgroup.closure_le _).2 hsC
  intro y hy
  have hy' := hle ((s5ext_mem_adj z hz hzz H y).2 (Or.inl hy))
  rcases (s5ext_mem_adj z hz hzz C y).1 hy' with hyC | hyC
  · exact hyC
  · have h' := H.mul_mem (H.inv_mem hy) (hCH hyC)
    rw [inv_mul_cancel_left] at h'
    exact absurd h' hzH

end CFSG.CGT.PushingUpLit.SolK
