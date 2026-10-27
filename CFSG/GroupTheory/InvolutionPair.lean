module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.GroupTheory

open Subgroup

variable {X : Type*} [Group X]

theorem coe_zpowers_eq_pair [Finite X] {u : X} (hu : u * u = 1) (hu1 : u ≠ 1) :
    (Subgroup.zpowers u : Set X) = {1, u} := by
  have hmem : ({1, u} : Set X) ⊆ (Subgroup.zpowers u : Set X) := by
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact Subgroup.one_mem _
    · rw [hx]; exact Subgroup.mem_zpowers u
  have hcard : Nat.card (Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two]) hu1]
  have hcard' : (Subgroup.zpowers u : Set X).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hpair : ({1, u} : Set X).ncard = 2 := by
    rw [Set.ncard_pair hu1.symm]
  exact (Set.eq_of_subset_of_ncard_le hmem (by rw [hcard', hpair])).symm

theorem card_closure_pair_eq_four [Finite X] {u v : X}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) :
    Nat.card (Subgroup.closure ({u, v} : Set X)) = 4 := by
  have hsup : Subgroup.closure ({u, v} : Set X) =
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
      · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    · apply sup_le
      · rw [Subgroup.zpowers_eq_closure]
        apply Subgroup.closure_mono
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Set.mem_insert u {v}
      · rw [Subgroup.zpowers_eq_closure]
        apply Subgroup.closure_mono
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Set.mem_insert_of_mem u rfl
  have hu2 : Nat.card (Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two]) hu1]
  have hv2 : Nat.card (Subgroup.zpowers v) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two]) hv1]
  have hdisj : Disjoint (Subgroup.zpowers u) (Subgroup.zpowers v) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxU : x ∈ Subgroup.zpowers u := (Subgroup.mem_inf.mp hx).1
    have hxV : x ∈ Subgroup.zpowers v := (Subgroup.mem_inf.mp hx).2
    have hxU' : x ∈ ({1, u} : Set X) := by
      change x ∈ (Subgroup.zpowers u : Set X) at hxU
      rwa [coe_zpowers_eq_pair hu hu1] at hxU
    have hxV' : x ∈ ({1, v} : Set X) := by
      change x ∈ (Subgroup.zpowers v : Set X) at hxV
      rwa [coe_zpowers_eq_pair hv hv1] at hxV
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxU' hxV'
    rcases hxU' with rfl | rfl
    · rfl
    · rcases hxV' with h | h
      · exact h
      · exact absurd h hne
  have hnormal : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers u : Set X) := by
    have hvu : v * u * v⁻¹ = u := by
      rw [inv_eq_of_mul_eq_one_right hv]
      calc v * u * v = v * (u * v) := by rw [mul_assoc]
        _ = v * (v * u) := by rw [huv]
        _ = (v * v) * u := by rw [← mul_assoc]
        _ = u := by rw [hv, one_mul]
    have hvui : v⁻¹ * u * v = u := by
      rw [inv_eq_of_mul_eq_one_right hv]
      calc v * u * v = v * (u * v) := by rw [mul_assoc]
        _ = v * (v * u) := by rw [huv]
        _ = (v * v) * u := by rw [← mul_assoc]
        _ = u := by rw [hv, one_mul]
    intro y hy
    have hy' : y ∈ ({1, v} : Set X) := by
      change y ∈ (Subgroup.zpowers v : Set X) at hy
      rwa [coe_zpowers_eq_pair hv hv1] at hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    change z ∈ (Subgroup.zpowers u : Set X) ↔ y * z * y⁻¹ ∈ (Subgroup.zpowers u : Set X)
    rw [coe_zpowers_eq_pair hu hu1]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy' ⊢
    rcases hy' with hy1 | hyv
    · rw [hy1]; simp
    · rw [hyv]
      have h1 : v * z * v⁻¹ = 1 ↔ z = 1 := by
        constructor
        · intro h
          have := congrArg (fun w => v⁻¹ * w * v) h
          simpa [mul_assoc] using this
        · intro h; rw [h]; simp
      have h2 : v * z * v⁻¹ = u ↔ z = u := by
        constructor
        · intro h
          have := congrArg (fun w => v⁻¹ * w * v) h
          simpa [mul_assoc, hvui] using this
        · intro h; rw [h, hvu]
      constructor
      · rintro (h | h)
        · exact Or.inl (by rw [h]; simp)
        · exact Or.inr (by rw [h, hvu])
      · rintro (h | h)
        · exact Or.inl (h1.mp h)
        · exact Or.inr (h2.mp h)
  have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers u) (Subgroup.zpowers v) hnormal hdisj
  rw [hsup, h, hu2, hv2]

theorem coe_closure_pair_eq [Finite X] {u v : X}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) :
    (Subgroup.closure ({u, v} : Set X) : Set X) = {1, u, v, u * v} := by
  have hmem : ({1, u, v, u * v} : Set X) ⊆ (Subgroup.closure ({u, v} : Set X) : Set X) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]; exact Subgroup.one_mem _
    · rw [hx]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [hx]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [hx]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hcardW : (Subgroup.closure ({u, v} : Set X) : Set X).ncard = 4 := by
    rw [← Nat.card_coe_set_eq (s := (Subgroup.closure ({u, v} : Set X) : Set X))]
    exact card_closure_pair_eq_four hu hv huv hu1 hv1 hne
  have huv1 : u * v ≠ 1 := by
    intro h
    apply hne
    calc u = u * 1 := (mul_one u).symm
      _ = u * (u * v) := by rw [h]
      _ = (u * u) * v := by rw [mul_assoc]
      _ = v := by rw [hu, one_mul]
  have huvu : u * v ≠ u := by
    intro h
    apply hv1
    calc v = (u * u) * v := by rw [hu, one_mul]
      _ = u * (u * v) := by rw [mul_assoc]
      _ = u * u := by rw [h]
      _ = 1 := hu
  have huvv : u * v ≠ v := by
    intro h
    apply hu1
    calc u = u * 1 := (mul_one u).symm
      _ = u * (v * v) := by rw [hv, mul_one]
      _ = (u * v) * v := by rw [mul_assoc]
      _ = v * v := by rw [h]
      _ = 1 := hv
  have hcardS : ({1, u, v, u * v} : Set X).ncard = 4 := by
    have h1 : ({1, u} : Set X).ncard = 2 := Set.ncard_pair hu1.symm
    have h2 : ({v, u * v} : Set X).ncard = 2 := Set.ncard_pair huvv.symm
    have hdisj : Disjoint ({1, u} : Set X) ({v, u * v} : Set X) := by
      rw [Set.disjoint_left]
      intro x hx hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rw [hx] at hy; exact hv1 hy.symm
      · rw [hx] at hy; exact huv1 hy.symm
      · rw [hx] at hy; exact hne hy
      · rw [hx] at hy; exact huvu hy.symm
    have hunion : ({1, u} : Set X) ∪ {v, u * v} = {1, u, v, u * v} := by
      ext x; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [← hunion, Set.ncard_union_eq hdisj, h1, h2]
  exact (Set.eq_of_subset_of_ncard_le hmem (by rw [hcardW, hcardS])).symm

theorem centralizer_pair_comm (x y : X) :
    centralizer ({x, y} : Set X) = centralizer ({y, x} : Set X) := by
  congr 1
  exact Set.pair_comm x y

theorem centralizer_pair_eq_of_mul {u v w : X} (hu : u * u = 1) (h : u * v = w) :
    centralizer ({u, v} : Set X) = centralizer ({u, w} : Set X) := by
  have hv : v = u * w := by rw [← h, ← mul_assoc, hu, one_mul]
  have hw : w = u * v := h.symm
  have hcl : Subgroup.closure ({u, v} : Set X) = Subgroup.closure ({u, w} : Set X) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.subset_closure (by simp)
      · rw [hx, hv]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.subset_closure (by simp)
      · rw [hx, hw]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  rw [← Subgroup.centralizer_closure ({u, v} : Set X), hcl,
    Subgroup.centralizer_closure]

theorem inf_centralizer_inf_centralizer_eq_pair (F : Subgroup X) (x y : X) :
    F ⊓ centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X) =
      F ⊓ centralizer ({x, y} : Set X) := by
  rw [inf_assoc]
  congr 1
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨hx, hy⟩ t ht
    rcases ht with ht | ht
    · rw [ht]; exact hx x rfl
    · rw [ht]; exact hy y rfl
  · intro h
    refine ⟨?_, ?_⟩
    · intro t ht
      exact h t (Or.inl ht)
    · intro t ht
      exact h t (Or.inr ht)

end CFSG.GroupTheory

end
