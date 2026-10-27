module

public import CFSG.GH74.GLS.Stage4.RestDodecA

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  DodecA

variable {G : Type} [Group G] {D : Ch6Notation G}

@[expose] def Ch6Notation.mirror (D : Ch6Notation G) : Ch6Notation G := { D with a := D.a⁻¹ }

namespace DodecA

theorem dodec_sq {Q : Type*} [Group Q] {A W₁ W₂ : Q} (hA : A ^ 3 = 1)
    (h1 : W₁ * A * W₁⁻¹ = A⁻¹) (h2 : W₂ * A * W₂⁻¹ = A⁻¹) (hs1 : W₁ * W₁ = 1) (hs2 : W₂ * W₂ = 1)
    (hc : W₁ * W₂ = W₂ * W₁) : (W₁ * (A * W₂ * A⁻¹)) ^ 2 = A ^ 2 := by
  have f1 : W₁ * A = A⁻¹ * W₁ := by
    calc W₁ * A = (W₁ * A * W₁⁻¹) * W₁ := by group
      _ = A⁻¹ * W₁ := by rw [h1]
  have f2 : W₂ * A⁻¹ = A * W₂ := by
    calc W₂ * A⁻¹ = (W₂ * A * W₂⁻¹)⁻¹ * W₂ := by group
      _ = A * W₂ := by rw [h2, inv_inv]
  have f3 : (W₁ * W₂) * A = A * (W₁ * W₂) := by
    have g2 : W₂ * A = A⁻¹ * W₂ := by
      calc W₂ * A = (W₂ * A * W₂⁻¹) * W₂ := by group
        _ = A⁻¹ * W₂ := by rw [h2]
    have g1 : W₁ * A⁻¹ = A * W₁ := by
      calc W₁ * A⁻¹ = (W₁ * A * W₁⁻¹)⁻¹ * W₁ := by group
        _ = A * W₁ := by rw [h1, inv_inv]
    calc (W₁ * W₂) * A = W₁ * (W₂ * A) := by group
      _ = W₁ * (A⁻¹ * W₂) := by rw [g2]
      _ = (W₁ * A⁻¹) * W₂ := by group
      _ = (A * W₁) * W₂ := by rw [g1]
      _ = A * (W₁ * W₂) := by group
  have f5 : (W₁ * W₂) ^ 2 = 1 := by
    calc (W₁ * W₂) ^ 2 = W₁ * (W₂ * W₁) * W₂ := by rw [pow_two]; simp only [mul_assoc]
      _ = W₁ * (W₁ * W₂) * W₂ := by rw [hc]
      _ = (W₁ * W₁) * (W₂ * W₂) := by group
      _ = 1 := by rw [hs1, hs2, mul_one]
  have hA' : A⁻¹ = A ^ 2 := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact hA
  have f4 : W₁ * (A * W₂ * A⁻¹) = A * (W₁ * W₂) := by
    calc W₁ * (A * W₂ * A⁻¹) = (W₁ * A) * (W₂ * A⁻¹) := by group
      _ = (A⁻¹ * W₁) * (A * W₂) := by rw [f1, f2]
      _ = A⁻¹ * (W₁ * A) * W₂ := by group
      _ = A⁻¹ * (A⁻¹ * W₁) * W₂ := by rw [f1]
      _ = A⁻¹ * A⁻¹ * (W₁ * W₂) := by group
      _ = A * (W₁ * W₂) := by
        rw [hA']
        calc A ^ 2 * A ^ 2 * (W₁ * W₂) = A ^ 3 * A * (W₁ * W₂) := by group
          _ = A * (W₁ * W₂) := by rw [hA, one_mul]
  have hcomm : Commute A (W₁ * W₂) := f3.symm
  rw [f4, hcomm.mul_pow, f5, mul_one]

theorem sq_aux (h : Ch6Basics D) :
    ((D.w₁ * (D.a * D.w₂ * D.a⁻¹)) ^ 2)⁻¹ * D.a ^ 2 ∈ D.H := by
  have : (D.H.subgroupOf (normalizer (D.H : Set G))).Normal := Subgroup.normal_in_normalizer
  let π : ↥(normalizer (D.H : Set G)) →* ↥(normalizer (D.H : Set G)) ⧸
      D.H.subgroupOf (normalizer (D.H : Set G)) := QuotientGroup.mk' _
  let w₁' : ↥(normalizer (D.H : Set G)) := ⟨D.w₁, h.w₁_normH⟩
  let w₂' : ↥(normalizer (D.H : Set G)) := ⟨D.w₂, h.w₂_normH⟩
  let a' : ↥(normalizer (D.H : Set G)) := ⟨D.a, h.a_normH⟩
  have hπ : ∀ x y : ↥(normalizer (D.H : Set G)), π x = π y ↔ (x : G)⁻¹ * (y : G) ∈ D.H :=
    fun x y => by
      show (QuotientGroup.mk x : _ ⧸ _) = QuotientGroup.mk y ↔ _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
  have hπ1 : ∀ x : ↥(normalizer (D.H : Set G)), π x = 1 ↔ (x : G) ∈ D.H := fun x => by
    show (QuotientGroup.mk x : _ ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hA : π a' ^ 3 = 1 := by
    rw [← map_pow π a' 3, hπ1]
    exact h.a_cube
  have hrel : ∀ (w : ↥(normalizer (D.H : Set G))) (h₁ : G), h₁ ∈ D.H →
      (w : G) * D.a * (w : G)⁻¹ = D.a⁻¹ * h₁ → π w * π a' * (π w)⁻¹ = (π a')⁻¹ := by
    intro w h₁ hh₁ hr
    have e : π (w * a' * w⁻¹) = π a'⁻¹ := by
      rw [hπ]
      show ((w : G) * D.a * (w : G)⁻¹)⁻¹ * D.a⁻¹ ∈ D.H
      rw [hr]
      have : (D.a⁻¹ * h₁)⁻¹ * D.a⁻¹ = h₁⁻¹ := by group
      rw [this]
      exact D.H.inv_mem hh₁
    simpa only [map_mul, map_inv] using e
  obtain ⟨h₁, hh₁, hr₁⟩ := h.w₁_a
  obtain ⟨h₂, hh₂, hr₂⟩ := h.w₂_a
  have hsq : ∀ (w : ↥(normalizer (D.H : Set G))), (w : G) * (w : G) ∈ D.H → π w * π w = 1 := by
    intro w hw
    rw [← map_mul, hπ1]
    exact hw
  have hc : π w₁' * π w₂' = π w₂' * π w₁' := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h.w₁_comm_w₂
  have k := dodec_sq hA (hrel w₁' h₁ hh₁ hr₁) (hrel w₂' h₂ hh₂ hr₂) (hsq w₁' h.sq₁)
    (hsq w₂' (by rw [h.w₂_sq]; exact h.z_mem_H)) hc
  have e : π ((w₁' * (a' * w₂' * a'⁻¹)) ^ 2) = π (a' ^ 2) := by
    simpa only [map_mul, map_inv, map_pow] using k
  exact (hπ _ _).1 e

end DodecA

theorem Ch6Basics.mirror_r₂ : D.mirror.r₂ = D.a * D.w₂ * D.a⁻¹ := by
  simp [Ch6Notation.r₂, Ch6Notation.mirror]

theorem Ch6Basics.a_sq_mem_mirror_N (h : Ch6Basics D) : D.a ^ 2 ∈ D.mirror.N := by
  have hH : ∀ x ∈ D.H, x ∈ D.mirror.N := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hw₁ : D.w₁ ∈ D.mirror.N := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hr : D.a * D.w₂ * D.a⁻¹ ∈ D.mirror.N := by
    rw [← Ch6Basics.mirror_r₂]
    exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have h2 : (D.w₁ * (D.a * D.w₂ * D.a⁻¹)) ^ 2 ∈ D.mirror.N := pow_mem (mul_mem hw₁ hr) 2
  have h3 := DodecA.sq_aux h
  have e : D.a ^ 2 = (D.w₁ * (D.a * D.w₂ * D.a⁻¹)) ^ 2 *
      (((D.w₁ * (D.a * D.w₂ * D.a⁻¹)) ^ 2)⁻¹ * D.a ^ 2) := by group
  rw [e]
  exact mul_mem h2 (hH _ h3)

theorem Ch6Basics.a_mem_mirror_N (h : Ch6Basics D) : D.a ∈ D.mirror.N := by
  have hH : ∀ x ∈ D.H, x ∈ D.mirror.N := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have e : D.a = (D.a ^ 2) * (D.a ^ 2) * (D.a ^ 3)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem h.a_sq_mem_mirror_N h.a_sq_mem_mirror_N) (Subgroup.inv_mem _ (hH _ h.a_cube))

theorem Ch6Basics.mirror_N (h : Ch6Basics D) : D.mirror.N = D.N := by
  have hH : ∀ x ∈ D.H, x ∈ D.N := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hH' : ∀ x ∈ D.H, x ∈ D.mirror.N := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hw₁ : D.w₁ ∈ D.N := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hw₁' : D.w₁ ∈ D.mirror.N := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hr₂ : D.r₂ ∈ D.N := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hr₂' : D.a * D.w₂ * D.a⁻¹ ∈ D.mirror.N := by
    rw [← Ch6Basics.mirror_r₂]
    exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x (hx | hx)
    · exact hH x hx
    · rcases hx with rfl | rfl
      · exact hw₁
      ·
        have ha : D.a ∈ D.N := h.a_mem_N
        have e : D.mirror.r₂ = D.a ^ 2 * D.r₂ * (D.a ^ 2)⁻¹ := by
          rw [Ch6Basics.mirror_r₂]
          simp only [Ch6Notation.r₂]
          group
        rw [e]
        exact mul_mem (mul_mem (pow_mem ha 2) hr₂) (Subgroup.inv_mem _ (pow_mem ha 2))
  · refine (Subgroup.closure_le _).2 ?_
    rintro x (hx | hx)
    · exact hH' x hx
    · rcases hx with rfl | rfl
      · exact hw₁'
      · have ha : D.a ∈ D.mirror.N := h.a_mem_mirror_N
        have e : D.r₂ = (D.a ^ 2)⁻¹ * (D.a * D.w₂ * D.a⁻¹) * D.a ^ 2 := by
          simp only [Ch6Notation.r₂]
          group
        rw [e]
        exact mul_mem (mul_mem (Subgroup.inv_mem _ (pow_mem ha 2)) hr₂') (pow_mem ha 2)

theorem Ch6Basics.mirror (h : Ch6Basics D) : Ch6Basics D.mirror :=
  { h with
    a_normH := Subgroup.inv_mem _ h.a_normH
    a_cube := by
      show (D.a⁻¹) ^ 3 ∈ D.H
      rw [inv_pow]
      exact D.H.inv_mem h.a_cube
    w₁_a := by
      obtain ⟨h₁, hh₁, hr⟩ := h.w₁_a
      refine ⟨D.a⁻¹ * h₁⁻¹ * D.a, ?_, ?_⟩
      · show D.a⁻¹ * h₁⁻¹ * D.a ∈ D.H
        have := (mem_normalizer_iff.1 (Subgroup.inv_mem _ h.a_normH) h₁⁻¹).1 (D.H.inv_mem hh₁)
        simpa using this
      · show D.w₁ * D.a⁻¹ * D.w₁⁻¹ = (D.a⁻¹)⁻¹ * (D.a⁻¹ * h₁⁻¹ * D.a)
        calc D.w₁ * D.a⁻¹ * D.w₁⁻¹ = (D.w₁ * D.a * D.w₁⁻¹)⁻¹ := by group
          _ = (D.a⁻¹ * h₁)⁻¹ := by rw [hr]
          _ = (D.a⁻¹)⁻¹ * (D.a⁻¹ * h₁⁻¹ * D.a) := by group
    w₂_a := by
      obtain ⟨h₂, hh₂, hr⟩ := h.w₂_a
      refine ⟨D.a⁻¹ * h₂⁻¹ * D.a, ?_, ?_⟩
      · show D.a⁻¹ * h₂⁻¹ * D.a ∈ D.H
        have := (mem_normalizer_iff.1 (Subgroup.inv_mem _ h.a_normH) h₂⁻¹).1 (D.H.inv_mem hh₂)
        simpa using this
      · show D.w₂ * D.a⁻¹ * D.w₂⁻¹ = (D.a⁻¹)⁻¹ * (D.a⁻¹ * h₂⁻¹ * D.a)
        calc D.w₂ * D.a⁻¹ * D.w₂⁻¹ = (D.w₂ * D.a * D.w₂⁻¹)⁻¹ := by group
          _ = (D.a⁻¹ * h₂)⁻¹ := by rw [hr]
          _ = (D.a⁻¹)⁻¹ * (D.a⁻¹ * h₂⁻¹ * D.a) := by group
    a_mem_N := by
      have := Subgroup.inv_mem _ h.a_mem_mirror_N
      exact this
    S_le := by
      show D.S ≤ ⨆ n ∈ D.mirror.N, conjBy n (D.K₁ ⊔ D.K₂)
      rw [h.mirror_N]
      exact h.S_le
    F_normN := by
      show D.F ≤ normalizer (D.mirror.N : Set G)
      rw [h.mirror_N]
      exact h.F_normN }

theorem conjBy_inv_a_eq (h : Ch6Basics D) {B : Subgroup G} (hB : HInv D.H B) :
    conjBy D.a⁻¹ B = conjBy (D.a ^ 2) B := by
  have e : D.a⁻¹ = D.a ^ 2 * (D.a ^ 3)⁻¹ := by group
  rw [e]
  exact conjBy_mul_of_mem hB (pow_mem h.a_normH 2) (D.H.inv_mem h.a_cube)

theorem conjBy_inv_a_sq_eq (h : Ch6Basics D) {B : Subgroup G} (hB : HInv D.H B) :
    conjBy (D.a⁻¹ ^ 2) B = conjBy D.a B := by
  have e : (D.a⁻¹) ^ 2 = D.a * (D.a ^ 3)⁻¹ := by group
  rw [e]
  exact conjBy_mul_of_mem hB h.a_normH (D.H.inv_mem h.a_cube)

theorem Ch6Basics.mirror_root_1 (_h : Ch6Basics D) : D.mirror.root 1 = D.root 1 :=
  (root_p1 D.mirror).trans (root_p1 D).symm

theorem Ch6Basics.mirror_root_2 (h : Ch6Basics D) : D.mirror.root 2 = D.root 6 := by
  rw [root_p2, root_p6]
  exact conjBy_inv_a_sq_eq h h.H_norm_X₂'

theorem Ch6Basics.mirror_root_3 (h : Ch6Basics D) : D.mirror.root 3 = D.root (-5) := by
  rw [root_p3, root_m5]
  exact conjBy_inv_a_eq h h.H_norm_X₁'

theorem Ch6Basics.mirror_root_4 (_h : Ch6Basics D) : D.mirror.root 4 = D.root 4 :=
  (root_p4 D.mirror).trans (root_p4 D).symm

theorem Ch6Basics.mirror_root_5 (h : Ch6Basics D) : D.mirror.root 5 = D.root (-3) := by
  rw [root_p5, root_m3]
  exact conjBy_inv_a_sq_eq h h.H_norm_X₁

theorem Ch6Basics.mirror_root_6 (h : Ch6Basics D) : D.mirror.root 6 = D.root 2 := by
  rw [root_p6, root_p2]
  exact conjBy_inv_a_eq h h.H_norm_X₂'

end CFSG.GH74.GLS.Stage4.Rest
