module

public import CFSG.LocalAnalysis.OddStandard.Harada75Heis
public import Mathlib.GroupTheory.Nilpotent
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.Harada75

open Heis

@[expose] def Z₀ : Subgroup Heis where
  carrier := {h | h.w = 0}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    show a.w + b.w = 0
    rw [ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    exact ha

theorem mem_Z₀ (h : Heis) : h ∈ Z₀ ↔ h.w = 0 := Iff.rfl

instance (h : Heis) : Decidable (h ∈ Z₀) :=
  decidable_of_iff (h.w = 0) (mem_Z₀ h).symm

theorem card_Z₀ : Nat.card Z₀ = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem neg_eq_self_W₀ : ∀ w : W₀, -w = w := by decide

theorem eq_of_add_eq_zero_W₀ {x y : W₀} (h : x + y = 0) : x = y := by
  have := eq_neg_of_add_eq_zero_left h
  rw [this, neg_eq_self_W₀]

@[expose] def cImage (N : Subgroup Heis) : AddSubgroup W₀ where
  carrier := {w | ∃ h ∈ N, h.w = w}
  zero_mem' := ⟨1, N.one_mem, rfl⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, N.mul_mem ha hb, rfl⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (neg_eq_self_W₀ _).symm⟩

theorem card_eq_cImage_mul (N : Subgroup Heis) :
    Nat.card N = Nat.card (cImage N) * Nat.card ↥(N ⊓ Z₀) := by
  let ρ : N →* Multiplicative W₀ :=
    { toFun := fun n => Multiplicative.ofAdd n.1.w
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have e1 : Nat.card ρ.ker = Nat.card ↥(N ⊓ Z₀) := by
    refine Nat.card_congr
      { toFun := fun n => ⟨n.1.1, n.1.2, by
          have := n.2
          rw [MonoidHom.mem_ker] at this
          exact this⟩
        invFun := fun h => ⟨⟨h.1, h.2.1⟩, by
          rw [MonoidHom.mem_ker]
          exact h.2.2⟩
        left_inv := fun n => rfl
        right_inv := fun h => rfl }
  have e2 : Nat.card ρ.range = Nat.card (cImage N) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd x.1, by
          obtain ⟨n, hn⟩ := x.2
          exact ⟨n.1, n.2, by rw [← hn]; rfl⟩⟩
        invFun := fun w => ⟨Multiplicative.ofAdd w.1, by
          obtain ⟨h, hh, e⟩ := w.2
          exact ⟨⟨h, hh⟩, by simp [ρ, e]⟩⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
  rw [e1, e2] at h1
  rw [← h1, mul_comm]

theorem card_inf_Z₀_le (N : Subgroup Heis) : Nat.card ↥(N ⊓ Z₀) ≤ 2 := by
  have := Subgroup.card_le_of_le (inf_le_right : N ⊓ Z₀ ≤ Z₀)
  rwa [card_Z₀] at this

theorem card_inf_Z₀_of_mem (N : Subgroup Heis) (h : z₀ ∈ N) : Nat.card ↥(N ⊓ Z₀) = 2 := by
  have hZ : Z₀ ≤ N := by
    intro x hx
    have hx' : x.w = 0 := hx
    have : x = 1 ∨ x = z₀ := by
      have hk := zmod2_cases x.k
      rcases hk with hk | hk
      · left; exact Heis.ext hx' hk
      · right; exact Heis.ext hx' hk
    rcases this with rfl | rfl
    · exact N.one_mem
    · exact h
  have : N ⊓ Z₀ = Z₀ := inf_eq_right.mpr hZ
  rw [this, card_Z₀]

theorem Zc_eq_one (k : ZMod 2) : Zc k = 1 ↔ k = 0 := by
  rcases zmod2_cases k with rfl | rfl
  · simp [Zc_zero]
  · constructor
    · intro h
      exact absurd (congrArg Heis.k h) (by decide)
    · intro h
      exact absurd h (by decide)

theorem exists_two (X : AddSubgroup W₀) (h3 : 3 ≤ Nat.card X) :
    ∃ u ∈ X, ∃ v ∈ X, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
  classical
  have hcard : ∀ S : Finset W₀, (∀ x ∈ X, x ∈ S) → Nat.card X ≤ S.card := by
    intro S hS
    have : (X : Set W₀) ⊆ (S : Set W₀) := fun x hx => hS x hx
    have h1 := Set.ncard_le_ncard this (Finset.finite_toSet S)
    rw [Set.ncard_coe_finset] at h1
    rwa [← Nat.card_coe_set_eq] at h1
  have hu : ∃ u ∈ X, u ≠ 0 := by
    by_contra hne
    push Not at hne
    have := hcard {0} (fun x hx => by simp [hne x hx])
    rw [Finset.card_singleton] at this
    omega
  obtain ⟨u, huX, hu0⟩ := hu
  have hv : ∃ v ∈ X, v ≠ 0 ∧ v ≠ u := by
    by_contra hne
    push Not at hne
    have := hcard {0, u} (fun x hx => by
      by_cases h0 : x = 0
      · simp [h0]
      · simp [hne x hx h0])
    have h2 : ({0, u} : Finset W₀).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨v, hvX, hv0, hvu⟩ := hv
  exact ⟨u, huX, v, hvX, hu0, hv0, hvu.symm⟩

theorem exists_indep (X : AddSubgroup W₀) (h5 : 5 ≤ Nat.card X) :
    ∃ u ∈ X, ∃ v ∈ X, ∃ w ∈ X, Indep u v w := by
  classical
  have hcard : ∀ S : Finset W₀, (∀ x ∈ X, x ∈ S) → Nat.card X ≤ S.card := by
    intro S hS
    have : (X : Set W₀) ⊆ (S : Set W₀) := fun x hx => hS x hx
    have h1 := Set.ncard_le_ncard this (Finset.finite_toSet S)
    rw [Set.ncard_coe_finset] at h1
    rwa [← Nat.card_coe_set_eq] at h1
  have hu : ∃ u ∈ X, u ≠ 0 := by
    by_contra hne
    push Not at hne
    have := hcard {0} (fun x hx => by simp [hne x hx])
    rw [Finset.card_singleton] at this
    omega
  obtain ⟨u, huX, hu0⟩ := hu
  have hv : ∃ v ∈ X, v ≠ 0 ∧ v ≠ u := by
    by_contra hne
    push Not at hne
    have := hcard {0, u} (fun x hx => by
      by_cases h0 : x = 0
      · simp [h0]
      · simp [hne x hx h0])
    have h2 : ({0, u} : Finset W₀).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨v, hvX, hv0, hvu⟩ := hv
  have hw : ∃ w ∈ X, w ≠ 0 ∧ w ≠ u ∧ w ≠ v ∧ w ≠ u + v := by
    by_contra hne
    push Not at hne
    have := hcard {0, u, v, u + v} (fun x hx => by
      by_cases h0 : x = 0
      · simp [h0]
      by_cases h1 : x = u
      · simp [h1]
      by_cases h2 : x = v
      · simp [h2]
      have := hne x hx h0 h1 h2
      simp [this])
    have h4 : ({0, u, v, u + v} : Finset W₀).card ≤ 4 := Finset.card_le_four
    omega
  obtain ⟨w, hwX, hw0, hwu, hwv, hwuv⟩ := hw
  exact ⟨u, huX, v, hvX, w, hwX, hu0, hv0, hvu.symm, hw0, hwu, hwv, hwuv⟩

theorem card_cImage_le_four (N : Subgroup Heis)
    (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : Nat.card (cImage N) ≤ 4 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨u, hu, v, hv, w, hw, hind⟩ := exists_indep (cImage N) hlt
  have horth : ∀ x ∈ cImage N, ∀ y ∈ cImage N, b₀ x y = 0 := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have h1 := comm_formula a b
    rw [hab a ha b hb, mul_inv_cancel_right, mul_inv_cancel] at h1
    have h2 := congrArg Heis.k h1
    simpa [Zc] using h2.symm
  exact no_isotropic_three u v w hind ⟨horth u hu v hv, horth u hu w hw, horth v hv w hw⟩

theorem card_le_eight_of_abelian (N : Subgroup Heis)
    (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : Nat.card N ≤ 8 := by
  have h1 := card_eq_cImage_mul N
  have h2 := card_cImage_le_four N hab
  have h3 := card_inf_Z₀_le N
  rw [h1]
  calc Nat.card (cImage N) * Nat.card ↥(N ⊓ Z₀) ≤ 4 * 2 := Nat.mul_le_mul h2 h3
    _ = 8 := rfl

theorem finset_card_le_subgroup {G : Type*} [Group G] [Finite G] (A : Finset G) (U : Subgroup G)
    (h : ∀ a ∈ A, a ∈ U) : A.card ≤ Nat.card U := by
  have h1 : (A : Set G) ⊆ (U : Set G) := fun a ha => h a ha
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h2
  exact h2.trans_eq (Nat.card_coe_set_eq (U : Set G)).symm

theorem eight_le_card_of_cover (y : W₀ → Heis) (A : Finset W₀)
    (hA : ∀ a ∈ A, ∃ w, (y w).w = a) (hA4 : 4 ≤ A.card) (C : Finset Heis)
    (hC : ∀ w k, Zc k * y w ∈ C) : 8 ≤ C.card := by
  have h1 : A ×ˢ (Finset.univ : Finset (ZMod 2)) ⊆ C.image (fun h : Heis => (h.w, h.k)) := by
    intro q hq
    obtain ⟨hq1, -⟩ := Finset.mem_product.mp hq
    obtain ⟨w₀, hw₀⟩ := hA q.1 hq1
    refine Finset.mem_image.mpr ⟨Zc (q.2 + (y w₀).k) * y w₀, hC w₀ _, ?_⟩
    refine Prod.ext ?_ ?_
    · show (0 : W₀) + (y w₀).w = q.1
      rw [zero_add, hw₀]
    · show q.2 + (y w₀).k + (y w₀).k + beta 0 (y w₀).w = q.2
      have : beta 0 (y w₀).w = 0 := by simp [beta]
      rw [this, add_zero, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h2 := Finset.card_le_card h1
  rw [Finset.card_product, Finset.card_univ, ZMod.card] at h2
  have h3 := Finset.card_image_le (s := C) (f := fun h : Heis => (h.w, h.k))
  omega

end CFSG.OddStandard.Harada75
