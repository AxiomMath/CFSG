module

public import CFSG.Certificates.Kernel.OrbRow.Tight

public section

namespace CFSG.KC.Co3Cent

open Subgroup CFSG.KC.OrbRow

variable {α : Type*}

theorem card_le_orbit (H : Subgroup (Equiv.Perm α)) [Finite H] (a : α) (s : Finset α)
    (hs : ∀ g ∈ H, g a ∈ s) (S : Subgroup (Equiv.Perm α)) (hS : ∀ g ∈ H, g a = a → g ∈ S)
    (hSH : S ≤ H) : Nat.card H ≤ s.card * Nat.card S := by
  classical
  have hfin : Finite S := Finite.of_injective (fun g : S => (⟨g.1, hSH g.2⟩ : H)) fun g h he => by
    apply Subtype.ext
    simpa using congrArg Subtype.val he
  let r : α → Equiv.Perm α := fun x => if h : ∃ g ∈ H, g a = x then h.choose else 1
  have hr : ∀ g ∈ H, r (g a) ∈ H ∧ r (g a) a = g a := by
    intro g hg
    have h : ∃ g' ∈ H, g' a = g a := ⟨g, hg, rfl⟩
    simp only [r, dif_pos h]
    exact h.choose_spec
  let F : H → s × S := fun g =>
    (⟨g.1 a, hs g.1 g.2⟩, ⟨(r (g.1 a))⁻¹ * g.1, hS _ (H.mul_mem (H.inv_mem (hr g.1 g.2).1) g.2)
      (by rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, (hr g.1 g.2).2])⟩)
  have hF : Function.Injective F := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ he
    have h1 : g a = g' a := congrArg (fun p => (p.1 : α)) he
    have h2 : (r (g a))⁻¹ * g = (r (g' a))⁻¹ * g' := congrArg (fun p => (p.2 : Equiv.Perm α)) he
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := s), Fintype.card_coe] at this

theorem mem_of_tight (H : Subgroup (Equiv.Perm α)) [Finite H] (a : α) (s : Finset α)
    (hs : ∀ x ∈ s, ∃ h ∈ H, h a = x) (S : Subgroup (Equiv.Perm α)) (hS : ∀ g ∈ S, g ∈ H ∧ g a = a)
    (hcard : Nat.card H = s.card * Nat.card S) : ∀ g ∈ H, g a ∈ s := by
  classical
  intro g hg
  by_contra hn
  have hfin : Finite S := Finite.of_injective (fun x : S => (⟨x.1, (hS x.1 x.2).1⟩ : H))
    fun x y he => by
      apply Subtype.ext
      simpa using congrArg Subtype.val he
  have h := card_ge_of_orbit H a (insert (g a) s) (fun x hx => by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨g, hg, rfl⟩
    · exact hs x hx) S hS
  rw [Finset.card_insert_of_notMem hn, hcard, add_mul, one_mul] at h
  have : 0 < Nat.card S := Nat.card_pos
  omega

theorem bound_of_chain (C : Subgroup (Equiv.Perm α)) [Finite C] (b : ℕ → α) (L : ℕ) (c : ℕ → ℕ)
    (m : ℕ) (hcap : ∀ i < L, ∃ s : Finset α, s.card ≤ c i ∧ ∀ g ∈ stabB C b i, g (b i) ∈ s)
    (hL : Nat.card (stabB C b L) ≤ m) : Nat.card C ≤ (∏ i ∈ Finset.range L, c i) * m := by
  have hfin : ∀ i, Finite (stabB C b i) := fun i =>
    Finite.of_injective (fun g : stabB C b i => (⟨g.1, g.2.1⟩ : C)) fun g h he => by
      apply Subtype.ext
      simpa using congrArg Subtype.val he
  have key : ∀ d i, i + d = L → Nat.card (stabB C b i) ≤ (∏ t ∈ Finset.Ico i L, c t) * m := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have : i = L := by omega
      subst this
      rw [Finset.Ico_self, Finset.prod_empty, one_mul]
      exact hL
    | succ d ih =>
      intro i hi
      have hiL : i < L := by omega
      obtain ⟨s, hs, hsub⟩ := hcap i hiL
      have h1 := card_le_orbit (stabB C b i) (b i) s hsub (stabB C b (i + 1))
        (fun g hg hga => ⟨hg.1, fun t ht => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
          · exact hg.2 t ht
          · exact hga⟩)
        (fun g hg => ⟨hg.1, fun t ht => hg.2 t (Nat.lt_succ_of_lt ht)⟩)
      rw [Finset.prod_eq_prod_Ico_succ_bot hiL, mul_assoc]
      exact h1.trans (Nat.mul_le_mul hs (ih (i + 1) (by omega)))
  have h0 : stabB C b 0 = C := by
    ext g
    exact ⟨fun h => h.1, fun h => ⟨h, fun t ht => absurd ht (Nat.not_lt_zero t)⟩⟩
  have := key L 0 (by omega)
  rw [h0, Finset.range_eq_Ico] at *
  exact this

theorem deg_invariant [DecidableEq α] (F : Finset α) (Δ : α → Prop) [DecidablePred Δ]
    (g u v : Equiv.Perm α) (hF : ∀ r, g r ∈ F ↔ r ∈ F) (hΔ : ∀ y, Δ ((u⁻¹ * g * v) y) ↔ Δ y) :
    (F.filter fun r => Δ (u⁻¹ r)).card = (F.filter fun r => Δ (v⁻¹ r)).card := by
  have ki : ∀ (k : Equiv.Perm α) y, k (k⁻¹ y) = y := fun k y => Equiv.apply_symm_apply k y
  have gi : ∀ y, g (g⁻¹ y) = y := ki g
  have key : ∀ r, u⁻¹ (g r) = (u⁻¹ * g * v) (v⁻¹ r) := fun r => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ki v r]
  rw [← Finset.card_map (s := F.filter fun r => Δ (v⁻¹ r)) g.toEmbedding]
  congr 1
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Equiv.toEmbedding_apply]
  constructor
  · intro ⟨hy, hd⟩
    refine ⟨g⁻¹ y, ⟨(hF _).1 (by rw [gi]; exact hy), ?_⟩, gi y⟩
    rw [← hΔ, ← key, gi]
    exact hd
  · rintro ⟨r, ⟨hr, hd⟩, rfl⟩
    exact ⟨(hF r).2 hr, by rw [key, hΔ]; exact hd⟩

end CFSG.KC.Co3Cent

end
