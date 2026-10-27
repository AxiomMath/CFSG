module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Final

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.M12Facts

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13

abbrev NF : Type := Fin 4 × Fin 4 × Fin 2 × Fin 2

@[expose] def act (k l : Fin 2) (u v : Fin 4) : Fin 4 × Fin 4 :=
  if k = 0 then (if l = 0 then (u, v) else (-u, -v)) else (if l = 0 then (v, u) else (-v, -u))

@[expose] def nfMul (p q : NF) : NF :=
  (p.1 + (act p.2.2.1 p.2.2.2 q.1 q.2.1).1, p.2.1 + (act p.2.2.1 p.2.2.2 q.1 q.2.1).2,
   p.2.2.1 + q.2.2.1, p.2.2.2 + q.2.2.2)

@[expose] def nfInv (p : NF) : NF :=
  ((act p.2.2.1 p.2.2.2 (-p.1) (-p.2.1)).1, (act p.2.2.1 p.2.2.2 (-p.1) (-p.2.1)).2,
   p.2.2.1, p.2.2.2)

theorem nfMul_nfInv : ∀ p : NF, nfMul p (nfInv p) = (0, 0, 0, 0) := by decide +kernel

section
variable {G : Type*} [Group G] {S : Subgroup G} {a b y x : G}

@[expose] def nu (a b y x : G) (p : NF) : G :=
  a ^ p.1.val * b ^ p.2.1.val * (y ^ p.2.2.1.val * x ^ p.2.2.2.val)

theorem pow_fin4_add {g : G} (hg : g ^ 4 = 1) (i j : Fin 4) :
    g ^ (i + j : Fin 4).val = g ^ i.val * g ^ j.val := by
  rw [Fin.val_add, ← pow_eq_pow_mod _ hg, pow_add]

theorem pow_fin2_add {g : G} (hg : g ^ 2 = 1) (i j : Fin 2) :
    g ^ (i + j : Fin 2).val = g ^ i.val * g ^ j.val := by
  rw [Fin.val_add, ← pow_eq_pow_mod _ hg, pow_add]

theorem pow_fin4_neg {g : G} (hg : g ^ 4 = 1) (m : Fin 4) :
    g ^ (-m : Fin 4).val = (g ^ m.val)⁻¹ := by
  fin_cases m
  · simp
  · have h : ((-1 : Fin 4) : ℕ) = 3 := by decide
    have : g ^ 3 * g = 1 := by rw [← pow_succ]; exact hg
    simpa [h] using eq_inv_of_mul_eq_one_left this
  · have h : ((-2 : Fin 4) : ℕ) = 2 := by decide
    have : g ^ 2 * g ^ 2 = 1 := by rw [← pow_add]; exact hg
    simpa [h] using eq_inv_of_mul_eq_one_left this
  · have h : ((-3 : Fin 4) : ℕ) = 1 := by decide
    have : g * g ^ 3 = 1 := by rw [← pow_succ']; exact hg
    simpa [h] using eq_inv_of_mul_eq_one_left this

theorem nu_zero : nu a b y x (0, 0, 0, 0) = 1 := by simp [nu]

section Rel
variable (h : M12Data S a b y x)
include h

theorem conj_y_a (n : ℕ) : y * a ^ n * y⁻¹ = b ^ n := by rw [← conj_pow, h.hya]
theorem conj_y_b (n : ℕ) : y * b ^ n * y⁻¹ = a ^ n := by rw [← conj_pow, h.hyb]
theorem conj_x_a (n : ℕ) : x * a ^ n * x⁻¹ = (a ^ n)⁻¹ := by rw [← conj_pow, h.hxa, inv_pow]
theorem conj_x_b (n : ℕ) : x * b ^ n * x⁻¹ = (b ^ n)⁻¹ := by rw [← conj_pow, h.hxb, inv_pow]

theorem comm_ab (u v : ℕ) : a ^ u * b ^ v = b ^ v * a ^ u :=
  (Commute.pow_pow (show Commute a b from h.hab) u v).eq

theorem y_sq : y ^ 2 = 1 := by rw [pow_two]; exact h.hy
theorem x_sq : x ^ 2 = 1 := by rw [pow_two]; exact h.hx

theorem comm_yx (u v : ℕ) : y ^ u * x ^ v = x ^ v * y ^ u :=
  (Commute.pow_pow (show Commute y x from h.hyx) u v).eq

theorem y_ab (u v : ℕ) : y * (a ^ u * b ^ v) = (a ^ v * b ^ u) * y := by
  have : y * (a ^ u * b ^ v) * y⁻¹ = a ^ v * b ^ u := by
    rw [← conj_mul, conj_y_a h, conj_y_b h, comm_ab h]
  calc y * (a ^ u * b ^ v) = (y * (a ^ u * b ^ v) * y⁻¹) * y := by group
    _ = _ := by rw [this]

theorem x_ab (u v : ℕ) : x * (a ^ u * b ^ v) = ((a ^ u)⁻¹ * (b ^ v)⁻¹) * x := by
  have : x * (a ^ u * b ^ v) * x⁻¹ = (a ^ u)⁻¹ * (b ^ v)⁻¹ := by
    rw [← conj_mul, conj_x_a h, conj_x_b h]
  calc x * (a ^ u * b ^ v) = (x * (a ^ u * b ^ v) * x⁻¹) * x := by group
    _ = _ := by rw [this]

theorem yx_ab (u v : ℕ) : (y * x) * (a ^ u * b ^ v) = ((a ^ v)⁻¹ * (b ^ u)⁻¹) * (y * x) := by
  have h1 : x * (a ^ u * b ^ v) * x⁻¹ = (a ^ u)⁻¹ * (b ^ v)⁻¹ := by
    rw [← conj_mul, conj_x_a h, conj_x_b h]
  have h2 : y * ((a ^ u)⁻¹ * (b ^ v)⁻¹) * y⁻¹ = (a ^ v)⁻¹ * (b ^ u)⁻¹ := by
    rw [← conj_mul, ← conj_inv, ← conj_inv, conj_y_a h, conj_y_b h]
    exact (Commute.pow_pow (show Commute a b from h.hab) v u).symm.inv_inv.eq
  calc (y * x) * (a ^ u * b ^ v) = y * (x * (a ^ u * b ^ v) * x⁻¹) * y⁻¹ * (y * x) := by group
    _ = _ := by rw [h1, h2]

theorem act_spec (k l : Fin 2) (u v : Fin 4) :
    (y ^ k.val * x ^ l.val) * (a ^ u.val * b ^ v.val) =
      (a ^ (act k l u v).1.val * b ^ (act k l u v).2.val) * (y ^ k.val * x ^ l.val) := by
  fin_cases k <;> fin_cases l
  · simp [act]
  · simp only [act]
    simp [pow_fin4_neg h.ha, pow_fin4_neg h.hb, x_ab h]
  · simp [act, y_ab h]
  · simp [act, pow_fin4_neg h.ha, pow_fin4_neg h.hb, yx_ab h]

theorem ab_ab (i j I J : ℕ) :
    a ^ i * b ^ j * (a ^ I * b ^ J) = (a ^ i * a ^ I) * (b ^ j * b ^ J) := by
  calc a ^ i * b ^ j * (a ^ I * b ^ J) = a ^ i * ((b ^ j * a ^ I) * b ^ J) := by
        simp only [mul_assoc]
    _ = a ^ i * ((a ^ I * b ^ j) * b ^ J) := by rw [← comm_ab h]
    _ = _ := by simp only [mul_assoc]

theorem yx_yx (k l k' l' : ℕ) :
    (y ^ k * x ^ l) * (y ^ k' * x ^ l') = (y ^ k * y ^ k') * (x ^ l * x ^ l') := by
  calc (y ^ k * x ^ l) * (y ^ k' * x ^ l') = y ^ k * ((x ^ l * y ^ k') * x ^ l') := by
        simp only [mul_assoc]
    _ = y ^ k * ((y ^ k' * x ^ l) * x ^ l') := by rw [← comm_yx h]
    _ = _ := by simp only [mul_assoc]

theorem nu_mul (p q : NF) : nu a b y x p * nu a b y x q = nu a b y x (nfMul p q) := by
  obtain ⟨i, j, k, l⟩ := p
  obtain ⟨i', j', k', l'⟩ := q
  have hs := act_spec h k l i' j'
  unfold nu nfMul
  simp only [pow_fin4_add h.ha, pow_fin4_add h.hb, pow_fin2_add (y_sq h), pow_fin2_add (x_sq h)]
  calc a ^ i.val * b ^ j.val * (y ^ k.val * x ^ l.val) *
        (a ^ i'.val * b ^ j'.val * (y ^ k'.val * x ^ l'.val))
      = a ^ i.val * b ^ j.val * (((y ^ k.val * x ^ l.val) * (a ^ i'.val * b ^ j'.val)) *
          (y ^ k'.val * x ^ l'.val)) := by simp only [mul_assoc]
    _ = a ^ i.val * b ^ j.val * (((a ^ (act k l i' j').1.val * b ^ (act k l i' j').2.val) *
          (y ^ k.val * x ^ l.val)) * (y ^ k'.val * x ^ l'.val)) := by rw [hs]
    _ = (a ^ i.val * b ^ j.val * (a ^ (act k l i' j').1.val * b ^ (act k l i' j').2.val)) *
          ((y ^ k.val * x ^ l.val) * (y ^ k'.val * x ^ l'.val)) := by simp only [mul_assoc]
    _ = _ := by rw [ab_ab h, yx_yx h]

theorem nu_inv (p : NF) : (nu a b y x p)⁻¹ = nu a b y x (nfInv p) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [nu_mul h, nfMul_nfInv, nu_zero]

theorem a_mem : a ∈ S := h.gen ▸ Subgroup.subset_closure (by simp)
theorem b_mem : b ∈ S := h.gen ▸ Subgroup.subset_closure (by simp)
theorem y_mem : y ∈ S := h.gen ▸ Subgroup.subset_closure (by simp)
theorem x_mem : x ∈ S := h.gen ▸ Subgroup.subset_closure (by simp)

theorem nu_mem (p : NF) : nu a b y x p ∈ S :=
  S.mul_mem (S.mul_mem (S.pow_mem (a_mem h) _) (S.pow_mem (b_mem h) _))
    (S.mul_mem (S.pow_mem (y_mem h) _) (S.pow_mem (x_mem h) _))

theorem exists_nf {s : G} (hs : s ∈ S) : ∃ p : NF, s = nu a b y x p := by
  rw [← h.gen] at hs
  induction hs using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨(1, 0, 0, 0), by simp [nu]⟩
    · exact ⟨(0, 1, 0, 0), by simp [nu]⟩
    · exact ⟨(0, 0, 1, 0), by simp [nu]⟩
    · exact ⟨(0, 0, 0, 1), by simp [nu]⟩
  | one => exact ⟨(0, 0, 0, 0), nu_zero.symm⟩
  | mul g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨p, rfl⟩ := h₁
    obtain ⟨q, rfl⟩ := h₂
    exact ⟨nfMul p q, nu_mul h p q⟩
  | inv g _ h₁ =>
    obtain ⟨p, rfl⟩ := h₁
    exact ⟨nfInv p, (nu_inv h p)⟩

theorem nu_injective : Function.Injective (nu a b y x) := by
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  let f : NF → S := fun p => ⟨nu a b y x p, nu_mem h p⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨p, rfl⟩ := exists_nf h hs
    exact ⟨p, rfl⟩
  have hcard : Nat.card NF ≤ Nat.card S := by
    rw [h.card, Nat.card_eq_fintype_card]
    simp
  have hbij := hsurj.bijective_of_nat_card_le hcard
  intro p q hpq
  exact hbij.1 (Subtype.ext hpq)

end Rel
end

end CFSG.GH74.GLS.Stage1.Thm6.M12Facts
