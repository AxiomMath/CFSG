module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

abbrev S8A5 : Type := ↥(alternatingGroup (Fin 5))

instance s8DecEven : DecidablePred (IsEvenVec : (Fin 5 → ZMod 2) → Prop) := fun v => by
  unfold IsEvenVec; infer_instance

theorem s8_permVec_mul (σ τ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2) :
    permVec (σ * τ) v = permVec σ (permVec τ v) := rfl

theorem s8_permVec_one (v : Fin 5 → ZMod 2) : permVec 1 v = v := rfl

theorem s8_add_self (v : Fin 5 → ZMod 2) : v + v = 0 := by
  funext i
  show v i + v i = 0
  generalize v i = x
  revert x
  decide

theorem s8_isEvenVec_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

theorem s8_isEvenVec_add {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp [Finset.sum_add_distrib, hv, hw]

theorem s8_isEvenVec_permVec (σ : Equiv.Perm (Fin 5)) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec at *
  rw [show (∑ i, (v ∘ ⇑σ.symm) i) = ∑ i, v i from Equiv.sum_comp σ.symm v]
  exact hv

theorem s8_fin_faithful (a : S8A5)
    (h : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → permVec (a : Equiv.Perm (Fin 5)) v = v) :
    a = 1 := by
  revert a h
  decide +kernel

theorem s8_fin_sum2 (u : Fin 5 → ZMod 2) (hu : IsEvenVec u) :
    ∃ (a₁ a₂ : S8A5) (w₁ w₂ : Fin 5 → ZMod 2), IsEvenVec w₁ ∧ IsEvenVec w₂ ∧
      u = (permVec (a₁ : Equiv.Perm (Fin 5)) w₁ + w₁) +
        (permVec (a₂ : Equiv.Perm (Fin 5)) w₂ + w₂) := by
  revert u hu
  decide +kernel

theorem s8_fin_irred (u w : Fin 5 → ZMod 2) (hu : IsEvenVec u) (hw : IsEvenVec w) (h0 : u ≠ 0) :
    ∃ a₁ a₂ : S8A5, w = permVec (a₁ : Equiv.Perm (Fin 5)) u + permVec (a₂ : Equiv.Perm (Fin 5)) u ∨
      w = permVec (a₁ : Equiv.Perm (Fin 5)) u := by
  revert u w hu hw h0
  decide +kernel

@[expose] def s8Pa : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def s8Pb : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem s8Pa_mem : s8Pa ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem s8Pb_mem : s8Pb ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem s8P_facts : s8Pa * s8Pa = 1 ∧ s8Pb * s8Pb = 1 ∧ s8Pa * s8Pb = s8Pb * s8Pa := by
  decide +kernel

theorem s8_permVec_sq_a (v : Fin 5 → ZMod 2) : permVec s8Pa (permVec s8Pa v) = v := by
  rw [← s8_permVec_mul, s8P_facts.1, s8_permVec_one]

theorem s8_permVec_sq_b (v : Fin 5 → ZMod 2) : permVec s8Pb (permVec s8Pb v) = v := by
  rw [← s8_permVec_mul, s8P_facts.2.1, s8_permVec_one]

theorem s8_fin_free_a (s : Fin 5 → ZMod 2) (hs : IsEvenVec s) (h : permVec s8Pa s = s) :
    ∃ u : Fin 5 → ZMod 2, IsEvenVec u ∧ s = u + permVec s8Pa u := by
  revert s hs h
  decide +kernel

theorem s8_fin_free_b (s : Fin 5 → ZMod 2) (hs : IsEvenVec s) (h : permVec s8Pb s = s) :
    ∃ u : Fin 5 → ZMod 2, IsEvenVec u ∧ s = u + permVec s8Pb u := by
  revert s hs h
  decide +kernel

theorem s8_fin_free_ab' (r : Fin 5 → ZMod 2) (hr : IsEvenVec r) (ha : permVec s8Pa r = r)
    (hb : permVec s8Pb r = r) :
    ∃ z : Fin 5 → ZMod 2, IsEvenVec z ∧ permVec s8Pb z = z ∧ r = z + permVec s8Pa z := by
  revert r hr ha hb
  decide +kernel

theorem s8_mem_sup_of_commute {X : Type} [Group X] {A B : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

@[expose] def s8Klein {G : Type} [Group G] (a b : G) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) : Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have hba : b * a = a * b := hab.symm
    have e1 : a * (a * b) = b := by rw [← mul_assoc, ha2, one_mul]
    have e2 : (a * b) * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha2, one_mul]
    have e3 : (a * b) * b = a := by rw [mul_assoc, hb2, mul_one]
    have e4 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb2, mul_one]
    have e5 : (a * b) * (a * b) = 1 := by
      rw [mul_assoc, ← mul_assoc b a b, hba, mul_assoc a b b, hb2, mul_one, ha2]
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [ha2, hb2, hba, e1, e2, e3, e4, e5]
  inv_mem' := by
    have hba : b * a = a * b := hab.symm
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · simp
    · rw [ia]; simp
    · rw [ib]; simp
    · rw [mul_inv_rev, ia, ib, hba]; simp

theorem mem_s8Klein_iff {G : Type} [Group G] (a b : G) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (x : G) :
    x ∈ s8Klein a b ha2 hb2 hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b :=
  Iff.rfl

@[expose] def s8PaA : S8A5 := ⟨s8Pa, s8Pa_mem⟩

@[expose] def s8PbA : S8A5 := ⟨s8Pb, s8Pb_mem⟩

theorem s8K4_facts : s8PaA * s8PaA = 1 ∧ s8PbA * s8PbA = 1 ∧ s8PaA * s8PbA = s8PbA * s8PaA ∧
    s8PaA ≠ 1 ∧ s8PbA ≠ 1 ∧ s8PaA * s8PbA ≠ 1 ∧ s8PaA ≠ s8PbA ∧ s8PaA ≠ s8PaA * s8PbA ∧
      s8PbA ≠ s8PaA * s8PbA := by
  decide +kernel

@[expose] def s8K4 : Subgroup S8A5 :=
  s8Klein s8PaA s8PbA s8K4_facts.1 s8K4_facts.2.1 s8K4_facts.2.2.1

theorem s8K4_index : s8K4.index = 15 := by
  have h1 : Nat.card S8A5 = 60 := by
    rw [Nat.card_eq_fintype_card]; decide +kernel
  have h2 : Nat.card s8K4 = 4 := by
    have hset : (s8K4 : Set S8A5) = ↑({1, s8PaA, s8PbA, s8PaA * s8PbA} : Finset S8A5) := by
      ext x; simp [s8K4, s8Klein]
    have h3 : Nat.card s8K4 = (s8K4 : Set S8A5).ncard := Nat.card_coe_set_eq (s8K4 : Set S8A5)
    rw [h3, hset, Set.ncard_coe_finset]
    decide +kernel
  have h4 := s8K4.card_mul_index
  rw [h2, h1] at h4
  omega

end CFSG.OddStandard.SmallF3.Omega
