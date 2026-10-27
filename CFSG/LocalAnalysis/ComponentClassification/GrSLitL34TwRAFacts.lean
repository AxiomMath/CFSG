module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwFinDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts

structure RAHyp : Prop where
  sq₅ : g₅ * g₅ = 1
  sq₆ : g₆ * g₆ = 1
  comm : g₅ * g₆ = g₆ * g₅
  conj₅ : ∀ x ∈ T0, g₅ * x * g₅ ∈ T0
  conj₆ : ∀ x ∈ T0, g₆ * x * g₆ ∈ T0

@[expose] noncomputable def kel (a b : Bool) : Equiv.Perm (Fin 42) :=
  (if a then g₅ else 1) * (if b then g₆ else 1)

@[expose] def kcode (a b : Bool) : Fin 4 := ⟨a.toNat + 2 * b.toNat, by cases a <;> cases b <;> decide⟩

theorem kcode_xor (a b c d : Bool) :
    (kcode (xor a c) (xor b d)).val = (kcode a b).val ^^^ (kcode c d).val := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

namespace RAHyp

variable (h : RAHyp)
include h

theorem kel_mul (a b c d : Bool) : kel a b * kel c d = kel (xor a c) (xor b d) := by
  have e₅ : ∀ x, g₅ * (g₅ * x) = x := fun x => by rw [← mul_assoc, h.sq₅, one_mul]
  have e₆ : ∀ x, g₆ * (g₆ * x) = x := fun x => by rw [← mul_assoc, h.sq₆, one_mul]
  have c₁ : g₆ * g₅ = g₅ * g₆ := h.comm.symm
  have c₂ : ∀ x, g₆ * (g₅ * x) = g₅ * (g₆ * x) := fun x => by rw [← mul_assoc, c₁, mul_assoc]
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [kel, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.false_xor, Bool.xor_true,
      Bool.true_xor, Bool.not_false, Bool.not_true, mul_one, one_mul, mul_assoc, e₅, e₆, c₁, c₂,
      h.sq₅, h.sq₆]

theorem kel_sq (a b : Bool) : kel a b * kel a b = 1 := by
  rw [h.kel_mul]
  simp [kel]

theorem kel_inv (a b : Bool) : (kel a b)⁻¹ = kel a b := inv_eq_of_mul_eq_one_right (h.kel_sq a b)

theorem kel_mem (a b : Bool) : kel a b ∈ RA := by
  have h₅ : g₅ ∈ RA := subset_closure (Or.inr (Or.inl rfl))
  have h₆ : g₆ ∈ RA := subset_closure (Or.inr (Or.inr rfl))
  unfold kel
  refine RA.mul_mem ?_ ?_
  · cases a
    · exact RA.one_mem
    · exact h₅
  · cases b
    · exact RA.one_mem
    · exact h₆

theorem T0_le_RA : T0 ≤ RA := fun _ hx => subset_closure (Or.inl hx)

theorem kel_conj (a b : Bool) {x : Equiv.Perm (Fin 42)} (hx : x ∈ T0) :
    kel a b * x * kel a b ∈ T0 := by
  unfold kel
  cases a <;> cases b
  · simpa using hx
  · simpa using h.conj₆ x hx
  · simpa using h.conj₅ x hx
  · have := h.conj₅ _ (h.conj₆ x hx)
    simp only [↓reduceIte]
    have e : g₅ * g₆ * x * (g₅ * g₆) = g₅ * (g₆ * x * g₆) * g₅ := by
      nth_rw 2 [h.comm]
      group
    rwa [e]

theorem mem_RA_iff {x : Equiv.Perm (Fin 42)} : x ∈ RA ↔ ∃ a b, ∃ t ∈ T0, x = kel a b * t := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | rfl | rfl
      · exact ⟨false, false, y, hy, by simp [kel]⟩
      · exact ⟨true, false, 1, T0.one_mem, by simp [kel]⟩
      · exact ⟨false, true, 1, T0.one_mem, by simp [kel]⟩
    | one => exact ⟨false, false, 1, T0.one_mem, by simp [kel]⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, b, t, ht, rfl⟩ := hy
      obtain ⟨c, d, s, hs, rfl⟩ := hz
      refine ⟨xor a c, xor b d, kel c d * t * kel c d * s,
        T0.mul_mem (h.kel_conj c d ht) hs, ?_⟩
      rw [← h.kel_mul]
      have e := h.kel_sq c d
      calc kel a b * t * (kel c d * s) = kel a b * (kel c d * kel c d) * t * (kel c d * s) := by
            rw [e, mul_one]
        _ = kel a b * kel c d * (kel c d * t * kel c d * s) := by group
    | inv y _ hy =>
      obtain ⟨a, b, t, ht, rfl⟩ := hy
      refine ⟨a, b, kel a b * t⁻¹ * kel a b, h.kel_conj a b (T0.inv_mem ht), ?_⟩
      rw [mul_inv_rev, h.kel_inv]
      have e := h.kel_sq a b
      calc t⁻¹ * kel a b = kel a b * kel a b * t⁻¹ * kel a b := by rw [e, one_mul]
        _ = kel a b * (kel a b * t⁻¹ * kel a b) := by group
  · rintro ⟨a, b, t, ht, rfl⟩
    exact RA.mul_mem (h.kel_mem a b) (h.T0_le_RA ht)


theorem kel_mem_S {a b : Bool} (hk : kel a b ∈ S) : a = false ∧ b = false := by
  cases a <;> cases b
  · exact ⟨rfl, rfl⟩
  · exact (not_mem_S_r₃ (by simpa [kel, r₃] using hk)).elim
  · exact (not_mem_S_r₂ (by simpa [kel, r₂] using hk)).elim
  · exact (not_mem_S_r₄ (by simpa [kel, r₄] using hk)).elim


theorem kel_mem_T0 {a b : Bool} (hk : kel a b ∈ T0) : a = false ∧ b = false :=
  h.kel_mem_S (T0_le_S hk)

theorem kel_mul_mem_T0 {a b : Bool} {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) :
    kel a b * t ∈ T0 ↔ a = false ∧ b = false := by
  constructor
  · intro hx
    refine h.kel_mem_T0 ?_
    have := T0.mul_mem hx (T0.inv_mem ht)
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨rfl, rfl⟩
    simpa [kel] using ht

theorem kel_inj {a b c d : Bool} {t s : Equiv.Perm (Fin 42)} (ht : t ∈ T0) (hs : s ∈ T0)
    (e : kel a b * t = kel c d * s) : a = c ∧ b = d ∧ t = s := by
  have h1 : kel c d * kel a b * (t * s⁻¹) ∈ T0 := by
    have : kel c d * kel a b * (t * s⁻¹) = kel c d * (kel a b * t) * s⁻¹ := by group
    rw [this, e, ← mul_assoc, h.kel_sq, one_mul, mul_inv_cancel]
    exact T0.one_mem
  rw [h.kel_mul] at h1
  obtain ⟨h₁, h₂⟩ := (h.kel_mul_mem_T0 (T0.mul_mem ht (T0.inv_mem hs))).1 h1
  have hac : a = c := by cases a <;> cases c <;> simp_all
  have hbd : b = d := by cases b <;> cases d <;> simp_all
  subst hac hbd
  exact ⟨rfl, rfl, mul_left_cancel e⟩

theorem card_eq : Nat.card RA = 256 := by
  have key : ∀ x : RA, ∃ p : (Bool × Bool) × T0, (x : Equiv.Perm (Fin 42)) = kel p.1.1 p.1.2 * p.2 :=
    fun x => by
      obtain ⟨a, b, t, ht, e⟩ := h.mem_RA_iff.1 x.2
      exact ⟨((a, b), ⟨t, ht⟩), e⟩
  let f : (Bool × Bool) × T0 → RA := fun p =>
    ⟨kel p.1.1 p.1.2 * p.2, h.mem_RA_iff.2 ⟨_, _, _, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, b⟩, t⟩ ⟨⟨c, d⟩, s⟩ e
      have e' : kel a b * t = kel c d * s := congrArg Subtype.val e
      obtain ⟨rfl, rfl, e''⟩ := h.kel_inj t.2 s.2 e'
      rw [Subtype.ext e'']
    · intro x
      obtain ⟨p, e⟩ := key x
      exact ⟨p, Subtype.ext e.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_T0]
  simp

theorem inf_S_eq : RA ⊓ S = T0 := by
  apply le_antisymm
  · rintro x ⟨hx, hS⟩
    obtain ⟨a, b, t, ht, rfl⟩ := h.mem_RA_iff.1 hx
    have hk : kel a b ∈ S := by
      have := S.mul_mem hS (S.inv_mem (T0_le_S ht))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨rfl, rfl⟩ := h.kel_mem_S hk
    simpa [kel] using ht
  · exact le_inf h.T0_le_RA T0_le_S

theorem cosRA_kel (a b : Bool) {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) :
    cosRA (kel a b * t) = kcode a b := by
  have k₅ : g₅⁻¹ = kel true false := by
    rw [inv_eq_of_mul_eq_one_right h.sq₅]
    simp [kel]
  have k₆ : g₆⁻¹ = kel false true := by
    rw [inv_eq_of_mul_eq_one_right h.sq₆]
    simp [kel]
  unfold cosRA
  rw [k₅, k₆, ← mul_assoc, ← mul_assoc, h.kel_mul, h.kel_mul, h.kel_mul_mem_T0 ht,
    h.kel_mul_mem_T0 ht, h.kel_mul_mem_T0 ht]
  cases a <;> cases b <;> simp <;> rfl

theorem cos_mul {x y : Equiv.Perm (Fin 42)} (hx : x ∈ RA) (hy : y ∈ RA) :
    (cosRA (x * y)).val = (cosRA x).val ^^^ (cosRA y).val := by
  obtain ⟨a, b, t, ht, rfl⟩ := h.mem_RA_iff.1 hx
  obtain ⟨c, d, s, hs, rfl⟩ := h.mem_RA_iff.1 hy
  have e : kel a b * t * (kel c d * s) = kel (xor a c) (xor b d) * (kel c d * t * kel c d * s) := by
    rw [← h.kel_mul]
    have e := h.kel_sq c d
    calc kel a b * t * (kel c d * s) = kel a b * (kel c d * kel c d) * t * (kel c d * s) := by
          rw [e, mul_one]
      _ = kel a b * kel c d * (kel c d * t * kel c d * s) := by group
  rw [e, h.cosRA_kel _ _ (T0.mul_mem (h.kel_conj c d ht) hs), h.cosRA_kel _ _ ht,
    h.cosRA_kel _ _ hs, kcode_xor]

theorem eq_of_cosRA {s : Equiv.Perm (Fin 42)} (hs : s ∈ RA) :
    (cosRA s = 1 → ∃ t ∈ T0, s = g₅ * t) ∧ (cosRA s = 2 → ∃ t ∈ T0, s = g₆ * t) := by
  obtain ⟨a, b, t, ht, rfl⟩ := h.mem_RA_iff.1 hs
  rw [h.cosRA_kel _ _ ht]
  constructor
  · intro e
    cases a <;> cases b <;> simp [kcode] at e
    exact ⟨t, ht, by simp [kel]⟩
  · intro e
    cases a <;> cases b <;> simp [kcode] at e
    exact ⟨t, ht, by simp [kel]⟩

theorem klein_inv (hk : ∀ k t, (k = g₅ ∨ k = g₆) → t ∈ T0 → k * t * (k * t) = 1 →
      ∃ e₁ e₂, e₁ ∈ T0 ∧ e₂ ∈ T0 ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₂ ≠ e₁ ∧
        e₁ * e₂ = e₂ * e₁ ∧ e₁ * (k * t) = k * t * e₁ ∧ e₂ * (k * t) = k * t * e₂) :
    ∀ s ∈ RA, s * s = 1 → (cosRA s = 1 ∨ cosRA s = 2) → ∃ e₁ e₂, e₁ ∈ T0 ∧ e₂ ∈ T0 ∧
      e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₂ ≠ e₁ ∧ e₁ * e₂ = e₂ * e₁ ∧
      e₁ * s = s * e₁ ∧ e₂ * s = s * e₂ := by
  intro s hs hsq hc
  rcases hc with hc | hc
  · obtain ⟨t, ht, rfl⟩ := (h.eq_of_cosRA hs).1 hc
    exact hk _ t (Or.inl rfl) ht hsq
  · obtain ⟨t, ht, rfl⟩ := (h.eq_of_cosRA hs).2 hc
    exact hk _ t (Or.inr rfl) ht hsq

theorem exists_t5 (ht : ∃ u ∈ T0, g₅ * u * (g₅ * u) = 1 ∧ g₅ * (g₅ * u) = g₅ * u * g₅ ∧
      g₅ * g₆ * (g₅ * u) = g₅ * u * (g₅ * g₆) ∧ g₅ * u ≠ g₅) :
    ∃ t ∈ RA, cosRA t = 1 ∧ t * t = 1 ∧ g₅ * t = t * g₅ ∧ g₅ * g₆ * t = t * (g₅ * g₆) ∧
      g₅ * g₆ = g₆ * g₅ ∧ t ≠ g₅ := by
  obtain ⟨u, hu, h1, h2, h3, h4⟩ := ht
  have e : g₅ * u = kel true false * u := by simp [kel]
  refine ⟨g₅ * u, ?_, ?_, h1, h2, h3, h.comm, h4⟩
  · rw [e]
    exact h.mem_RA_iff.2 ⟨_, _, _, hu, rfl⟩
  · rw [e, h.cosRA_kel _ _ hu]
    decide

end RAHyp

end CFSG.ComponentClassification.GrSLit.L34Tw

end
