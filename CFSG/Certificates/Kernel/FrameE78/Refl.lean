module

public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.FrameE78.Refl

open Matrix

variable {n : ℕ}

@[expose] def rf (C : Matrix (Fin n) (Fin n) (ZMod 3)) (c : Fin n → ZMod 3) :
    Matrix (Fin n) (Fin n) (ZMod 3) :=
  Matrix.of fun p q => (if p = q then 1 else 0) - (C *ᵥ c) p * c q

@[expose] def bf (C : Matrix (Fin n) (Fin n) (ZMod 3)) (a b : Fin n → ZMod 3) : ZMod 3 :=
  a ⬝ᵥ (C *ᵥ b)

variable {C : Matrix (Fin n) (Fin n) (ZMod 3)}

theorem rf_mulVec (c w : Fin n → ZMod 3) : rf C c *ᵥ w = w - (c ⬝ᵥ w) • (C *ᵥ c) := by
  unfold rf
  generalize C *ᵥ c = u
  funext p
  simp only [mulVec, dotProduct, of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

theorem matrix_ext_mulVec {M N : Matrix (Fin n) (Fin n) (ZMod 3)}
    (h : ∀ w, M *ᵥ w = N *ᵥ w) : M = N := by
  ext p q
  have h1 := congrFun (h (Pi.single q 1)) p
  simpa [mulVec, dotProduct, Pi.single_apply] using h1

theorem bf_symm (hC : C.IsSymm) (a b : Fin n → ZMod 3) : bf C a b = bf C b a := by
  unfold bf
  rw [dotProduct_mulVec, ← mulVec_transpose, hC.eq, dotProduct_comm]

theorem rf_mul_self {c : Fin n → ZMod 3} (hc : bf C c c = 2) : rf C c * rf C c = 1 := by
  refine matrix_ext_mulVec fun w => ?_
  rw [← mulVec_mulVec, rf_mulVec, rf_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul]
  unfold bf at hc
  rw [hc]
  funext p
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem rf_conj (hC : C.IsSymm) {a : Fin n → ZMod 3} (ha : bf C a a = 2) (b : Fin n → ZMod 3) :
    rf C a * rf C b * rf C a = rf C (b - bf C a b • a) := by
  refine matrix_ext_mulVec fun w => ?_
  have hs := bf_symm hC a b
  unfold bf at ha hs ⊢
  rw [← mulVec_mulVec, ← mulVec_mulVec, rf_mulVec, rf_mulVec, rf_mulVec, rf_mulVec]
  simp only [dotProduct_sub, dotProduct_smul, sub_dotProduct, smul_dotProduct, mulVec_sub,
    mulVec_smul, smul_eq_mul, ha]
  rw [hs]
  funext p
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem rf_smul {u : ZMod 3} (hu : u * u = 1) (c : Fin n → ZMod 3) : rf C (u • c) = rf C c := by
  ext p q
  simp only [rf, of_apply, mulVec_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  calc u * (C *ᵥ c) p * (u * c q) = (u * u) * ((C *ᵥ c) p * c q) := by ring
    _ = _ := by rw [hu, one_mul]

theorem rf_neg (c : Fin n → ZMod 3) : rf C (-c) = rf C c := by
  rw [← neg_one_smul (ZMod 3) c, rf_smul (by decide)]

theorem rf_comm_of_bf {a b : Fin n → ZMod 3} (h : bf C a b = 0) (h' : bf C b a = 0) :
    rf C a * rf C b = rf C b * rf C a := by
  refine matrix_ext_mulVec fun w => ?_
  unfold bf at h h'
  rw [← mulVec_mulVec, ← mulVec_mulVec, rf_mulVec, rf_mulVec, rf_mulVec, rf_mulVec]
  simp only [dotProduct_sub, dotProduct_smul, h, h', smul_eq_mul, mul_zero, sub_zero]
  funext p
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem sq_one_of_ne : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide

theorem rf_braid (hC : C.IsSymm) {a b : Fin n → ZMod 3} (ha : bf C a a = 2) (hb : bf C b b = 2)
    (h : bf C a b ≠ 0) : rf C a * rf C b * rf C a = rf C b * rf C a * rf C b := by
  rw [rf_conj hC ha, rf_conj hC hb, bf_symm hC b a]
  have hu := sq_one_of_ne _ h
  have e : b - bf C a b • a = (-bf C a b) • (a - bf C a b • b) := by
    rw [smul_sub, smul_smul, neg_mul, hu, neg_smul, neg_smul, one_smul]
    abel
  rw [e, rf_smul (by rw [neg_mul_neg, hu])]

theorem mulVec_ne_zero {c : Fin n → ZMod 3} (hc : bf C c c = 2) : C *ᵥ c ≠ 0 := by
  intro h
  unfold bf at hc
  rw [h, dotProduct_zero] at hc
  exact absurd hc (by decide)

private theorem smul_eq_zero3 {u : ZMod 3} {v : Fin n → ZMod 3} (h : u • v = 0) :
    u = 0 ∨ v = 0 := by
  by_cases hu : u = 0
  · exact Or.inl hu
  · right
    rw [← one_smul (ZMod 3) v, ← sq_one_of_ne u hu, ← smul_smul, h, smul_zero]

theorem rf_fix {c : Fin n → ZMod 3} (hc : bf C c c = 2) (x : Fin n → ZMod 3) :
    rf C c *ᵥ x = x ↔ c ⬝ᵥ x = 0 := by
  rw [rf_mulVec, sub_eq_self]
  refine ⟨fun h => (smul_eq_zero3 h).resolve_right (mulVec_ne_zero hc), fun h => ?_⟩
  rw [h, zero_smul]

private theorem sq_cases : ∀ x : ZMod 3, x * x = 1 → x = 1 ∨ x = -1 := by decide

private theorem key2 : ∀ x : ZMod 3, x * (x * 2) = 2 → x * x = 1 := by decide

theorem rf_inj {a b : Fin n → ZMod 3} (ha : bf C a a = 2) (hb : bf C b b = 2)
    (h : rf C a = rf C b) : a = b ∨ a = -b := by
  have hv : ∀ w, (a ⬝ᵥ w) • (C *ᵥ a) = (b ⬝ᵥ w) • (C *ᵥ b) := by
    intro w
    have h1 := congrArg (· *ᵥ w) h
    simp only [rf_mulVec] at h1
    exact sub_right_injective h1
  obtain ⟨p, hp⟩ : ∃ p, (C *ᵥ a) p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact mulVec_ne_zero ha (funext hc)
  have hsq := sq_one_of_ne _ hp
  have hab : a = ((C *ᵥ b) p * (C *ᵥ a) p) • b := by
    funext q
    have h1 : a q * (C *ᵥ a) p = b q * (C *ᵥ b) p := by
      have h2 := congrFun (hv (Pi.single q 1)) p
      simpa only [Pi.smul_apply, smul_eq_mul, dotProduct_single, mul_one] using h2
    rw [Pi.smul_apply, smul_eq_mul]
    calc a q = a q * ((C *ᵥ a) p * (C *ᵥ a) p) := by rw [hsq, mul_one]
      _ = (a q * (C *ᵥ a) p) * (C *ᵥ a) p := by ring
      _ = _ := by rw [h1]; ring
  set l := (C *ᵥ b) p * (C *ᵥ a) p with hl
  have hll : l * l = 1 := by
    have e : bf C a a = l * (l * bf C b b) := by
      unfold bf
      rw [hab, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [ha, hb] at e
    exact key2 l e.symm
  rcases sq_cases l hll with h1 | h1
  · left
    rw [hab, h1, one_smul]
  · right
    rw [hab, h1, neg_one_smul]

theorem rf_ne_comm (hC : C.IsSymm) {a b : Fin n → ZMod 3} (ha : bf C a a = 2)
    (hb : bf C b b = 2) (hab : a ≠ b) (hab' : a ≠ -b) (h : rf C a * rf C b = rf C b * rf C a) :
    bf C a b = 0 := by
  by_contra h0
  have e : rf C (b - bf C a b • a) = rf C b := by
    rw [← rf_conj hC ha, h, mul_assoc, rf_mul_self ha, mul_one]
  have hn : bf C (b - bf C a b • a) (b - bf C a b • a) = 2 := by
    have hs := bf_symm hC a b
    have hu := sq_one_of_ne _ h0
    unfold bf at ha hb hs ⊢
    simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, ha, hb]
    rw [← hs]
    ring
  have hu := sq_one_of_ne _ h0
  rcases rf_inj hn hb e with e1 | e1
  · have e2 : bf C a b • a = 0 := by
      have e3 : bf C a b • a = -((b - bf C a b • a) - b) := by abel
      rw [e3, e1, sub_self, neg_zero]
    have e4 : a = 0 := by
      rw [← one_smul (ZMod 3) a, ← hu, ← smul_smul, e2, smul_zero]
    rw [e4] at ha
    unfold bf at ha
    rw [mulVec_zero, dotProduct_zero] at ha
    exact absurd ha (by decide)
  · have e2 : a = (-bf C a b) • b := by
      have e3 : bf C a b • a = b + b := by
        have e5 : bf C a b • a = b + b - ((b - bf C a b • a) - -b) := by abel
        rw [e5, e1, sub_self, sub_zero]
      have e4 : a = bf C a b • (b + b) := by
        rw [← e3, smul_smul, hu, one_smul]
      have h2 : bf C a b * 2 = -bf C a b := by
        have h3 : (2 : ZMod 3) = -1 := by decide
        rw [h3, mul_neg_one]
      calc a = bf C a b • (b + b) := e4
        _ = (-bf C a b) • b := by rw [← two_smul (ZMod 3) b, smul_smul, h2]
    rcases sq_cases _ hu with h1 | h1
    · apply hab'
      rw [e2, h1, neg_one_smul]
    · apply hab
      rw [e2, h1, neg_neg, one_smul]

inductive ConjDer (S : Fin n → Matrix (Fin n) (Fin n) (ZMod 3)) :
    Matrix (Fin n) (Fin n) (ZMod 3) → Prop
  | base (i : Fin n) : ConjDer S (S i)
  | conj (i : Fin n) {r : Matrix (Fin n) (Fin n) (ZMod 3)} (h : ConjDer S r) :
      ConjDer S (S i * r * S i)

theorem conjDer_conj {S : Fin n → Matrix (Fin n) (Fin n) (ZMod 3)} (hS : ∀ i, S i * S i = 1)
    {t : Matrix (Fin n) (Fin n) (ZMod 3)} (ht : ConjDer S t) :
    ∀ {r}, ConjDer S r → ConjDer S (t * r * t) := by
  induction ht with
  | base i => exact fun hr => ConjDer.conj i hr
  | @conj i t' _ ih =>
    intro r hr
    have e : S i * t' * S i * r * (S i * t' * S i) = S i * (t' * (S i * r * S i) * t') * S i := by
      simp only [mul_assoc]
    rw [e]
    exact ConjDer.conj i (ih (ConjDer.conj i hr))

theorem conjDer_mul_self {S : Fin n → Matrix (Fin n) (Fin n) (ZMod 3)} (hS : ∀ i, S i * S i = 1)
    {t : Matrix (Fin n) (Fin n) (ZMod 3)} (ht : ConjDer S t) : t * t = 1 := by
  induction ht with
  | base i => exact hS i
  | @conj i t' _ ih =>
    calc S i * t' * S i * (S i * t' * S i) = S i * (t' * (S i * S i) * t') * S i := by
          simp only [mul_assoc]
      _ = 1 := by rw [hS i, mul_one, ih, mul_one, hS i]

@[expose] def Dich {M : Type*} [Mul M] (A : ℕ → ℕ → Prop) (T : Set M) : Prop :=
  (∃ P Q : Set M, P ∪ Q = T ∧ Disjoint P Q ∧ P.Nonempty ∧ Q.Nonempty ∧
      (∀ r ∈ P, ∀ t ∈ P, t * r * t ∈ P) ∧ (∀ r ∈ Q, ∀ t ∈ Q, t * r * t ∈ Q) ∧
      ∀ r ∈ P, ∀ t ∈ Q, r * t = t * r) ∨
    ∃ d : ℕ, (∀ r ∈ T, Set.ncard {t | t ∈ T ∧ r * t ≠ t * r} = d) ∧ A (Set.ncard T) d

theorem dich_image {M : Type*} [Mul M] (f : M ≃* M) {A : ℕ → ℕ → Prop} {T : Set M}
    (h : Dich A T) : Dich A (f '' T) := by
  rcases h with ⟨P, Q, hU, hD, hP, hQ, hPc, hQc, hPQ⟩ | ⟨d, hd, hA⟩
  · refine Or.inl ⟨f '' P, f '' Q, by rw [← Set.image_union, hU],
      (Set.disjoint_image_iff f.injective).2 hD, hP.image f, hQ.image f, ?_, ?_, ?_⟩
    · rintro _ ⟨r, hr, rfl⟩ _ ⟨t, ht, rfl⟩
      exact ⟨t * r * t, hPc r hr t ht, by simp only [map_mul]⟩
    · rintro _ ⟨r, hr, rfl⟩ _ ⟨t, ht, rfl⟩
      exact ⟨t * r * t, hQc r hr t ht, by simp only [map_mul]⟩
    · rintro _ ⟨r, hr, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul, hPQ r hr t ht]
  · refine Or.inr ⟨d, ?_, by rw [Set.ncard_image_of_injective _ f.injective]; exact hA⟩
    rintro _ ⟨r, hr, rfl⟩
    have e : {t | t ∈ f '' T ∧ f r * t ≠ t * f r} = f '' {t | t ∈ T ∧ r * t ≠ t * r} := by
      ext t
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, hne⟩
        refine ⟨u, ⟨hu, fun e => hne ?_⟩, rfl⟩
        rw [← map_mul, ← map_mul, e]
      · rintro ⟨u, ⟨hu, hne⟩, rfl⟩
        refine ⟨⟨u, hu, rfl⟩, fun e => hne ?_⟩
        rw [← map_mul, ← map_mul] at e
        exact f.injective e
    rw [e, Set.ncard_image_of_injective _ f.injective]
    exact hd r hr

@[expose] def conjEquiv {s : Matrix (Fin n) (Fin n) (ZMod 3)} (hs : s * s = 1) :
    Matrix (Fin n) (Fin n) (ZMod 3) ≃* Matrix (Fin n) (Fin n) (ZMod 3) where
  toFun r := s * r * s
  invFun r := s * r * s
  left_inv r := by
    change s * (s * r * s) * s = r
    simp only [← mul_assoc, hs, one_mul]
    rw [mul_assoc, hs, mul_one]
  right_inv r := by
    change s * (s * r * s) * s = r
    simp only [← mul_assoc, hs, one_mul]
    rw [mul_assoc, hs, mul_one]
  map_mul' r t := by
    change s * (r * t) * s = s * r * s * (s * t * s)
    calc s * (r * t) * s = s * r * (s * s) * t * s := by rw [hs, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]

end CFSG.KC.FrameE78.Refl

end
