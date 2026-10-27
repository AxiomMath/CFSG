module

public import Certificates.Data.Kernel.SporCov.BaseKit
public import CFSG.Certificates.Kernel.SporCov.Words
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.KC.Loop CFSG.Sporadic.Th

variable {G : Type} [Group G]

@[expose] def fP (a b : G) (c : ℕ) : G :=
  if c = 0 then a else if c = 1 then a⁻¹ else if c = 2 then b else b⁻¹

theorem fP_zero (a b : G) : fP a b 0 = a := rfl

theorem fP_two (a b : G) : fP a b 2 = b := rfl

private theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

variable {n : ℕ} [MulAction G (Fin n)]

theorem inv_of_left {g : G} {f h : ℕ → ℕ} (hf : ∀ x < n, f x = idx n g x)
    (hl : ∀ x < n, h (f x) = x) : ∀ y < n, h y = idx n g⁻¹ y := by
  intro y hy
  have hx := idx_lt g⁻¹ hy
  have e := hl _ hx
  rwa [hf _ hx, idx_idx_inv] at e

section Kit

variable {a b : G} {fA fAi fB fBi : ℕ → ℕ} (hA : ∀ x < n, fA x = idx n a x)
  (hAi : ∀ x < n, fAi x = idx n a⁻¹ x) (hB : ∀ x < n, fB x = idx n b x)
  (hBi : ∀ x < n, fBi x = idx n b⁻¹ x)
include hA hAi hB hBi

theorem letB_eq (c : ℕ) {x : ℕ} (hx : x < n) :
    letB fA fAi fB fBi c x = idx n (fP a b c) x := by
  unfold letB fP
  rcases c with _ | _ | _ | c
  · exact hA x hx
  · exact hAi x hx
  · exact hB x hx
  · have e0 : Nat.beq (c + 3) 0 = false := rfl
    have e1 : Nat.beq (c + 3) 1 = false := rfl
    have e2 : Nat.beq (c + 3) 2 = false := rfl
    rw [e0, e1, e2]
    simpa using hBi x hx

theorem imB_eq : ∀ (w : List ℕ) {x : ℕ}, x < n →
    imB fA fAi fB fBi w x = idx n (wE (fP a b) w) x
  | [], x, _ => by
    change x = _
    rw [wE_nil, idx_one]
  | c :: w, x, hx => by
    change strictN (letB fA fAi fB fBi c x) (imB fA fAi fB fBi w) = _
    rw [strictN_eq, letB_eq hA hAi hB hBi c hx,
      imB_eq w (idx_lt _ hx), wE_cons, idx_mul]

omit hA hAi hB hBi in
theorem eqB_spec {bs : List ℕ} {u v : List ℕ} (h : eqB fA fAi fB fBi bs u v = true) :
    ∀ x ∈ bs, imB fA fAi fB fBi u x = imB fA fAi fB fBi v x := by
  induction bs with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons y bs ih =>
    change Bool.rec (motive := fun _ => Bool) false (eqB fA fAi fB fBi bs u v)
      (Nat.beq (imB fA fAi fB fBi u y) (imB fA fAi fB fBi v y)) = true at h
    cases hb : Nat.beq (imB fA fAi fB fBi u y) (imB fA fAi fB fBi v y)
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb] at h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.eq_of_beq_eq_true hb
      · exact ih h x hx

omit hA hAi hB hBi in
theorem eqB_of {bs : List ℕ} {u v : List ℕ}
    (h : ∀ x ∈ bs, imB fA fAi fB fBi u x = imB fA fAi fB fBi v x) :
    eqB fA fAi fB fBi bs u v = true := by
  induction bs with
  | nil => rfl
  | cons y bs ih =>
    change Bool.rec (motive := fun _ => Bool) false (eqB fA fAi fB fBi bs u v)
      (Nat.beq (imB fA fAi fB fBi u y) (imB fA fAi fB fBi v y)) = true
    rw [h y List.mem_cons_self, Nat.beq_refl]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem eqB_model {bs : List ℕ} (hbs : ∀ x ∈ bs, x < n)
    (hsep : ∀ g : G, (∀ x ∈ bs, idx n g x = x) → g = 1) :
    Model letP (eqB fA fAi fB fBi bs) (wE (fP a b)) ∧
      ∀ u, chW letP u = true → wE (fP a b) u = 1 → eqB fA fAi fB fBi bs u [] = true := by
  have key := imB_eq hA hAi hB hBi
  refine ⟨Model.of_wE _ fun u v _ _ h => ?_, fun u _ h => eqB_of fun x hx => ?_⟩
  · have h1 : (wE (fP a b) v)⁻¹ * wE (fP a b) u = 1 := by
      apply hsep
      intro x hx
      have e := eqB_spec h x hx
      rw [key u (hbs x hx), key v (hbs x hx)] at e
      rw [idx_mul, e, idx_inv_idx]
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  · rw [key u (hbs x hx), key [] (hbs x hx), h, wE_nil]

end Kit

end CFSG.KD.SporCov

end
