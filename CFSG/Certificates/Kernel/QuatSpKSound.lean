module

public import Certificates.Data.Kernel.QuatSpK
public import CFSG.Certificates.Kernel.QuatPackSound

public section

namespace CFSG.KC.QuatK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw.Orb

variable {n w : Nat}

theorem ap2_eq {t s : Nat} {T S : Equiv.Perm (Fin n)} (ht : PRep n w t T) (hs : PRep n w s S)
    (x : Fin n) : ap2 w t s x = ((T * S) x : ℕ) := by
  rw [ap2, hs x, ht (S x)]
  rfl

theorem twP_iff {t s a b : Nat} {T S A B : Equiv.Perm (Fin n)} (ht : PRep n w t T)
    (hs : PRep n w s S) (ha : PRep n w a A) (hb : PRep n w b B) :
    twP n w t s a b = true ↔ T * S * A = B * (T * S) := by
  have key : ∀ x : Fin n, Nat.beq (ap2 w t s (pg w (mask w) a x))
      (pg w (mask w) b (ap2 w t s x)) = true ↔ (T * S * A) x = (B * (T * S)) x := by
    intro x
    rw [ha x, ap2_eq ht hs, ap2_eq ht hs x, hb, Nat.beq_eq, Fin.val_inj]
    simp only [Equiv.Perm.mul_apply]
  rw [twP, allN_iff]
  constructor
  · intro h
    exact Equiv.ext fun x => (key x).1 (h x x.2)
  · intro h i hi
    exact (key ⟨i, hi⟩).2 (by rw [h])

theorem sqP_iff {t s : Nat} {T S : Equiv.Perm (Fin n)} (ht : PRep n w t T) (hs : PRep n w s S) :
    sqP n w t s = true ↔ T * S * (T * S) = 1 := by
  have key : ∀ x : Fin n, Nat.beq (ap2 w t s (ap2 w t s x)) x = true ↔
      (T * S * (T * S)) x = (1 : Equiv.Perm (Fin n)) x := by
    intro x
    rw [ap2_eq ht hs x, ap2_eq ht hs, Nat.beq_eq, Fin.val_inj]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rw [sqP, allN_iff]
  constructor
  · intro h
    exact Equiv.ext fun x => (key x).1 (h x x.2)
  · intro h i hi
    exact (key ⟨i, hi⟩).2 (by rw [h])

theorem exists_left_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {y : β}, y ∈ l₂ → ∃ x ∈ l₁, R x y
  | _, _, .nil, _, hy => absurd hy List.not_mem_nil
  | _, _, .cons hxy t, _, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨x, hx, h⟩ := exists_left_of_forall₂ t hy
      exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

theorem exists_right_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {x : α}, x ∈ l₁ → ∃ y ∈ l₂, R x y
  | _, _, .nil, _, hx => absurd hx List.not_mem_nil
  | _, _, .cons hxy t, _, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨y, hy, h⟩ := exists_right_of_forall₂ t hx
      exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem spRefK_spec (hw : 0 < w) {t s e r u v u' v' : Nat} {L : List Nat}
    {T S R U V U' V' : Equiv.Perm (Fin n)} {LP : List (Equiv.Perm (Fin n))}
    (ht : PRep n w t T) (hs : PRep n w s S) (he : CRep n w e 1) (hr : CRep n w r R)
    (hu : PRep n w u U) (hv : PRep n w v V) (hu' : PRep n w u' U') (hv' : PRep n w v' V')
    (hL : List.Forall₂ (CRep n w) L LP) (h : spRefK n w t s e r u v u' v' L = true) :
    ¬ (T * S * U = U * (T * S) ∧ T * S * V = V * (T * S) ∧ T * S * (T * S) = 1 ∧
      (∃ X ∈ LP, T * S * U' = X * (T * S)) ∧ (∃ X ∈ LP, T * S * V' = X * (T * S)) ∧
      ∀ X ∈ LP, T * S * X = X * (T * S) → X = 1 ∨ X = R) := by
  rintro ⟨h1, h2, h3, ⟨X4, hX4, h4⟩, ⟨X5, hX5, h5⟩, h6⟩
  simp only [spRefK, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
    Bool.and_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | ⟨b, hb, ⟨hbe, hbr⟩, hbt⟩
  · rw [(twP_iff ht hs hu hu).2 h1] at h
    exact Bool.noConfusion h
  · rw [(twP_iff ht hs hv hv).2 h2] at h
    exact Bool.noConfusion h
  · rw [(sqP_iff ht hs).2 h3] at h
    exact Bool.noConfusion h
  · obtain ⟨b, hb, hbX⟩ := exists_left_of_forall₂ hL hX4
    have hf := h b hb
    rw [(twP_iff ht hs hu' hbX.1).2 h4] at hf
    exact Bool.noConfusion hf
  · obtain ⟨b, hb, hbX⟩ := exists_left_of_forall₂ hL hX5
    have hf := h b hb
    rw [(twP_iff ht hs hv' hbX.1).2 h5] at hf
    exact Bool.noConfusion hf
  · obtain ⟨X, hX, hbX⟩ := exists_right_of_forall₂ hL hb
    have hc := (twP_iff ht hs hbX.1 hbX.1).1 hbt
    rw [beq_eq hw hbX he, decide_eq_false_iff_not] at hbe
    rw [beq_eq hw hbX hr, decide_eq_false_iff_not] at hbr
    rcases h6 X hX hc with h7 | h7
    · exact hbe h7
    · exact hbr h7

theorem spScanK_spec {T : Nat → Nat} {N s e r u v u' v' : Nat} {L : List Nat}
    (h : spScanK n w T N s e r u v u' v' L = true) {i : Nat} (hi : i < N) :
    spRefK n w (T i) s e r u v u' v' L = true := by
  rw [spScanK, allN_iff] at h
  have h1 := h i hi
  rwa [strictB_eq] at h1

end CFSG.KC.QuatK

end
