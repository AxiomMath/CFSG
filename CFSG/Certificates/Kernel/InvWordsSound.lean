module

public import Certificates.Data.Kernel.InvWords
public import Mathlib.Algebra.Group.Commute.Basic

public section

namespace CFSG.KC.InvWords

variable {G : Type*} [Group G] (g : ℕ → G)

@[expose] def ev : List ℕ → G
  | [] => 1
  | x :: l => g x * ev l

@[simp] theorem ev_nil : ev g [] = 1 := rfl

@[simp] theorem ev_cons (x : ℕ) (l : List ℕ) : ev g (x :: l) = g x * ev g l := rfl

@[simp] theorem ev_append (a b : List ℕ) : ev g (a ++ b) = ev g a * ev g b := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, mul_assoc]

variable {g}

theorem inv_eq_of_inv (hg : ∀ x, g x * g x = 1) (x : ℕ) : (g x)⁻¹ = g x :=
  (eq_inv_of_mul_eq_one_left (hg x)).symm

theorem ev_reverse (hg : ∀ x, g x * g x = 1) (l : List ℕ) : ev g l.reverse = (ev g l)⁻¹ := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, inv_eq_of_inv hg]

theorem ev_invRedAux (hg : ∀ x, g x * g x = 1) (acc l : List ℕ) :
    ev g (invRedAux acc l) = ev g acc.reverse * ev g l := by
  induction l generalizing acc with
  | nil => simp [invRedAux]
  | cons x l ih =>
    cases acc with
    | nil => simp [invRedAux, ih]
    | cons y acc =>
      by_cases h : x = y
      · subst h
        have hxx : ∀ a, g x * (g x * a) = a := fun a => by rw [← mul_assoc, hg, one_mul]
        simp [invRedAux, ih, mul_assoc, hxx]
      · simp [invRedAux, h, ih, mul_assoc]

theorem ev_invRed (hg : ∀ x, g x * g x = 1) (l : List ℕ) : ev g (invRed l) = ev g l := by
  simp [invRed, ev_invRedAux hg]

structure Good (z : G) : Prop where
  comm : ∀ y, Commute z y
  cube : z ^ 3 = 1

theorem good_one : Good (1 : G) := ⟨fun y => Commute.one_left y, one_pow 3⟩

theorem Good.mul {a b : G} (ha : Good a) (hb : Good b) : Good (a * b) :=
  ⟨fun y => (ha.1 y).mul_left (hb.1 y), by rw [(ha.1 b).mul_pow, ha.2, hb.2, one_mul]⟩

theorem Good.inv {a : G} (ha : Good a) : Good a⁻¹ :=
  ⟨fun y => (ha.1 y).inv_left, by rw [inv_pow, ha.2, inv_one]⟩

theorem good_entryWord (hg : ∀ x, g x * g x = 1) {R : List (List ℕ)}
    (hR : ∀ r ∈ R, Good (ev g r)) (t : List ℕ) : Good (ev g (entryWord R t)) := by
  have hk : ∀ k, Good (ev g (R.getD k [])) := by
    clear t
    revert hR
    induction R with
    | nil => intro _ k; simpa using good_one
    | cons r R ih =>
      intro hR k
      cases k with
      | zero => simpa using hR r List.mem_cons_self
      | succ k => simpa using ih (fun r' hr' => hR r' (List.mem_cons_of_mem _ hr')) k
  match t with
  | [] => exact good_one
  | [_] => exact good_one
  | k :: e :: u =>
    have hz : Good (ev g (if e == 1 then R.getD k [] else (R.getD k []).reverse)) := by
      split
      · exact hk k
      · rw [ev_reverse hg]
        exact (hk k).inv
    simp only [entryWord, ev_append, ev_reverse hg]
    rw [((hz.1 (ev g u)).eq).symm, mul_inv_cancel_right]
    exact hz

theorem good_certWord (hg : ∀ x, g x * g x = 1) {R : List (List ℕ)}
    (hR : ∀ r ∈ R, Good (ev g r)) (c : List (List ℕ)) : Good (ev g (certWord R c)) := by
  induction c with
  | nil => exact good_one
  | cons t c ih =>
    simp only [certWord, List.map_cons, List.flatten_cons, ev_append] at ih ⊢
    exact (good_entryWord hg hR t).mul ih

theorem good_of_invCheck (hg : ∀ x, g x * g x = 1) {R : List (List ℕ)}
    (hR : ∀ r ∈ R, Good (ev g r)) {c : List (List ℕ)} {t : List ℕ}
    (h : invCheck R c t = true) : Good (ev g t) := by
  have he : invRed (certWord R c) = invRed t := by simpa [invCheck] using h
  rw [← ev_invRed hg t, ← he, ev_invRed hg]
  exact good_certWord hg hR c

end CFSG.KC.InvWords
