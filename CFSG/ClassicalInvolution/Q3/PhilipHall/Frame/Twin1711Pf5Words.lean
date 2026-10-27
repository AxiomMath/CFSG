module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Pack
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.PkG

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> simp

theorem getD_default' {α : Type} (l : List α) (n : ℕ) (d : α) (h : l.length ≤ n) :
    l.getD n d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

@[expose] def permW {n : ℕ} (G : ℕ → Equiv.Perm (Fin n)) (w : List ℕ) : Equiv.Perm (Fin n) :=
  (w.map G).prod

section Perm

variable {n : ℕ} (G : ℕ → Equiv.Perm (Fin n))

theorem permW_nil : permW G [] = 1 := rfl

theorem permW_cons (l : ℕ) (w : List ℕ) : permW G (l :: w) = G l * permW G w := by
  simp [permW]

theorem permW_single (l : ℕ) : permW G [l] = G l := by
  simp [permW]

theorem permW_append (a b : List ℕ) : permW G (a ++ b) = permW G a * permW G b := by
  simp [permW]

theorem permW_mem {S : Subgroup (Equiv.Perm (Fin n))} (h : ∀ l, G l ∈ S) (w : List ℕ) :
    permW G w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons l w ih => rw [permW_cons]; exact S.mul_mem (h l) ih

theorem permW_invW {invL : ℕ → ℕ} (hI : ∀ l, G (invL l) = (G l)⁻¹) (w : List ℕ) :
    permW G ((w.map invL).reverse) = (permW G w)⁻¹ := by
  unfold permW
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  exact List.map_congr_left fun l _ => by simp [hI]

end Perm

@[expose] def LG {n : ℕ} (words : List (List ℕ)) (GB : ℕ → Equiv.Perm (Fin n)) (l : ℕ) :
    Equiv.Perm (Fin n) :=
  permW GB (words.getD l [])

section Rep

variable {b n : ℕ} (hb : 0 < b) (hn : n ≤ b) {baseGl : List ℕ} {GB : ℕ → Equiv.Perm (Fin n)}
  (hB : ∀ l, Rep b n (baseGl.getD l (one b n)) (GB l)) (words : List (List ℕ))

include hb hn hB in
theorem prep_LG (l : ℕ) :
    Rep b n ((words.map (evalW b n baseGl)).getD l (one b n)) (LG words GB l) := by
  have h := evalW_rep hb hn baseGl GB hB (words.getD l [])
  have e : (words.map (evalW b n baseGl)).getD l (one b n) =
      evalW b n baseGl (words.getD l []) := by
    exact getD_map' (evalW b n baseGl) words l []
  rw [e]
  exact h

include hb hn hB in
theorem prep_permW (w : List ℕ) :
    Rep b n (evalW b n (words.map (evalW b n baseGl)) w) (permW (LG words GB) w) :=
  evalW_rep hb hn _ (LG words GB) (prep_LG hb hn hB words) w

include hb hn hB in
theorem LG_inv {invL : ℕ → ℕ} (N : ℕ) (hN : words.length ≤ N) (hfix : ∀ l, N ≤ l → invL l = l)
    (hc : ∀ l, l < N → comp b n ((words.map (evalW b n baseGl)).getD l (one b n))
      ((words.map (evalW b n baseGl)).getD (invL l) (one b n)) = one b n) (l : ℕ) :
    LG words GB (invL l) = (LG words GB l)⁻¹ := by
  by_cases hl : l < N
  · have h2 := (prep_LG hb hn hB words l).comp hb (prep_LG hb hn hB words (invL l))
    rw [hc l hl] at h2
    exact eq_inv_of_mul_eq_one_right (Rep.unique h2 (Rep.one hb hn))
  · have h1 : words.getD l [] = [] := getD_default' _ _ _ (by omega)
    have h2 : invL l = l := hfix l (by omega)
    have hL : LG words GB l = 1 := by
      unfold LG permW
      rw [h1]
      rfl
    rw [h2, hL]
    simp

end Rep

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.PkG
