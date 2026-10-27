module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrRec

public section

namespace CFSG.EvenSporadicStandard.TwoHS.SignWr

open Equiv Equiv.Perm

abbrev Wr : Type := RegularWreathProduct (Perm (Fin 5)) (Multiplicative (ZMod 2))

@[expose] def mk (a b : Perm (Fin 5)) (q : Multiplicative (ZMod 2)) : Wr :=
  ⟨fun x => if x = 1 then a else b, q⟩

@[simp]
theorem mk_left_one (a b : Perm (Fin 5)) (q : Multiplicative (ZMod 2)) : (mk a b q).left 1 = a := by
  simp [mk]

@[simp]
theorem mk_left_eps (a b : Perm (Fin 5)) (q : Multiplicative (ZMod 2)) :
    (mk a b q).left eps = b := by
  simp [mk, eps_ne_one]

@[simp]
theorem mk_right (a b : Perm (Fin 5)) (q : Multiplicative (ZMod 2)) : (mk a b q).right = q := rfl

theorem ext3 {u w : Wr} (h1 : u.left 1 = w.left 1) (h2 : u.left eps = w.left eps)
    (h3 : u.right = w.right) : u = w := by
  refine RegularWreathProduct.ext ?_ h3
  funext x
  rcases eq_one_or_eps x with rfl | rfl
  · exact h1
  · exact h2

theorem mk_eta (w : Wr) : mk (w.left 1) (w.left eps) w.right = w :=
  ext3 (by simp) (by simp) rfl

theorem mk_inj {a b c d : Perm (Fin 5)} {p q : Multiplicative (ZMod 2)} :
    mk a b p = mk c d q ↔ a = c ∧ b = d ∧ p = q := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun w : Wr => w.left 1) h,
      by simpa using congrArg (fun w : Wr => w.left eps) h, congrArg RegularWreathProduct.right h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem mk_one_one_one : mk 1 1 1 = 1 := ext3 (by simp) (by simp) rfl

theorem mk_mul_one (a b c d : Perm (Fin 5)) (q : Multiplicative (ZMod 2)) :
    mk a b 1 * mk c d q = mk (a * c) (b * d) q := by
  apply ext3 <;> simp [RegularWreathProduct.mul_def]

theorem mk_mul_eps (a b c d : Perm (Fin 5)) (q : Multiplicative (ZMod 2)) :
    mk a b eps * mk c d q = mk (a * d) (b * c) (eps * q) := by
  apply ext3 <;> simp [RegularWreathProduct.mul_def, eps_inv, eps_mul_eps]

@[expose] def inFirst : Perm (Fin 5) →* Wr where
  toFun c := mk c 1 1
  map_one' := mk_one_one_one
  map_mul' c d := by rw [mk_mul_one, mul_one]

@[expose] def inSecond : Perm (Fin 5) →* Wr where
  toFun d := mk 1 d 1
  map_one' := mk_one_one_one
  map_mul' c d := by rw [mk_mul_one, mul_one]

theorem inFirst_apply (c : Perm (Fin 5)) : inFirst c = mk c 1 1 := rfl

theorem inSecond_apply (d : Perm (Fin 5)) : inSecond d = mk 1 d 1 := rfl

theorem inFirst_injective : Function.Injective inFirst := fun c d h => by
  simpa [inFirst_apply, mk_inj] using h

@[expose] def chi : Wr →* ℤˣ where
  toFun w := sign (w.left 1) * sign (w.left eps)
  map_one' := by simp
  map_mul' u w := by
    obtain ⟨a, b, p, rfl⟩ : ∃ a b p, u = mk a b p := ⟨_, _, _, (mk_eta u).symm⟩
    obtain ⟨c, d, q, rfl⟩ : ∃ c d q, w = mk c d q := ⟨_, _, _, (mk_eta w).symm⟩
    rcases eq_one_or_eps p with rfl | rfl
    · rw [mk_mul_one]
      simp only [mk_left_one, mk_left_eps, map_mul]
      ac_rfl
    · rw [mk_mul_eps]
      simp only [mk_left_one, mk_left_eps, map_mul]
      ac_rfl

theorem chi_mk (a b : Perm (Fin 5)) (q : Multiplicative (ZMod 2)) :
    chi (mk a b q) = sign a * sign b := by
  simp [chi]

@[expose] def swapEl : Wr := mk 1 1 eps

theorem swapEl_mul_self : swapEl * swapEl = 1 := by
  rw [swapEl, mk_mul_eps]
  simp [eps_mul_eps, mk_one_one_one]

theorem swapEl_inv : swapEl⁻¹ = swapEl := inv_eq_of_mul_eq_one_right swapEl_mul_self

theorem swapEl_conj (a b : Perm (Fin 5)) : swapEl * mk a b 1 * swapEl⁻¹ = mk b a 1 := by
  rw [swapEl_inv, swapEl, mk_mul_eps]
  simp only [one_mul, mul_one]
  rw [mk_mul_eps]
  simp [eps_mul_eps]

theorem chi_conj (w g : Wr) : chi (g * w * g⁻¹) = chi w := by
  rw [map_mul, map_mul, map_inv, mul_comm (chi g) (chi w), mul_assoc, mul_inv_cancel, mul_one]

end CFSG.EvenSporadicStandard.TwoHS.SignWr
