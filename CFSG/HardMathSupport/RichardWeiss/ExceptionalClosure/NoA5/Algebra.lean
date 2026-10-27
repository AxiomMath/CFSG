module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.NoA5

variable {S : Type*} [Group S]

theorem sq_comm {p q : S} (h : (p * q) ^ 2 = 1) : (q * p) ^ 2 = 1 := by
  simp only [pow_two] at h ⊢
  calc q * p * (q * p) = p⁻¹ * (p * q * (p * q)) * p := by group
    _ = 1 := by rw [h]; group

theorem sq_inv {p q : S} (h : (p * q) ^ 2 = 1) : (p⁻¹ * q⁻¹) ^ 2 = 1 := by
  have h2 := sq_comm h
  simp only [pow_two] at h2 ⊢
  calc p⁻¹ * q⁻¹ * (p⁻¹ * q⁻¹) = (q * p * (q * p))⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem inv_eq_sq_of_cube {x : S} (h : x ^ 3 = 1) : x⁻¹ = x * x := by
  rw [inv_eq_iff_mul_eq_one]
  rw [← pow_three]; exact h

theorem inv_mul_inv_of_cube {x : S} (h : x ^ 3 = 1) : x⁻¹ * x⁻¹ = x := by
  rw [inv_eq_sq_of_cube h]
  calc x * x * (x * x) = x ^ 3 * x := by rw [pow_three]; group
    _ = x := by rw [h]; group

theorem eq_inv_of_mul_self {t : S} (h : t * t = 1) : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one]; exact h

theorem l1_core {p t e : S} (hp : p ^ 3 = 1) (hq : (p * t) ^ 3 = 1) (ht : t * t = 1)
    (hte : (t * e) * (t * e) = 1) (hpe : p * e = e * p) (he3 : e ^ 3 = 1) : e = 1 := by
  have htinv : t⁻¹ = t := eq_inv_of_mul_self ht
  have hpe' : p⁻¹ * e = e * p⁻¹ := by
    calc p⁻¹ * e = p⁻¹ * (e * p) * p⁻¹ := by group
      _ = p⁻¹ * (p * e) * p⁻¹ := by rw [hpe]
      _ = e * p⁻¹ := by group
  have htet : t * e * t = e⁻¹ := by
    calc t * e * t = t * e * t * (e * e⁻¹) := by group
      _ = (t * e * (t * e)) * e⁻¹ := by group
      _ = e⁻¹ := by rw [hte]; group
  have h21 : (p * t * p⁻¹) * (p⁻¹ * t * p) * t = 1 := by
    calc (p * t * p⁻¹) * (p⁻¹ * t * p) * t = p * t * (p⁻¹ * p⁻¹) * t * p * t := by group
      _ = (p * t) * (p * t) * (p * t) := by rw [inv_mul_inv_of_cube hp]; group
      _ = 1 := by rw [← pow_three']; exact hq
  have hu1sq : (p⁻¹ * t * p) * (p⁻¹ * t * p) = 1 := by
    calc (p⁻¹ * t * p) * (p⁻¹ * t * p) = p⁻¹ * (t * t) * p := by group
      _ = 1 := by rw [ht]; group
  have hu2sq : (p * t * p⁻¹) * (p * t * p⁻¹) = 1 := by
    calc (p * t * p⁻¹) * (p * t * p⁻¹) = p * (t * t) * p⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hu1inv := eq_inv_of_mul_self hu1sq
  have hu2inv := eq_inv_of_mul_self hu2sq
  have htu : t = (p⁻¹ * t * p) * (p * t * p⁻¹) := by
    have : (p * t * p⁻¹) * (p⁻¹ * t * p) = t⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]; exact h21
    rw [htinv] at this
    calc t = ((p * t * p⁻¹) * (p⁻¹ * t * p))⁻¹ := by rw [this, htinv]
      _ = (p⁻¹ * t * p)⁻¹ * (p * t * p⁻¹)⁻¹ := by rw [mul_inv_rev]
      _ = (p⁻¹ * t * p) * (p * t * p⁻¹) := by rw [hu1inv, hu2inv]
  have hu1e : (p⁻¹ * t * p) * e * (p⁻¹ * t * p) = e⁻¹ := by
    calc (p⁻¹ * t * p) * e * (p⁻¹ * t * p) = p⁻¹ * t * (p * e * p⁻¹) * t * p := by group
      _ = p⁻¹ * t * (e * p * p⁻¹) * t * p := by rw [hpe]
      _ = p⁻¹ * (t * e * t) * p := by group
      _ = p⁻¹ * e⁻¹ * p := by rw [htet]
      _ = (p⁻¹ * e * p)⁻¹ := by group
      _ = e⁻¹ := by rw [hpe']; group
  have hu2e : (p * t * p⁻¹) * e * (p * t * p⁻¹) = e⁻¹ := by
    calc (p * t * p⁻¹) * e * (p * t * p⁻¹) = p * t * (p⁻¹ * e * p) * t * p⁻¹ := by group
      _ = p * t * (e * p⁻¹ * p) * t * p⁻¹ := by rw [hpe']
      _ = p * (t * e * t) * p⁻¹ := by group
      _ = p * e⁻¹ * p⁻¹ := by rw [htet]
      _ = (p * e * p⁻¹)⁻¹ := by group
      _ = e⁻¹ := by rw [hpe]; group
  have hte' : t * e * t = e := by
    calc t * e * t = t * e * t⁻¹ := by rw [htinv]
      _ = ((p⁻¹ * t * p) * (p * t * p⁻¹)) * e * ((p⁻¹ * t * p) * (p * t * p⁻¹))⁻¹ := by
          rw [← htu]
      _ = (p⁻¹ * t * p) * ((p * t * p⁻¹) * e * (p * t * p⁻¹)) * (p⁻¹ * t * p) := by
          rw [mul_inv_rev, hu1inv, hu2inv]; group
      _ = (p⁻¹ * t * p) * e⁻¹ * (p⁻¹ * t * p) := by rw [hu2e]
      _ = ((p⁻¹ * t * p) * e * (p⁻¹ * t * p))⁻¹ := by
          have key : ∀ u : S, u⁻¹ = u → u * e⁻¹ * u = (u * e * u)⁻¹ := fun u hu => by
            simp only [mul_inv_rev, hu, mul_assoc]
          exact key _ hu1inv
      _ = e := by rw [hu1e]; group
  have heinv : e = e⁻¹ := hte'.symm.trans htet
  have he2 : e * e = 1 := mul_eq_one_iff_eq_inv.mpr heinv
  calc e = e * e * e := by rw [he2]; group
    _ = e ^ 3 := by rw [pow_three']
    _ = 1 := he3

theorem l1 {p q r : S} (hp : p ^ 3 = 1) (hq : q ^ 3 = 1) (hr : r ^ 3 = 1)
    (h1 : (p⁻¹ * q) ^ 2 = 1) (h2 : (q⁻¹ * r) ^ 2 = 1) (hc : p * r = r * p) : p = r := by
  have hq' : q = p * (p⁻¹ * q) := by group
  have hr' : r = p * (p⁻¹ * r) := by group
  have ht2 : (p⁻¹ * q) * (p⁻¹ * q) = 1 := by rw [← pow_two]; exact h1
  have hpe : p * (p⁻¹ * r) = (p⁻¹ * r) * p := by
    calc p * (p⁻¹ * r) = r := by group
      _ = p⁻¹ * (p * r) := by group
      _ = p⁻¹ * (r * p) := by rw [hc]
      _ = (p⁻¹ * r) * p := by group
  have he3 : (p⁻¹ * r) ^ 3 = 1 := by
    have hcomm : Commute p⁻¹ r := (show Commute p r from hc).inv_left
    rw [hcomm.mul_pow, inv_pow, hp, inv_one, one_mul, hr]
  have hte : ((p⁻¹ * q) * (p⁻¹ * r)) * ((p⁻¹ * q) * (p⁻¹ * r)) = 1 := by
    have hh : q⁻¹ * r = (p⁻¹ * q) * (p⁻¹ * r) := by
      have := eq_inv_of_mul_self ht2
      calc q⁻¹ * r = (p⁻¹ * q)⁻¹ * (p⁻¹ * r) := by group
        _ = (p⁻¹ * q) * (p⁻¹ * r) := by rw [this]
    rw [← hh, ← pow_two]; exact h2
  have hq3 : (p * (p⁻¹ * q)) ^ 3 = 1 := by rw [← hq']; exact hq
  have he := l1_core hp hq3 ht2 hte hpe he3
  have : p⁻¹ * r = 1 := he
  calc p = p * (p⁻¹ * r) := by rw [this]; group
    _ = r := by group

theorem v_rel {p t : S} (hp : p ^ 3 = 1) (hq : (p * t) ^ 3 = 1) :
    (p * t * p⁻¹) * (p⁻¹ * t * p) * t = 1 := by
  calc (p * t * p⁻¹) * (p⁻¹ * t * p) * t = p * t * (p⁻¹ * p⁻¹) * t * p * t := by group
    _ = (p * t) * (p * t) * (p * t) := by rw [inv_mul_inv_of_cube hp]; group
    _ = 1 := by rw [← pow_three']; exact hq

theorem v_mul {p t : S} (ht : t * t = 1) (hp : p ^ 3 = 1) (hq : (p * t) ^ 3 = 1) :
    (p⁻¹ * t * p) * t = p * t * p⁻¹ := by
  have h := v_rel hp hq
  have htinv := eq_inv_of_mul_self ht
  calc (p⁻¹ * t * p) * t = ((p * t * p⁻¹)⁻¹ * ((p * t * p⁻¹) * (p⁻¹ * t * p) * t)) := by group
    _ = (p * t * p⁻¹)⁻¹ := by rw [h]; group
    _ = p * t * p⁻¹ := by
        have : (p * t * p⁻¹) * (p * t * p⁻¹) = 1 := by
          calc (p * t * p⁻¹) * (p * t * p⁻¹) = p * (t * t) * p⁻¹ := by group
            _ = 1 := by rw [ht]; group
        exact eq_inv_of_mul_self this

theorem comm_of_comm_conj {y g : S} (hg : g ^ 3 = 1) (h : (y⁻¹ * g) ^ 2 = 1)
    (hc : y * (g⁻¹ * y * g) = (g⁻¹ * y * g) * y) : y * g = g * y := by
  have hs2 : (y⁻¹ * g) * (y⁻¹ * g) = 1 := by rw [← pow_two]; exact h
  have hsinv := eq_inv_of_mul_self hs2
  have hg' : g = y * (y⁻¹ * g) := by group
  have hg3 : (y * (y⁻¹ * g)) * (y * (y⁻¹ * g)) * (y * (y⁻¹ * g)) = 1 := by
    rw [← hg', ← pow_three']; exact hg
  generalize y⁻¹ * g = s at hs2 hsinv hg' hg3 h
  subst hg'
  have hconj : (y * s)⁻¹ * y * (y * s) = s * y * s := by
    calc (y * s)⁻¹ * y * (y * s) = s⁻¹ * y * s := by group
      _ = s * y * s := by rw [hsinv]
  rw [hconj] at hc
  have h1 : y * s * y * s = s * y⁻¹ := by
    have h : y * s * y * s = (y * s)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc y * s * y * s * (y * s) = (y * s) * (y * s) * (y * s) := by group
        _ = 1 := hg3
    rw [h, mul_inv_rev, hsinv]
  have h2 : y * s * y = s * y⁻¹ * s := by
    have h : y * s * y = (s * y * s)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc y * s * y * (s * y * s) = (y * s) * (y * s) * (y * s) := by group
        _ = 1 := hg3
    rw [h]
    simp only [mul_inv_rev, hsinv, mul_assoc]
  have h3 : s * y⁻¹ = y⁻¹ * s := by
    calc s * y⁻¹ = y * s * y * s := h1.symm
      _ = s * y * s * y := by
          calc y * s * y * s = y * (s * y * s) := by group
            _ = (s * y * s) * y := hc
            _ = s * y * s * y := rfl
      _ = s * (y * s * y) := by group
      _ = s * (s * y⁻¹ * s) := by rw [h2]
      _ = y⁻¹ * s := by calc s * (s * y⁻¹ * s) = (s * s) * y⁻¹ * s := by group
          _ = y⁻¹ * s := by rw [hs2]; group
  have h4 : y * s = s * y := by
    calc y * s = y * (s * y⁻¹) * y := by group
      _ = y * (y⁻¹ * s) * y := by rw [h3]
      _ = s * y := by group
  calc y * (y * s) = y * (s * y) := by rw [h4]
    _ = (y * s) * y := by group

theorem conj_inv_shift {y g' : S} (h : (y⁻¹ * g') ^ 2 = 1) :
    g' * y * g'⁻¹ = y * (g'⁻¹ * y * g') * y⁻¹ := by
  have hs2 : (y⁻¹ * g') * (y⁻¹ * g') = 1 := by rw [← pow_two]; exact h
  have hsinv := eq_inv_of_mul_self hs2
  have hg' : g' = y * (y⁻¹ * g') := by group
  generalize y⁻¹ * g' = s at hs2 hsinv hg' h
  subst hg'
  calc y * s * y * (y * s)⁻¹ = y * s * y * (s⁻¹ * y⁻¹) := by group
    _ = y * s * y * (s * y⁻¹) := by rw [hsinv]
    _ = y * ((y * s)⁻¹ * y * (y * s)) * y⁻¹ := by
        calc y * s * y * (s * y⁻¹) = y * (s⁻¹ * y * s) * y⁻¹ := by rw [hsinv]; group
          _ = y * ((y * s)⁻¹ * y * (y * s)) * y⁻¹ := by group

theorem comm_of_comm_conj_inv {y g : S} (hg : g ^ 3 = 1) (h : (y⁻¹ * g⁻¹) ^ 2 = 1)
    (hc : y * (g⁻¹ * y * g) = (g⁻¹ * y * g) * y) : y * g = g * y := by
  have hg' : g⁻¹ ^ 3 = 1 := by rw [inv_pow, hg, inv_one]
  have hshift := conj_inv_shift h
  rw [inv_inv] at hshift
  set X : S := g * y * g⁻¹ with hX
  have hc' : y * X = X * y := by
    have h1 : y * (y * X * y⁻¹) = (y * X * y⁻¹) * y := by rw [← hshift]; exact hc
    calc y * X = y⁻¹ * (y * (y * X * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * X * y⁻¹) * y) * y := by rw [h1]
      _ = X * y := by group
  have := comm_of_comm_conj hg' h (by rw [inv_inv]; exact hc')
  have h2 : y * g⁻¹ = g⁻¹ * y := this
  calc y * g = g * (g⁻¹ * y) * g := by group
    _ = g * (y * g⁻¹) * g := by rw [h2]
    _ = g * y := by group

theorem sq_inv' {p q : S} (h : (p⁻¹ * q⁻¹) ^ 2 = 1) : (p * q) ^ 2 = 1 := by
  have := sq_inv h
  simpa using this

theorem comm_of_sq {s u : S} (hs : s * s = 1) (hu : u * u = 1) (h : (s * u) ^ 2 = 1) :
    s * u = u * s := by
  have hsi := eq_inv_of_mul_self hs
  have hui := eq_inv_of_mul_self hu
  have h' : (s * u) * (s * u) = 1 := by rw [← pow_two]; exact h
  calc s * u = (s * u)⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h'
    _ = u * s := by rw [mul_inv_rev, hsi, hui]

theorem t_eq_u1u2 {p t : S} (ht : t * t = 1) (hp : p ^ 3 = 1) (hq : (p * t) ^ 3 = 1) :
    t = (p⁻¹ * t * p) * (p * t * p⁻¹) := by
  have h21 := v_rel hp hq
  have htinv := eq_inv_of_mul_self ht
  have hu1sq : (p⁻¹ * t * p) * (p⁻¹ * t * p) = 1 := by
    calc (p⁻¹ * t * p) * (p⁻¹ * t * p) = p⁻¹ * (t * t) * p := by group
      _ = 1 := by rw [ht]; group
  have hu2sq : (p * t * p⁻¹) * (p * t * p⁻¹) = 1 := by
    calc (p * t * p⁻¹) * (p * t * p⁻¹) = p * (t * t) * p⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hu1inv := eq_inv_of_mul_self hu1sq
  have hu2inv := eq_inv_of_mul_self hu2sq
  have : (p * t * p⁻¹) * (p⁻¹ * t * p) = t⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]; exact h21
  rw [htinv] at this
  calc t = ((p * t * p⁻¹) * (p⁻¹ * t * p))⁻¹ := by rw [this, htinv]
    _ = (p⁻¹ * t * p)⁻¹ * (p * t * p⁻¹)⁻¹ := by rw [mul_inv_rev]
    _ = (p⁻¹ * t * p) * (p * t * p⁻¹) := by rw [hu1inv, hu2inv]

theorem l5_core {p t s : S} (hp : p ^ 3 = 1) (ht : t * t = 1) (hs : s * s = 1)
    (hq : (p * t) ^ 3 = 1) (h1 : (s * (p⁻¹ * t * p)) ^ 2 = 1)
    (h2 : (s * (p * t * p⁻¹)) ^ 2 = 1) : s * t = t * s := by
  have hu1sq : (p⁻¹ * t * p) * (p⁻¹ * t * p) = 1 := by
    calc (p⁻¹ * t * p) * (p⁻¹ * t * p) = p⁻¹ * (t * t) * p := by group
      _ = 1 := by rw [ht]; group
  have hu2sq : (p * t * p⁻¹) * (p * t * p⁻¹) = 1 := by
    calc (p * t * p⁻¹) * (p * t * p⁻¹) = p * (t * t) * p⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have c1 := comm_of_sq hs hu1sq h1
  have c2 := comm_of_sq hs hu2sq h2
  have htu := t_eq_u1u2 ht hp hq
  calc s * t = s * ((p⁻¹ * t * p) * (p * t * p⁻¹)) := by rw [← htu]
    _ = (s * (p⁻¹ * t * p)) * (p * t * p⁻¹) := by group
    _ = ((p⁻¹ * t * p) * s) * (p * t * p⁻¹) := by rw [c1]
    _ = (p⁻¹ * t * p) * (s * (p * t * p⁻¹)) := by group
    _ = (p⁻¹ * t * p) * ((p * t * p⁻¹) * s) := by rw [c2]
    _ = ((p⁻¹ * t * p) * (p * t * p⁻¹)) * s := by group
    _ = t * s := by rw [← htu]

theorem conj_sq {p q : S} (hp : p ^ 3 = 1) (hq : q ^ 3 = 1) (h : (p⁻¹ * q) ^ 2 = 1) :
    (p⁻¹ * (q⁻¹ * p * q)) ^ 2 = 1 := by
  have ht : (p⁻¹ * q) * (p⁻¹ * q) = 1 := by rw [← pow_two]; exact h
  have hq' : (p * (p⁻¹ * q)) ^ 3 = 1 := by
    have : p * (p⁻¹ * q) = q := by group
    rw [this]; exact hq
  have hv := v_mul ht hp hq'
  have hq'' : q = p * (p⁻¹ * q) := by group
  generalize p⁻¹ * q = t at ht hv hq'' h
  subst hq''
  have e : p⁻¹ * ((p * t)⁻¹ * p * (p * t)) = (p⁻¹ * t * p) * t := by
    have htinv := eq_inv_of_mul_self ht
    calc p⁻¹ * ((p * t)⁻¹ * p * (p * t)) = p⁻¹ * (t⁻¹ * p⁻¹ * p * (p * t)) := by group
      _ = p⁻¹ * (t * p * t) := by rw [htinv]; group
      _ = (p⁻¹ * t * p) * t := by group
  rw [e, hv]
  calc (p * t * p⁻¹) ^ 2 = p * (t * t) * p⁻¹ := by simp only [pow_two]; group
    _ = 1 := by rw [ht]; group

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.NoA5
