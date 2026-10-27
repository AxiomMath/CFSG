module

public import CFSG.Fischer.Classification.Recognition.PSU6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35L

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

theorem vec_add_self (z : Fin n → K) : z + z = 0 := by
  rw [← two_smul K z, two_eq_zero, zero_smul]

theorem exists_add_frob_eq {t : K} (ht : t = 0 ∨ t = 1) : ∃ c : K, c + frob c = t := by
  rcases ht with rfl | rfl
  · exact ⟨0, by rw [map_zero, add_zero]⟩
  · exact ⟨ω, omega_add_frob⟩

@[expose] noncomputable def invN (e : SUid frob n) (z : Fin n → K) : Fin n → K := e • z + z

theorem invN_apply (e : SUid frob n) (z : Fin n → K) : invN e z = e • z + z := rfl

theorem smul_eq_invN_add (e : SUid frob n) (z : Fin n → K) : e • z = invN e z + z := by
  rw [invN_apply, add_assoc, vec_add_self, add_zero]

theorem invN_add (e : SUid frob n) (a b : Fin n → K) :
    invN e (a + b) = invN e a + invN e b := by
  simp only [invN_apply, smul_add]
  abel

theorem invN_smul (e : SUid frob n) (c : K) (a : Fin n → K) : invN e (c • a) = c • invN e a := by
  simp only [invN_apply, smul_add, smul_comm e c a]

theorem invN_zero (e : SUid frob n) : invN e 0 = 0 := by
  rw [invN_apply, smul_zero, add_zero]

theorem invN_eq_zero_iff (e : SUid frob n) (z : Fin n → K) : invN e z = 0 ↔ e • z = z := by
  rw [invN_apply]
  constructor
  · intro h
    calc e • z = e • z + z + z := by rw [add_assoc, vec_add_self, add_zero]
      _ = z := by rw [h, zero_add]
  · intro h
    rw [h, vec_add_self]

section Invol

variable {e : SUid frob n} (he : e * e = 1)
include he

theorem smul_smul_self (z : Fin n → K) : e • e • z = z := by
  rw [← mul_smul, he, one_smul]

theorem invN_invN (z : Fin n → K) : invN e (invN e z) = 0 := by
  rw [show invN e z = e • z + z from rfl, invN_add, invN_apply, invN_apply, smul_smul_self he,
    show z + e • z + (e • z + z) = (z + z) + (e • z + e • z) by abel, vec_add_self,
    vec_add_self, add_zero]

theorem herm_invN_left (a b : Fin n → K) : herm frob (invN e a) b = herm frob a (invN e b) := by
  have h1 : herm frob (e • a) b = herm frob a (e • b) := by
    conv_lhs => rw [← smul_smul_self he b]
    rw [herm_smul_smul]
  rw [invN_apply, invN_apply, herm_add_left, herm_add_right, h1]

theorem herm_invN_invN (a b : Fin n → K) : herm frob (invN e a) (invN e b) = 0 := by
  rw [herm_invN_left he, invN_invN he, herm_zero_right]

theorem herm_invN_swap (a b : Fin n → K) :
    herm frob b (invN e a) = frob (herm frob a (invN e b)) := by
  rw [← herm_invN_left he, herm_conj frob frob_frob a (invN e b)]

theorem herm_invN_self (a : Fin n → K) :
    herm frob a (invN e a) = 0 ∨ herm frob a (invN e a) = 1 := by
  rw [← frob_eq_self_iff]
  exact (herm_invN_swap he a a).symm

theorem herm_invN_add_add (a b : Fin n → K) :
    herm frob (a + b) (invN e (a + b)) = herm frob a (invN e a) + herm frob b (invN e b) +
      (herm frob a (invN e b) + frob (herm frob a (invN e b))) := by
  rw [invN_add, herm_add_left, herm_add_right, herm_add_right, herm_invN_swap he a b]
  ring

theorem herm_invN_eq_zero_of_diag {a b : Fin n → K} (ha : herm frob a (invN e a) = 0)
    (hb : herm frob b (invN e b) = 0) (hab : herm frob (a + b) (invN e (a + b)) = 0)
    (habω : herm frob (a + ω • b) (invN e (a + ω • b)) = 0) :
    herm frob a (invN e b) = 0 := by
  have hbω : herm frob (ω • b) (invN e (ω • b)) = 0 := by
    rw [invN_smul, herm_smul_left, herm_smul_right, hb, mul_zero, mul_zero]
  rw [herm_invN_add_add he, ha, hb, zero_add, zero_add] at hab
  rw [herm_invN_add_add he, ha, hbω, zero_add, zero_add, invN_smul, herm_smul_right] at habω
  rcases (add_frob_eq_zero_iff _).1 hab with h0 | h1
  · exact h0
  · exfalso
    rw [h1, mul_one] at habω
    rcases (add_frob_eq_zero_iff ω).1 habω with h | h
    · exact omega_ne_zero h
    · exact omega_ne_one h

theorem invN_eq_zero_of_diag (h : ∀ a, herm frob a (invN e a) = 0) (b : Fin n → K) :
    invN e b = 0 := by
  refine eq_zero_of_herm frob fun a => ?_
  rw [herm_invN_left he]
  exact herm_invN_eq_zero_of_diag he (h b) (h a) (h _) (h _)

omit he in
theorem herm_invN_proj {q : Fin n → K} (hq : herm frob q (invN e q) = 1) (a : Fin n → K) :
    herm frob q (invN e (a + herm frob q (invN e a) • q)) = 0 := by
  rw [invN_add, invN_smul, herm_add_right, herm_smul_right, hq, mul_one, add_self_K]

theorem invN_eq_of_rank_one {q : Fin n → K} (hq : herm frob q (invN e q) = 1)
    (h : ∀ y, herm frob q (invN e y) = 0 → herm frob y (invN e y) = 0) (b : Fin n → K) :
    invN e b = herm frob (invN e q) b • invN e q := by
  have hperp : ∀ a b, herm frob q (invN e a) = 0 → herm frob q (invN e b) = 0 →
      herm frob a (invN e b) = 0 := by
    intro a b ha hb
    have hab : herm frob q (invN e (a + b)) = 0 := by rw [invN_add, herm_add_right, ha, hb,
      add_zero]
    have habω : herm frob q (invN e (a + ω • b)) = 0 := by
      rw [invN_add, invN_smul, herm_add_right, herm_smul_right, ha, hb, mul_zero, add_zero]
    exact herm_invN_eq_zero_of_diag he (h a ha) (h b hb) (h _ hab) (h _ habω)
  have hform : ∀ a, herm frob a (invN e b) =
      frob (herm frob q (invN e a)) * herm frob q (invN e b) := by
    intro a
    set c := herm frob q (invN e a) with hc
    set d := herm frob q (invN e b) with hd
    have ha' := herm_invN_proj hq a
    have hb' := herm_invN_proj hq b
    have h0 := hperp _ _ ha' hb'
    have h1 : herm frob (a + c • q) (invN e q) = 0 := by
      rw [herm_invN_swap he, ha', map_zero]
    have hea : a = (a + c • q) + c • q := by rw [add_assoc, vec_add_self, add_zero]
    have heb : b = (b + d • q) + d • q := by rw [add_assoc, vec_add_self, add_zero]
    conv_lhs => rw [hea, heb]
    rw [invN_add, invN_smul, herm_add_left, herm_add_right, herm_add_right, herm_smul_right,
      herm_smul_left, herm_smul_left, herm_smul_right, h0, h1, hb', hq]
    ring
  refine sub_eq_zero.1 (eq_zero_of_herm frob fun a => herm_eq_zero_comm frob frob_frob ?_)
  rw [herm_sub_right, hform a, herm_smul_right, herm_invN_left he q b,
    herm_invN_swap he q a]
  ring

theorem eq_tvU_of_rank_one {q : Fin n → K} (hq : herm frob q (invN e q) = 1)
    (h : ∀ y, herm frob q (invN e y) = 0 → herm frob y (invN e y) = 0) :
    invN e q ≠ 0 ∧ herm frob (invN e q) (invN e q) = 0 ∧ e = tvU (invN e q) := by
  have hp0 : invN e q ≠ 0 := by
    intro h0
    rw [h0, herm_zero_right] at hq
    exact zero_ne_one hq
  have hpp := herm_invN_invN he q q
  refine ⟨hp0, hpp, ext_smul _ fun b => ?_⟩
  rw [smul_eq_invN_add, invN_eq_of_rank_one he hq h b, tvU_smul hpp, add_comm]

theorem exists_frame {q₀ y₀ : Fin n → K} (hq : herm frob q₀ (invN e q₀) = 1)
    (hy : herm frob y₀ (invN e y₀) = 1) (hqy : herm frob q₀ (invN e y₀) = 0) :
    ∃ p x q y : Fin n → K, invN e p = 0 ∧ invN e x = 0 ∧ invN e q = p ∧ invN e y = x ∧
      herm frob p p = 0 ∧ herm frob x x = 0 ∧ herm frob q q = 0 ∧ herm frob y y = 0 ∧
      herm frob p x = 0 ∧ herm frob p q = 1 ∧ herm frob p y = 0 ∧ herm frob x q = 0 ∧
      herm frob x y = 1 ∧ herm frob q y = 0 := by
  set p := invN e q₀ with hp
  set x := invN e y₀ with hx
  have hNp : invN e p = 0 := invN_invN he q₀
  have hNx : invN e x = 0 := invN_invN he y₀
  have hpp : herm frob p p = 0 := herm_invN_invN he q₀ q₀
  have hxx : herm frob x x = 0 := herm_invN_invN he y₀ y₀
  have hpx : herm frob p x = 0 := herm_invN_invN he q₀ y₀
  have hxp : herm frob x p = 0 := herm_invN_invN he y₀ q₀
  have hpq₀ : herm frob p q₀ = 1 := by rw [hp, herm_invN_left he, hq]
  have hq₀p : herm frob q₀ p = 1 := hq
  have hpy₀ : herm frob p y₀ = 0 := by rw [hp, herm_invN_left he, hqy]
  have hy₀p : herm frob y₀ p = 0 := herm_eq_zero_comm frob frob_frob hpy₀
  have hxq₀ : herm frob x q₀ = 0 := by rw [hx, herm_invN_left he, herm_invN_swap he, hqy,
    map_zero]
  have hq₀x : herm frob q₀ x = 0 := herm_eq_zero_comm frob frob_frob hxq₀
  have hxy₀ : herm frob x y₀ = 1 := by rw [hx, herm_invN_left he, hy]
  have hy₀x : herm frob y₀ x = 1 := hy
  obtain ⟨c, hc⟩ :=
    exists_add_frob_eq ((frob_eq_self_iff _).1 (herm_self_fixed frob frob_frob q₀))
  obtain ⟨c', hc'⟩ :=
    exists_add_frob_eq ((frob_eq_self_iff _).1 (herm_self_fixed frob frob_frob y₀))
  set q := q₀ + c • p with hqdef
  set y₁ := y₀ + c' • x with hy₁
  set d := herm frob q y₁ with hd
  refine ⟨p, x, q, y₁ + d • p, hNp, hNx, ?_, ?_, hpp, hxx, ?_, ?_, hpx, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqdef, invN_add, invN_smul, hNp, smul_zero, add_zero]
  · rw [invN_add, invN_smul, hNp, smul_zero, add_zero, hy₁, invN_add, invN_smul, hNx,
      smul_zero, add_zero]
  · rw [hqdef]
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hpp, hpq₀, hq₀p,
      mul_zero, add_zero, mul_one]
    linear_combination hc + herm frob q₀ q₀ * two_eq_zero
  · rw [hy₁]
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hpp, hxx, hpx,
      hxp, hpy₀, hy₀p, hxy₀, hy₀x, mul_zero, add_zero, mul_one]
    linear_combination hc' + herm frob y₀ y₀ * two_eq_zero
  · rw [hqdef, herm_add_right, herm_smul_right, hpq₀, hpp, mul_zero, add_zero]
  · rw [hy₁]
    simp only [herm_add_right, herm_smul_right, hpy₀, hpx, hpp, mul_zero, add_zero]
  · rw [hqdef, herm_add_right, herm_smul_right, hxq₀, hxp, mul_zero, add_zero]
  · rw [hy₁]
    simp only [herm_add_right, herm_smul_right, hxy₀, hxx, hxp, mul_zero, add_zero]
  · have hqp : herm frob q p = 1 := by
      rw [hqdef, herm_add_left, herm_smul_left, hq₀p, hpp, mul_zero, add_zero]
    rw [herm_add_right, herm_smul_right, hqp, mul_one, ← hd, add_self_K]

end Invol

end CFSG.LargeExtraspecial.AS35L
