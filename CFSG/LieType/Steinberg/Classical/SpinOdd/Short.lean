module

public import CFSG.LieType.Steinberg.Classical.SpinFrame.Basic

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame CliffordAlgebra QuadraticMap

section Vectors

variable {n : ℕ}

@[expose] def IsShort (e : Fin n → ℤ) : Prop :=
  ∃ (i : Fin n) (s : Bool), e = Pi.single i (boolSign s)

theorem isShort_single (i : Fin n) (s : Bool) :
    IsShort (Pi.single i (boolSign s) : Fin n → ℤ) :=
  ⟨i, s, rfl⟩

theorem IsShort.not_isLong {e : Fin n → ℤ} (he : IsShort e) : ¬IsLong e := by
  obtain ⟨k, u, rfl⟩ := he
  rintro ⟨i, j, hij, s, t, h⟩
  exact single_ne_single_add_single hij (boolSign_ne_zero s) (boolSign_ne_zero t) h

theorem eq_of_single_eq_single {i i' : Fin n} {s s' : Bool}
    (h : (Pi.single i (boolSign s) : Fin n → ℤ) = Pi.single i' (boolSign s')) :
    i = i' ∧ s = s' := by
  obtain ⟨h1, h2⟩ := (single_eq_single_iff' (boolSign_ne_zero s)).mp h
  exact ⟨h1, boolSign_injective h2⟩

end Vectors

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : OddFrame Q n)

open _root_.Classical in
@[expose] def shortElt (e : Fin n → ℤ) (c : K) : spinGroup Q :=
  if h : ∃ p : Fin n × Bool, e = Pi.single p.1 (boolSign p.2) then
    F.shortRoot h.choose.1 h.choose.2 (.ofAdd ((boolSign h.choose.2 : K) * c))
  else 1

theorem shortElt_eq {e : Fin n → ℤ} {i : Fin n} {s : Bool} (he : e = Pi.single i (boolSign s))
    (c : K) : shortElt F e c = F.shortRoot i s (.ofAdd ((boolSign s : K) * c)) := by
  have hex : ∃ p : Fin n × Bool, e = Pi.single p.1 (boolSign p.2) := ⟨(i, s), he⟩
  rw [shortElt, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := eq_of_single_eq_single (hex.choose_spec.symm.trans he)
  rw [h1, h2]

theorem shortRoot_eq_shortElt {e : Fin n → ℤ} {i : Fin n} {s : Bool}
    (he : e = Pi.single i (boolSign s)) (c : K) :
    F.shortRoot i s (.ofAdd c) = shortElt F e ((boolSign s : K) * c) := by
  rw [shortElt_eq F he, ← mul_assoc,
    intCast_mul_self_of_sq (boolSign_eq_one_or_eq_neg_one s), one_mul]

theorem shortElt_of_not {e : Fin n → ℤ} (he : ¬IsShort e) (c : K) : shortElt F e c = 1 := by
  rw [shortElt, dite_eq_right fun ⟨p, hp⟩ => he ⟨p.1, p.2, hp⟩]

theorem shortElt_zero (e : Fin n → ℤ) : shortElt F e (0 : K) = 1 := by
  by_cases he : IsShort e
  · obtain ⟨i, s, he⟩ := he
    rw [shortElt_eq F he, mul_zero, ofAdd_zero, map_one]
  · exact shortElt_of_not F he 0

theorem shortElt_add (e : Fin n → ℤ) (c d : K) :
    shortElt F e (c + d) = shortElt F e c * shortElt F e d := by
  by_cases he : IsShort e
  · obtain ⟨i, s, he⟩ := he
    rw [shortElt_eq F he, shortElt_eq F he, shortElt_eq F he, ← map_mul, ← ofAdd_add, mul_add]
  · rw [shortElt_of_not F he, shortElt_of_not F he, shortElt_of_not F he, mul_one]

theorem shortElt_neg (e : Fin n → ℤ) (c : K) : shortElt F e (-c) = (shortElt F e c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← shortElt_add, neg_add_cancel, shortElt_zero]

theorem shortElt_injective {e : Fin n → ℤ} (he : IsShort e) :
    Function.Injective (shortElt F e : K → spinGroup Q) := by
  obtain ⟨i, s, he⟩ := he
  intro c d h
  rw [shortElt_eq F he, shortElt_eq F he] at h
  have h' := congrArg Multiplicative.toAdd (F.shortRoot_injective i s h)
  simp only [toAdd_ofAdd] at h'
  exact mul_left_cancel₀ (intCast_ne_zero_of_sq (boolSign_eq_one_or_eq_neg_one s)) h'

theorem exists_shortElt_eq_iff {e : Fin n → ℤ} {i : Fin n} {s : Bool}
    (he : e = Pi.single i (boolSign s)) (g : spinGroup Q) :
    g ∈ (F.shortRoot i s).range ↔ ∃ c : K, shortElt F e c = g := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(boolSign s : K) * Multiplicative.toAdd c, by
      rw [← shortRoot_eq_shortElt F he, ofAdd_toAdd]⟩
  · rintro ⟨c, rfl⟩
    rw [shortElt_eq F he]
    exact ⟨_, rfl⟩

theorem conj_shortElt (g : spinGroup Q) {e e' : Fin n → ℤ} {i i' : Fin n} {s s' : Bool}
    (he : e = Pi.single i (boolSign s)) (he' : e' = Pi.single i' (boolSign s')) {μ l : K}
    (hz : spinAction Q g F.z = μ • F.z)
    (hi : spinAction Q g (F.vec i s) = l • F.vec i' s') (c : K) :
    g * shortElt F e c * g⁻¹ =
      shortElt F e' ((boolSign s : K) * boolSign s' * μ * l * c) := by
  rw [shortElt_eq F he, F.conj_shortRoot g i s i' s' hz hi, shortRoot_eq_shortElt F he']
  ring_nf

end CFSG.LieType.Steinberg.SpinOdd
