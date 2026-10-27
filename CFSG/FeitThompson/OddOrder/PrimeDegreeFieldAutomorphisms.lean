module

public import Mathlib.Order.Interval.Set.Nat
public import CFSG.FeitThompson.Foundations.FrobeniusNormPrimeDegree
public import CFSG.FeitThompson.OddOrder.FiniteFieldAutomorphismBound

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p q : ℕ} {F : Type*} [Field F]

theorem ringEquiv_pow_apply_of_apply_eq {σ : F ≃+* F} {x : F} (hx : σ x = x) (n : ℕ) :
    (σ ^ n) x = x := by
  have h : (σ ^ n) x = σ^[n] x := by rw [RingAut.coe_pow]
  rw [h]
  exact Function.IsFixedPt.iterate hx n

section
variable (p q F) [Fact p.Prime] [Finite F] [CharP F p]

theorem orderOf_frobeniusEquiv_eq_of_prime (hq : q.Prime) (hF : Nat.card F = p ^ q) :
    orderOf (frobeniusEquiv F p) = q := by
  have hp : p.Prime := Fact.out
  have hdvd : orderOf (frobeniusEquiv F p) ∣ q :=
    orderOf_dvd_of_pow_eq_one (frobeniusEquiv_pow_eq_one p F hF)
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
  · exfalso
    have h1 : frobeniusEquiv F p = 1 := orderOf_eq_one_iff.mp h
    have hall : ∀ x : F, x ∈ (⊥ : Subfield F) := by
      intro x
      rw [← frobeniusEquiv_eq_self_iff_mem_bot p F, h1]
      rfl
    have hbij : Function.Bijective (Subtype.val : (⊥ : Subfield F) → F) :=
      ⟨Subtype.val_injective, fun x => ⟨⟨x, hall x⟩, rfl⟩⟩
    have h2 : Nat.card (⊥ : Subfield F) = Nat.card F := Nat.card_eq_of_bijective _ hbij
    rw [Subfield.card_bot F p, hF] at h2
    exact hq.one_lt.ne' (Nat.pow_right_injective hp.two_le (by simpa using h2)).symm
  · exact h

theorem setOf_ringEquiv_fixing_bot_eq_image (hq : q.Prime) (hF : Nat.card F = p ^ q) :
    {σ : F ≃+* F | ∀ x ∈ (⊥ : Subfield F), σ x = x}
      = (frobeniusEquiv F p ^ ·) '' Set.Iio q := by
  have hp : p.Prime := Fact.out
  have hsub : (frobeniusEquiv F p ^ ·) '' Set.Iio q
      ⊆ {σ : F ≃+* F | ∀ x ∈ (⊥ : Subfield F), σ x = x} := by
    rintro σ ⟨i, -, rfl⟩ x hx
    exact ringEquiv_pow_apply_of_apply_eq ((frobeniusEquiv_eq_self_iff_mem_bot p F).2 hx) i
  have hinj : Set.InjOn (frobeniusEquiv F p ^ ·) (Set.Iio q) := by
    rw [← orderOf_frobeniusEquiv_eq_of_prime p q F hq hF]
    exact pow_injOn_Iio_orderOf
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ ?_).symm
  · rw [hinj.ncard_image, Set.ncard_Iio_nat]
    exact ncard_setOf_ringEquiv_fixing_le hp ⊥ hF (Subfield.card_bot F p)
  · have : Finite (F ≃+* F) := finite_ringEquiv_of_finite F
    exact Set.toFinite _

theorem ringEquiv_fixing_bot_iff_eq_frobeniusEquiv_pow (hq : q.Prime) (hF : Nat.card F = p ^ q)
    {σ : F ≃+* F} :
    (∀ x ∈ (⊥ : Subfield F), σ x = x) ↔ ∃ i < q, σ = frobeniusEquiv F p ^ i := by
  have h := setOf_ringEquiv_fixing_bot_eq_image p q F hq hF
  constructor
  · intro hσ
    obtain ⟨i, hi, rfl⟩ := h ▸ (show σ ∈ {σ : F ≃+* F | ∀ x ∈ (⊥ : Subfield F), σ x = x} from hσ)
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact (h.ge ⟨i, hi, rfl⟩ : _)

theorem fixedPoints_frobeniusEquiv_pow_eq_bot (hq : q.Prime) (hF : Nat.card F = p ^ q)
    {i : ℕ} (hi : i ≠ 0) (hiq : i < q) :
    Function.fixedPoints (frobeniusEquiv F p ^ i) = ((⊥ : Subfield F) : Set F) := by
  have hord : orderOf (frobeniusEquiv F p) = q := orderOf_frobeniusEquiv_eq_of_prime p q F hq hF
  have hndvd : ¬ q ∣ i := fun h =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h) (not_le.2 hiq)
  have hcop : Nat.Coprime i q := ((hq.coprime_iff_not_dvd).2 hndvd).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq.one_lt
  have hpow : (frobeniusEquiv F p ^ i) ^ m = frobeniusEquiv F p := by
    rw [← pow_mul, ← pow_mod_orderOf, hord, hm, pow_one]
  have key : ∀ x : F, (frobeniusEquiv F p ^ i) x = x → frobeniusEquiv F p x = x := by
    intro x hx
    have h2 := ringEquiv_pow_apply_of_apply_eq hx m
    rwa [hpow] at h2
  ext x
  exact ⟨fun hx => (frobeniusEquiv_eq_self_iff_mem_bot p F).1 (key x hx),
    fun hx => ringEquiv_pow_apply_of_apply_eq ((frobeniusEquiv_eq_self_iff_mem_bot p F).2 hx) i⟩

theorem fixedPoints_eq_bot_of_ne_one (hq : q.Prime) (hF : Nat.card F = p ^ q)
    {σ : F ≃+* F} (hfix : ∀ x ∈ (⊥ : Subfield F), σ x = x) (hσ : σ ≠ 1) :
    Function.fixedPoints σ = ((⊥ : Subfield F) : Set F) := by
  obtain ⟨i, hiq, rfl⟩ := (ringEquiv_fixing_bot_iff_eq_frobeniusEquiv_pow p q F hq hF).1 hfix
  refine fixedPoints_frobeniusEquiv_pow_eq_bot p q F hq hF (fun h => ?_) hiq
  exact hσ (by rw [h, pow_zero])

end

variable (p q F)

theorem frobenius_generates_automorphisms_of_natCard_eq_prime_pow
    (hp : p.Prime) (hq : q.Prime) (hF : Nat.card F = p ^ q) :
    ∃ σ : F ≃+* F, (∀ x : F, σ x = x ^ p) ∧ orderOf σ = q ∧
      {τ : F ≃+* F | ∀ x ∈ (⊥ : Subfield F), τ x = x} = (σ ^ ·) '' Set.Iio q ∧
      ∀ τ : F ≃+* F, (∀ x ∈ (⊥ : Subfield F), τ x = x) → τ ≠ 1 →
        Function.fixedPoints τ = ((⊥ : Subfield F) : Set F) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp hF
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hF
  exact ⟨frobeniusEquiv F p, frobeniusEquiv_def F p,
    orderOf_frobeniusEquiv_eq_of_prime p q F hq hF,
    setOf_ringEquiv_fixing_bot_eq_image p q F hq hF,
    fun τ hτ hτ1 => fixedPoints_eq_bot_of_ne_one p q F hq hF hτ hτ1⟩

end

end CFSG.FeitThompson
