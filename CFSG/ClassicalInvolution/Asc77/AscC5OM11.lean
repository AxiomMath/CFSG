module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

variable {F : Type} [Field F] [Finite F]

theorem exists_ringEquiv_eq_pow_half {p : ℕ} [Fact p.Prime] [CharP F p] (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x) (hσ1 : ∃ x, σ x ≠ x) :
    ∃ i : ℕ, Nat.card F = (p ^ i) ^ 2 ∧ ∀ x : F, σ x = x ^ (p ^ i) := by
  classical
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Fintype F := Fintype.ofFinite F
  let σAlg : F ≃ₐ[ZMod p] F := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : (σ.toRingHom.comp (algebraMap (ZMod p) F) : ZMod p →+* F) =
        algebraMap (ZMod p) F := RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  set fr := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F with hfr
  obtain ⟨⟨i, hi⟩, hσ⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σAlg
  have hσx : ∀ x : F, σ x = x ^ (p ^ i) := by
    intro x
    have hσx := DFunLike.congr_fun hσ x
    calc σ x = σAlg x := rfl
      _ = (fr ^ i) x := hσx.symm
      _ = ((⇑fr)^[i]) x := by rw [AlgEquiv.coe_pow]
      _ = x ^ (Fintype.card (ZMod p) ^ i) :=
        congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod p) F i) x
      _ = x ^ (p ^ i) := by rw [ZMod.card]
  have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) F
  set n := Module.finrank (ZMod p) F with hn
  have hσ' : fr ^ i = σAlg := hσ
  have hsq : fr ^ (2 * i) = 1 := by
    rw [pow_mul', hσ']
    ext x
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact hσ2 x
  have hdvd : n ∣ 2 * i := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hsq
  have hi0 : i ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hσ1
    apply hx
    rw [hσx x, pow_zero, pow_one]
  have h2i : 2 * i = n := by
    obtain ⟨c, hc⟩ := hdvd
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  refine ⟨i, ?_, hσx⟩
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, ← hn,
    ← h2i, pow_mul, ← pow_mul, mul_comm, pow_mul]

theorem isSquare_of_mul_ringEquiv {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x) (hσ1 : ∃ x, σ x ≠ x) {m a : F} (hm : m ≠ 0) (ha : σ a = a)
    (hma : m * σ m = a * a) : IsSquare m := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨i, hcard, hσx⟩ := exists_ringEquiv_eq_pow_half σ hσ2 hσ1
  have hchar : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : m * σ m = 0 := by rw [hma, mul_zero]
    rcases mul_eq_zero.mp h0 with h | h
    · exact hm h
    · exact hm ((map_eq_zero_iff σ σ.injective).mp h)
  rw [FiniteField.isSquare_iff hchar hm]
  set q₀ := p ^ i with hq₀
  have hq₀odd : Odd q₀ := ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  obtain ⟨r, hr⟩ := hq₀odd
  have hcard' : Fintype.card F / 2 = (q₀ + 1) * r := by
    rw [← Nat.card_eq_fintype_card, hcard, hr]
    have : (2 * r + 1) ^ 2 = 2 * ((2 * r + 1 + 1) * r) + 1 := by ring
    rw [this]
    omega
  have haq : a ^ q₀ = a := by rw [← hσx a, ha]
  have ha2r : a ^ (2 * r) = 1 := by
    have h1 : a ^ (2 * r) * a = a := by rw [← pow_succ, ← hr, haq]
    calc a ^ (2 * r) = a ^ (2 * r) * a * a⁻¹ := by field_simp
      _ = 1 := by rw [h1, mul_inv_cancel₀ ha0]
  rw [hcard', pow_mul, pow_succ, ← hσx m, mul_comm, hma, ← sq, ← pow_mul, ha2r]

end CFSG.ClassicalInvolution.Asc77.C5O.M
