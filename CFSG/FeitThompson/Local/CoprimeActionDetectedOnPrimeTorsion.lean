module

public import Mathlib.GroupTheory.PGroup
public import CFSG.FeitThompson.Local.FixedDisplacementSplittingCoprime

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Additive

variable {p n : ℕ} {B V : Type*} [Group B] [AddCommGroup V] [DistribMulAction B V] [Finite B]

theorem forall_smul_eq_of_forall_nsmul_eq_zero (hp : p.Prime) (hcard : Nat.card V = p ^ n)
    (hcop : (Nat.card B).Coprime p)
    (h : ∀ (b : B) (v : V), p • v = 0 → b • v = v) (b : B) (v : V) : b • v = v := by
  have hfin : Finite V :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero n hp.pos.ne')
  have hcop' : (Nat.card B).Coprime (Nat.card V) := by rw [hcard]; exact hcop.pow_right n
  have hDbot : ∀ d ∈ displacementAddSubgroup B V, d = 0 := by
    intro d hd
    by_contra hd0
    have hdvd : addOrderOf d ∣ p ^ n := hcard ▸ addOrderOf_dvd_natCard d
    obtain ⟨k, hkn, hkeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      refine ⟨k - 1, ?_⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [pow_zero] at hkeq
        exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 hkeq) hd0
      · omega
    have hpw : p • (p ^ j • d) = 0 := by
      rw [smul_smul, ← pow_succ', ← addOrderOf_dvd_iff_nsmul_eq_zero, hkeq]
    have hzero : (p ^ j) • d = 0 :=
      eq_zero_of_mem_displacementAddSubgroup_of_forall_smul_eq hcop'
        ((displacementAddSubgroup B V).nsmul_mem hd _) fun b => h b _ hpw
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hkeq,
      Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hzero
    omega
  obtain ⟨c, hc, d, hd, rfl⟩ := exists_add_eq_of_coprime hcop' v
  rw [hDbot d hd, add_zero]
  exact (FixedPoints.mem_addSubgroup B V c).1 hc b

theorem fixedPoints_addSubgroup_eq_top_of_forall_nsmul_eq_zero (hp : p.Prime)
    (hcard : Nat.card V = p ^ n) (hcop : (Nat.card B).Coprime p)
    (h : ∀ (b : B) (v : V), p • v = 0 → b • v = v) : FixedPoints.addSubgroup B V = ⊤ :=
  eq_top_iff.2 fun v _ => (FixedPoints.mem_addSubgroup B V v).2 fun b =>
    forall_smul_eq_of_forall_nsmul_eq_zero hp hcard hcop h b v

end Additive

section Transfer

variable {B P : Type*} [Group B] [CommGroup P] [MulDistribMulAction B P]

private instance additiveDistribMulAction : DistribMulAction B (Additive P) where
  smul b v := Additive.ofMul (b • Additive.toMul v)
  one_smul v := by
    change Additive.ofMul ((1 : B) • Additive.toMul v) = v
    rw [one_smul, ofMul_toMul]
  mul_smul x y v := by
    change Additive.ofMul ((x * y) • Additive.toMul v)
      = Additive.ofMul (x • Additive.toMul (Additive.ofMul (y • Additive.toMul v)))
    rw [mul_smul, toMul_ofMul]
  smul_zero b := by
    change Additive.ofMul (b • (1 : P)) = 0
    rw [smul_one, ofMul_one]
  smul_add b x y := by
    change Additive.ofMul (b • (Additive.toMul x * Additive.toMul y)) = _
    rw [smul_mul', ofMul_mul]
    rfl

private theorem smul_ofMul (b : B) (x : P) :
    b • Additive.ofMul x = Additive.ofMul (b • x) := (rfl)

end Transfer

section Multiplicative

variable {p : ℕ} {B P : Type*} [Group B] [CommGroup P] [Finite B] [Finite P]

theorem forall_smul_eq_of_forall_pow_eq_one [MulDistribMulAction B P] (hp : p.Prime)
    (hP : IsPGroup p P) (hcop : (Nat.card B).Coprime p)
    (h : ∀ (b : B) (x : P), x ^ p = 1 → b • x = x) (b : B) (x : P) : b • x = x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcard : Nat.card (Additive P) = p ^ n := by
    rw [← hn]; exact Nat.card_congr Additive.toMul
  have key : ∀ (b : B) (v : Additive P), b • v = v := by
    refine fun b v => forall_smul_eq_of_forall_nsmul_eq_zero hp hcard hcop ?_ b v
    intro b' v' hv'
    have hpow : Additive.toMul v' ^ p = 1 := by
      rw [← ofMul_eq_zero, ofMul_pow, ofMul_toMul, hv']
    rw [← ofMul_toMul v', smul_ofMul, h b' _ hpow]
  have hb := key b (Additive.ofMul x)
  rw [smul_ofMul] at hb
  exact Additive.ofMul.injective hb

theorem eq_one_of_forall_pow_eq_one (hp : p.Prime) (hP : IsPGroup p P)
    (hcop : (Nat.card B).Coprime p) (ρ : B →* MulAut P)
    (h : ∀ (b : B) (x : P), x ^ p = 1 → ρ b x = x) (b : B) : ρ b = 1 := by
  let _inst := MulDistribMulAction.compHom P ρ
  exact MulEquiv.ext (forall_smul_eq_of_forall_pow_eq_one hp hP hcop h b)

theorem eq_one_of_forall_pow_eq_one' (hp : p.Prime) (hP : IsPGroup p P)
    (hcop : (Nat.card B).Coprime p) (ρ : B →* MulAut P)
    (h : ∀ (b : B) (x : P), x ^ p = 1 → ρ b x = x) : ρ = 1 :=
  MonoidHom.ext fun b => eq_one_of_forall_pow_eq_one hp hP hcop ρ h b

theorem ker_eq_top_of_forall_pow_eq_one (hp : p.Prime) (hP : IsPGroup p P)
    (hcop : (Nat.card B).Coprime p) (ρ : B →* MulAut P)
    (h : ∀ (b : B) (x : P), x ^ p = 1 → ρ b x = x) : ρ.ker = ⊤ :=
  eq_top_iff.2 fun b _ => eq_one_of_forall_pow_eq_one hp hP hcop ρ h b

end Multiplicative

end CFSG.FeitThompson
