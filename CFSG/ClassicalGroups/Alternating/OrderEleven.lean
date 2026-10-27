module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.ClassicalGroups.Alternating

open Polynomial

section Eleven

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

private theorem natDegree_dvd_finrank_F2 [FiniteDimensional (ZMod 2) M]
    {P : (ZMod 2)[X]} (hP : Irreducible P) {T : Module.End (ZMod 2) M} (hT : aeval T P = 0) :
    P.natDegree ∣ Module.finrank (ZMod 2) M := by
  have : Fact (Irreducible P) := ⟨hP⟩
  let ψ : AdjoinRoot P →+* Module.End (ZMod 2) M :=
    Ideal.Quotient.lift (Ideal.span {P}) (aeval T).toRingHom (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hT])
  let _ : Module (AdjoinRoot P) M := Module.compHom M ψ
  have hψ : ∀ c : ZMod 2, ψ (algebraMap (ZMod 2) (AdjoinRoot P) c) = algebraMap _ _ c := by
    intro c
    change (aeval T) (C c) = _
    rw [aeval_C]
  have : IsScalarTower (ZMod 2) (AdjoinRoot P) M := by
    constructor
    intro c k m
    change ψ (c • k) m = c • ψ k m
    rw [Algebra.smul_def, map_mul, hψ]
    rfl
  have hpb := (AdjoinRoot.powerBasis hP.ne_zero).finrank
  rw [AdjoinRoot.powerBasis_dim] at hpb
  have : Module.Finite (AdjoinRoot P) M := Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  rw [← Module.finrank_mul_finrank (ZMod 2) (AdjoinRoot P) M, hpb]
  exact dvd_mul_right _ _

theorem irreducible_cyclotomic_eleven : Irreducible (cyclotomic 11 (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 11) (by norm_num)
    dvd_rfl ?_
  rw [natDegree_cyclotomic, show Nat.totient 11 = 10 by decide]
  symm
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨?_, ?_⟩
  · ext
    simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, Units.val_one]
    decide
  · intro m hm hm0
    interval_cases m <;>
      (intro h; have := congrArg Units.val h; simp at this <;> (revert this; decide))

theorem ten_dvd_finrank_of_sum_eq_zero [FiniteDimensional (ZMod 2) M]
    {T : Module.End (ZMod 2) M} (hS : ∑ i ∈ Finset.range 11, T ^ i = 0) :
    10 ∣ Module.finrank (ZMod 2) M := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hT : aeval T (cyclotomic 11 (ZMod 2)) = 0 := by
    rw [cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    exact hS
  have h := natDegree_dvd_finrank_F2 irreducible_cyclotomic_eleven hT
  rwa [natDegree_cyclotomic, show Nat.totient 11 = 10 by decide] at h

end Eleven

end CFSG.ClassicalGroups.Alternating
