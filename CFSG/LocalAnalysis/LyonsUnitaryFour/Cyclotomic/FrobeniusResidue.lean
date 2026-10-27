module

public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers IntermediateField Polynomial

theorem exists_frobenius_exponent {p a M : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ∃ k : ℕ, k.Coprime (p ^ a * M) ∧ k ≡ 1 [MOD p ^ a] ∧ k ≡ p [MOD M] := by
  have hcop : (p ^ a).Coprime M :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
  let k := Nat.chineseRemainder hcop 1 p
  have h1 : (k : ℕ) ≡ 1 [MOD p ^ a] := k.2.1
  have h2 : (k : ℕ) ≡ p [MOD M] := k.2.2
  refine ⟨k, ?_, h1, h2⟩
  apply Nat.Coprime.mul_right
  · rw [Nat.Coprime, h1.gcd_eq, Nat.gcd_one_left]
  · rw [Nat.Coprime, h2.gcd_eq]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM

theorem isCyclotomicExtension_adjoin_primitiveRoot {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := by
  have hζalg : IsAlgebraic ℚ ζ := by
    refine ⟨cyclotomic N ℚ, cyclotomic_ne_zero N ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]
    exact hζ
  change IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯.toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
  exact hζ.adjoin_isCyclotomicExtension ℚ

theorem isPrimitiveRoot_adjoinSimple_gen {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    IsPrimitiveRoot (AdjoinSimple.gen ℚ ζ) N :=
  IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ

theorem exists_galois_gen_eq_pow {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {k : ℕ}
    (hk : k.Coprime N) :
    ∃ σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯, σ (AdjoinSimple.gen ℚ ζ) = AdjoinSimple.gen ℚ ζ ^ k := by
  have : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := isCyclotomicExtension_adjoin_primitiveRoot hζ
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod N ℚ⟮ζ⟯).symm (ZMod.unitOfCoprime k hk)
  refine ⟨σ, ?_⟩
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N ℚ⟮ζ⟯ σ
    (isPrimitiveRoot_adjoinSimple_gen hζ).pow_eq_one]
  simp only [σ, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime]
  rw [ZMod.val_natCast, (isPrimitiveRoot_adjoinSimple_gen hζ).eq_orderOf, pow_mod_orderOf]

theorem map_aeval_int {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) (x : A) (f : ℤ[X]) :
    φ (aeval x f) = aeval (φ x) f :=
  (aeval_algHom_apply φ.toIntAlgHom x f).symm

theorem exists_intPoly_eq_of_isIntegral {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {x : ℚ⟮ζ⟯} (hx : IsIntegral ℤ x) : ∃ f : ℤ[X], aeval (AdjoinSimple.gen ℚ ζ) f = x := by
  have : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := isCyclotomicExtension_adjoin_primitiveRoot hζ
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton
    (isPrimitiveRoot_adjoinSimple_gen hζ)
  obtain ⟨y, rfl⟩ := hcl.isIntegral_iff.mp hx
  have hy : (y : ℚ⟮ζ⟯) ∈ (aeval (R := ℤ) (AdjoinSimple.gen ℚ ζ)).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact y.2
  obtain ⟨f, hf⟩ := hy
  exact ⟨f, hf⟩

theorem pow_eq_pow_of_modEq {R : Type*} [Monoid R] {w : R} {M k l : ℕ} (hw : w ^ M = 1)
    (h : k ≡ l [MOD M]) : w ^ k = w ^ l := by
  rw [← Nat.mod_add_div k M, ← Nat.mod_add_div l M, pow_add, pow_add, pow_mul, pow_mul, hw,
    one_pow, one_pow, show k % M = l % M from h]

theorem aeval_pow_sub_pow_mem (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] {a M k : ℕ}
    (z : ComplexAlgebraicIntegers) (hz : z ^ (p ^ a * M) = 1) (hk : k ≡ p [MOD M]) (f : ℤ[X]) :
    aeval (z ^ k) f - (aeval z f) ^ p ∈ ideal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
  set w := Ideal.Quotient.mk ideal z with hwdef
  have hw : w ^ M = 1 := by
    have := prime_power_root_residue_one ideal p (z ^ M) a (by rw [← pow_mul, mul_comm, hz])
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, map_pow] at this
    exact this
  rw [map_aeval_int, map_aeval_int, map_pow, ← hwdef, pow_eq_pow_of_modEq hw hk]
  have := map_aeval_int (frobenius (ComplexAlgebraicIntegers ⧸ ideal) p) w f
  simpa [frobenius_def] using this.symm

section Frobenius

variable {p a M N k : ℕ} {ζ : ℂ}

theorem galois_gen_eq_pow_of_coe {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) :
    σ (AdjoinSimple.gen ℚ ζ) = AdjoinSimple.gen ℚ ζ ^ k :=
  Subtype.ext (by simpa using hσ)

theorem galois_apply_of_pow_eq_one [NeZero N] (hζ : IsPrimitiveRoot ζ N)
    {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯} (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {ξ : ℚ⟮ζ⟯}
    (hξ : ξ ^ N = 1) : σ ξ = ξ ^ k := by
  obtain ⟨i, -, rfl⟩ := (isPrimitiveRoot_adjoinSimple_gen hζ).eq_pow_of_pow_eq_one hξ
  rw [map_pow, galois_gen_eq_pow_of_coe hσ, ← pow_mul, ← pow_mul, mul_comm]

theorem cyclotomic_frobenius_exists (hp : p.Prime) (hN : N = p ^ a * M) (hpM : ¬ p ∣ M)
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ N) :
    ∃ k : ℕ, k.Coprime N ∧ k ≡ 1 [MOD p ^ a] ∧ k ≡ p [MOD M] ∧
      ∃ σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯, (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k := by
  have : NeZero N := ⟨by rw [hN]; exact (Nat.mul_pos (pow_pos hp.pos a) hM).ne'⟩
  obtain ⟨k, hk, hk1, hkp⟩ := exists_frobenius_exponent (a := a) hp hpM
  rw [← hN] at hk
  obtain ⟨σ, hσ⟩ := exists_galois_gen_eq_pow hζ hk
  exact ⟨k, hk, hk1, hkp, σ, by rw [hσ]; simp⟩

theorem cyclotomic_frobenius_fix_prime_power_root (hp : p.Prime) (hN : N = p ^ a * M)
    (hpM : ¬ p ∣ M) (hM : 0 < M) (hζ : IsPrimitiveRoot ζ N) (hk1 : k ≡ 1 [MOD p ^ a])
    {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯} (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {ξ : ℚ⟮ζ⟯} {j : ℕ}
    (hξj : ξ ^ (p ^ j) = 1) (hξ : ξ ^ N = 1) : σ ξ = ξ := by
  have : NeZero N := ⟨by rw [hN]; exact (Nat.mul_pos (pow_pos hp.pos a) hM).ne'⟩
  rw [galois_apply_of_pow_eq_one hζ hσ hξ]
  have h1 : orderOf ξ ∣ p ^ j := orderOf_dvd_of_pow_eq_one hξj
  have h2 : orderOf ξ ∣ N := orderOf_dvd_of_pow_eq_one hξ
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp h1
  have h3 : orderOf ξ ∣ p ^ a := by
    rw [hi] at h2 ⊢
    rw [hN] at h2
    exact (Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)).dvd_of_dvd_mul_right
      h2
  have hξa : ξ ^ (p ^ a) = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
  simpa using pow_eq_pow_of_modEq hξa hk1

theorem cyclotomic_frobenius_apply_coprime_root (hp : p.Prime) (hN : N = p ^ a * M)
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ N) (hkp : k ≡ p [MOD M]) {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {ξ : ℚ⟮ζ⟯} (hξ : ξ ^ M = 1) :
    σ ξ = ξ ^ p := by
  have : NeZero N := ⟨by rw [hN]; exact (Nat.mul_pos (pow_pos hp.pos a) hM).ne'⟩
  have hξN : ξ ^ N = 1 := by rw [hN, mul_comm, pow_mul, hξ, one_pow]
  rw [galois_apply_of_pow_eq_one hζ hσ hξN, pow_eq_pow_of_modEq hξ hkp]

theorem isIntegral_coe_adjoin_iff {x : ℚ⟮ζ⟯} : IsIntegral ℤ (x : ℂ) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff ((ℚ⟮ζ⟯).val.toRingHom.toIntAlgHom) Subtype.val_injective

theorem galois_isIntegral_iff (σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯) {x : ℚ⟮ζ⟯} :
    IsIntegral ℤ (σ x : ℂ) ↔ IsIntegral ℤ (x : ℂ) := by
  have key : ∀ (τ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯) (y : ℚ⟮ζ⟯), IsIntegral ℤ (y : ℂ) →
      IsIntegral ℤ (τ y : ℂ) := by
    intro τ y hy
    rw [isIntegral_coe_adjoin_iff] at hy ⊢
    exact hy.map τ.toRingHom.toIntAlgHom
  exact ⟨fun h => by simpa using key σ.symm _ h, key σ x⟩

theorem cyclotomic_frobenius_sub_pow_mem (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (hp : p.Prime) [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hN : N = p ^ a * M) (hM : 0 < M) (hζ : IsPrimitiveRoot ζ N) (hkp : k ≡ p [MOD M])
    {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯} (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {x : ℚ⟮ζ⟯}
    {α β : ComplexAlgebraicIntegers} (hα : (α : ℂ) = x) (hβ : (β : ℂ) = σ x) :
    β - α ^ p ∈ ideal := by
  have : Fact p.Prime := ⟨hp⟩
  have hN0 : 0 < N := by
    rw [hN]
    exact Nat.mul_pos (pow_pos hp.pos a) hM
  have : NeZero N := ⟨hN0.ne'⟩
  have hxint : IsIntegral ℤ x :=
    isIntegral_coe_adjoin_iff.mp (hα ▸ (mem_integralClosure_iff ℤ ℂ).mp α.2)
  obtain ⟨f, hf⟩ := exists_intPoly_eq_of_isIntegral hζ hxint
  let z : ComplexAlgebraicIntegers :=
    ⟨ζ, rootOfUnity_mem_complexAlgebraicIntegers ζ N hN0 hζ.pow_eq_one⟩
  have hz : z ^ (p ^ a * M) = 1 := Subtype.ext (by simp [z, ← hN, hζ.pow_eq_one])
  have hcoe : ∀ w : ComplexAlgebraicIntegers, ((aeval w f : ComplexAlgebraicIntegers) : ℂ) =
      aeval (w : ℂ) f := fun w => map_aeval_int (integralClosure ℤ ℂ).val.toRingHom w f
  have hcoeE : ∀ w : ℚ⟮ζ⟯, ((aeval w f : ℚ⟮ζ⟯) : ℂ) = aeval (w : ℂ) f :=
    fun w => map_aeval_int (ℚ⟮ζ⟯).val.toRingHom w f
  have hα' : α = aeval z f := by
    apply Subtype.ext
    rw [hα, ← hf, hcoeE, hcoe]
    rfl
  have hβ' : β = aeval (z ^ k) f := by
    apply Subtype.ext
    have hσx : σ (aeval (AdjoinSimple.gen ℚ ζ) f) = aeval (σ (AdjoinSimple.gen ℚ ζ)) f := by
      simpa using map_aeval_int (σ : ℚ⟮ζ⟯ →+* ℚ⟮ζ⟯) (AdjoinSimple.gen ℚ ζ) f
    rw [hβ, ← hf, hσx, hcoeE, hcoe, hσ]
    simp [z]
  rw [hα', hβ']
  exact aeval_pow_sub_pow_mem ideal z hz hkp f

theorem cyclotomic_frobenius_mem_iff (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (hp : p.Prime) [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hN : N = p ^ a * M)
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ N) (hkp : k ≡ p [MOD M]) {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {x : ℚ⟮ζ⟯}
    {α β : ComplexAlgebraicIntegers} (hα : (α : ℂ) = x) (hβ : (β : ℂ) = σ x) :
    β ∈ ideal ↔ α ∈ ideal := by
  have h := cyclotomic_frobenius_sub_pow_mem ideal hp hN hM hζ hkp hσ hα hβ
  constructor
  · intro hβm
    have hαp : α ^ p ∈ ideal := by simpa using ideal.sub_mem hβm h
    exact (Ideal.IsMaximal.isPrime ‹_›).mem_of_pow_mem p hαp
  · intro hαm
    have hαp : α ^ p ∈ ideal := ideal.pow_mem_of_mem hαm p hp.pos
    simpa using ideal.add_mem h hαp

theorem cyclotomic_frobenius_image_ideal (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (hp : p.Prime) [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hN : N = p ^ a * M) (hM : 0 < M) (hζ : IsPrimitiveRoot ζ N) (hkp : k ≡ p [MOD M])
    {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯} (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) :
    σ '' {x : ℚ⟮ζ⟯ | ∃ α : ComplexAlgebraicIntegers, (α : ℂ) = x ∧ α ∈ ideal} =
      {x : ℚ⟮ζ⟯ | ∃ α : ComplexAlgebraicIntegers, (α : ℂ) = x ∧ α ∈ ideal} := by
  ext y
  constructor
  · rintro ⟨x, ⟨α, hα, hαm⟩, rfl⟩
    have hint : IsIntegral ℤ ((σ x : ℚ⟮ζ⟯) : ℂ) :=
      (galois_isIntegral_iff σ).mpr (hα ▸ (mem_integralClosure_iff ℤ ℂ).mp α.2)
    exact ⟨⟨σ x, hint⟩, rfl, (cyclotomic_frobenius_mem_iff ideal hp hN hM hζ hkp hσ hα rfl).mpr
      hαm⟩
  · rintro ⟨β, hβ, hβm⟩
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    have hint : IsIntegral ℤ ((σ.symm y : ℚ⟮ζ⟯) : ℂ) :=
      (galois_isIntegral_iff σ.symm).mpr (hβ ▸ (mem_integralClosure_iff ℤ ℂ).mp β.2)
    refine ⟨⟨_, hint⟩, rfl, ?_⟩
    exact (cyclotomic_frobenius_mem_iff ideal hp hN hM hζ hkp hσ (x := σ.symm y) rfl
      (by rw [σ.apply_symm_apply]; exact hβ)).mp hβm

end Frobenius

end CFSG.LyonsUnitaryFour
