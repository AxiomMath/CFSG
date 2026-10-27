module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.TraceValues
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.LyonsUnitaryFour

open IntermediateField Polynomial

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem character_rat_of_pow_prime_pow (ρ : Representation ℂ G V) {m : ℕ} (hm : 0 < m) {ξ : ℂ}
    (hξ : ξ ^ m = 1) {p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) {x : G} {e : ℕ}
    (hx : x ^ p ^ e = 1) (hχ : ρ.character x ∈ ℚ⟮ξ⟯) : ∃ q : ℚ, ρ.character x = q := by
  set n := p ^ e * m with hn
  have hn0 : 0 < n := Nat.mul_pos (pow_pos hp.pos e) hm
  have : NeZero n := ⟨hn0.ne'⟩
  set η : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hη : IsPrimitiveRoot η n := Complex.isPrimitiveRoot_exp n hn0.ne'
  have : IsCyclotomicExtension {n} ℚ ℚ⟮η⟯ := isCyclotomicExtension_adjoin_primitiveRoot hη
  have : NumberField ℚ⟮η⟯ := IsCyclotomicExtension.numberField {n} ℚ ℚ⟮η⟯
  have : IsGalois ℚ ℚ⟮η⟯ := IsCyclotomicExtension.isGalois {n} ℚ ℚ⟮η⟯
  set f := ρ x with hfdef
  have hfe : f ^ (p ^ e) = 1 := by rw [hfdef, ← map_pow, hx, map_one]
  have hfn : f ^ n = 1 := by rw [hn, pow_mul, hfe, one_pow]
  set c : ℚ⟮η⟯ := ⟨LinearMap.trace ℂ V f, trace_mem_adjoin hη hfn⟩ with hcdef
  have hξn : ξ ^ n = 1 := by rw [hn, mul_comm, pow_mul, hξ, one_pow]
  set ξE : ℚ⟮η⟯ := ⟨ξ, mem_adjoin_of_pow_eq_one hη hξn⟩ with hξEdef
  have hξalg : IsAlgebraic ℚ ξ := by
    refine ⟨X ^ m - 1, X_pow_sub_C_ne_zero hm 1, ?_⟩
    simp [hξ]
  obtain ⟨g, hg⟩ : ∃ g : ℚ[X], aeval ξ g = ρ.character x := by
    have h' : ρ.character x ∈ (ℚ⟮ξ⟯).toSubalgebra := hχ
    rw [adjoin_simple_toSubalgebra_of_isAlgebraic hξalg, Algebra.adjoin_singleton_eq_range_aeval]
      at h'
    obtain ⟨g, hg⟩ := h'
    exact ⟨g, hg⟩
  have hcg : c = aeval ξE g := by
    apply Subtype.ext
    have := aeval_algHom_apply (ℚ⟮η⟯).val ξE g
    simp only [IntermediateField.coe_val] at this
    rw [← this]
    exact hg.symm
  have hfix : ∀ τ : ℚ⟮η⟯ ≃ₐ[ℚ] ℚ⟮η⟯, τ c = c := by
    intro τ
    set u := ((IsCyclotomicExtension.Rat.galEquivZMod n ℚ⟮η⟯ τ : (ZMod n)ˣ) : ZMod n).val
      with hudef
    have hτ : (τ (AdjoinSimple.gen ℚ η) : ℂ) = η ^ u := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n ℚ⟮η⟯ τ
        (isPrimitiveRoot_adjoinSimple_gen hη).pow_eq_one]
      simp [u]
    have hu : u.Coprime n := ZMod.val_coe_unit_coprime _
    have hcop : (p ^ e).Coprime m :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
    let k := Nat.chineseRemainder hcop u 1
    have hk1 : (k : ℕ) ≡ u [MOD p ^ e] := k.2.1
    have hk2 : (k : ℕ) ≡ 1 [MOD m] := k.2.2
    have hkcop : (k : ℕ).Coprime n := by
      apply Nat.Coprime.mul_right
      · rw [Nat.Coprime, hk1.gcd_eq]
        exact Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hu
      · rw [Nat.Coprime, hk2.gcd_eq, Nat.gcd_one_left]
    obtain ⟨σ, hσ⟩ := exists_galois_gen_eq_pow hη hkcop
    have hσ' : (σ (AdjoinSimple.gen ℚ η) : ℂ) = η ^ (k : ℕ) := by rw [hσ]; simp
    have hσξ : σ ξE = ξE := by
      rw [galois_apply_of_pow_eq_one hη hσ' (Subtype.ext (by simpa using hξn))]
      exact (pow_eq_pow_of_modEq (Subtype.ext (by simpa using hξ) : ξE ^ m = 1) hk2).trans
        (pow_one _)
    have hσc : σ c = c := by
      have := aeval_algHom_apply (σ : ℚ⟮η⟯ →ₐ[ℚ] ℚ⟮η⟯) ξE g
      simp only [AlgEquiv.coe_toAlgHom] at this
      rw [hcg, ← this, hσξ]
    have h1 : (τ c : ℂ) = LinearMap.trace ℂ V (f ^ u) := galois_trace_eq hη hτ hfn
    have h2 : (σ c : ℂ) = LinearMap.trace ℂ V (f ^ (k : ℕ)) := galois_trace_eq hη hσ' hfn
    have h3 : f ^ (k : ℕ) = f ^ u := pow_eq_pow_of_modEq hfe hk1
    apply Subtype.ext
    rw [h1, ← h3, ← h2, hσc]
  have hbot : c ∈ (⊥ : IntermediateField ℚ ℚ⟮η⟯) := (IsGalois.mem_bot_iff_fixed c).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  refine ⟨q, ?_⟩
  have := congrArg (fun y : ℚ⟮η⟯ => (y : ℂ)) hq
  rw [show ρ.character x = LinearMap.trace ℂ V f from rfl]
  simpa [hcdef] using this.symm

theorem character_rat_of_forall_mem_cyclotomic (ρ : Representation ℂ G V) {m : ℕ} (hm : 0 < m)
    (hχ : ∀ g, ρ.character g ∈ ℚ⟮Complex.exp (2 * Real.pi * Complex.I / m)⟯) {p : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) {x : G} {e : ℕ} (hx : x ^ p ^ e = 1) :
    ∃ q : ℚ, ρ.character x = q :=
  character_rat_of_pow_prime_pow ρ hm (Complex.isPrimitiveRoot_exp m hm.ne').pow_eq_one hp hpm hx
    (hχ x)

theorem character_rat_of_isPGroup (ρ : Representation ℂ G V) {m : ℕ} (hm : 0 < m) {ξ : ℂ}
    (hξ : ξ ^ m = 1) (hχ : ∀ g, ρ.character g ∈ ℚ⟮ξ⟯) {p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m)
    {P : Subgroup G} (hP : IsPGroup p P) {y : G} (hy : y ∈ P) : ∃ q : ℚ, ρ.character y = q := by
  obtain ⟨e, he⟩ := hP ⟨y, hy⟩
  have hy' : y ^ p ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  exact character_rat_of_pow_prime_pow ρ hm hξ hp hpm hy' (hχ y)

end CFSG.LyonsUnitaryFour
