module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Sol78LemmaASpectral
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

open Polynomial Module
open scoped TensorProduct

namespace CFSG.LinearAlgebra

open CFSG.EvenSporadicStandard

theorem orderOf_zmod_le_finrank_of_conj_pow {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ℓ k : ℕ} (hℓ : ℓ.Prime) (hchar : (ℓ : K) ≠ 0)
    {f : Module.End K V} {e : V ≃ₗ[K] V}
    (hf : f ^ ℓ = 1) (hconj : e.conj f = f ^ k) (hne : f ≠ 1) :
    orderOf (k : ZMod ℓ) ≤ Module.finrank K V := by
  classical
  haveI : Nontrivial V := by
    rcases subsingleton_or_nontrivial V with h | h
    · exfalso
      apply hne
      apply LinearMap.ext
      intro v
      haveI : Subsingleton V := h
      exact Subsingleton.elim _ _
    · exact h
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  by_cases hk0 : (k : ZMod ℓ) = 0
  · rw [hk0]
    simp
  · let u : (ZMod ℓ)ˣ := Units.mk0 (k : ZMod ℓ) hk0
    let d : ℕ := orderOf u
    have hζr : ∀ {μ : K}, f.HasEigenvalue μ → μ ^ ℓ = 1 :=
      fun hμ => eigenvalue_pow_eq_one hf hμ
    have h_exists : ∃ ζ : K, f.HasEigenvalue ζ ∧ IsPrimitiveRoot ζ ℓ := by
      by_contra hno
      rw [not_exists] at hno
      have hall : ∀ μ, f.HasEigenvalue μ → μ = 1 := by
        intro μ hμ
        have hμℓ := hζr hμ
        by_contra hne1
        have hord : orderOf μ = ℓ := by
          rcases (Nat.dvd_prime hℓ).mp (orderOf_dvd_of_pow_eq_one hμℓ) with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hne1
          · exact h
        exact hno μ ⟨hμ, IsPrimitiveRoot.iff_orderOf.mpr hord⟩
      exact hne (eq_one_of_forall_hasEigenvalue_eq_one hchar hf hall)
    obtain ⟨ζ, hζeig, hζprim⟩ := h_exists
    have hstab : ∀ {μ : K}, f.HasEigenvalue μ → f.HasEigenvalue (μ ^ k) :=
      fun hμ => HasEigenvalue.of_conj_pow hconj hμ
    have hstab_iter : ∀ n : ℕ, f.HasEigenvalue (ζ ^ (k ^ n)) := by
      intro n
      induction n with
      | zero => simpa using hζeig
      | succ n ih =>
          have h := hstab ih
          simpa [pow_succ, pow_mul] using h
    let Φ : Fin d → f.Eigenvalues := fun i => ⟨ζ ^ (k ^ (i : ℕ)), hstab_iter (i : ℕ)⟩
    have hu_inj : ∀ a b : ℕ, a < d → b < d → u ^ a = u ^ b → a = b := by
      intro a b ha hb hab
      wlog hle : a ≤ b generalizing a b
      · exact (this b a hb ha hab.symm (le_of_not_ge hle)).symm
      have hdvd : d ∣ b - a := by
        change orderOf u ∣ b - a
        rw [orderOf_dvd_iff_pow_eq_one]
        have h1 : u ^ (b - a) = 1 := by
          apply mul_left_cancel (a := u ^ a)
          calc u ^ a * u ^ (b - a) = u ^ (a + (b - a)) := by rw [pow_add]
            _ = u ^ b := by rw [Nat.add_sub_of_le hle]
            _ = u ^ a := hab.symm
            _ = u ^ a * 1 := by rw [mul_one]
        exact h1
      by_contra hne
      have hlt : a < b := lt_of_le_of_ne hle hne
      have hpos : 0 < b - a := Nat.sub_pos_of_lt hlt
      have hlt_d : b - a < d := lt_of_le_of_lt (Nat.sub_le b a) hb
      have := Nat.le_of_dvd hpos hdvd
      omega
    have hΦ_inj : Function.Injective Φ := by
      intro i j hij
      have hval : ζ ^ (k ^ (i : ℕ)) = ζ ^ (k ^ (j : ℕ)) := congrArg Subtype.val hij
      have hmod : k ^ (i : ℕ) % ℓ = k ^ (j : ℕ) % ℓ := by
        have hi_lt : k ^ (i : ℕ) % ℓ < ℓ := Nat.mod_lt _ hℓ.pos
        have hj_lt : k ^ (j : ℕ) % ℓ < ℓ := Nat.mod_lt _ hℓ.pos
        have hpow : ζ ^ (k ^ (i : ℕ) % ℓ) = ζ ^ (k ^ (j : ℕ) % ℓ) := by
          calc ζ ^ (k ^ (i : ℕ) % ℓ) = ζ ^ (k ^ (i : ℕ)) := by
                 rw [hζprim.eq_orderOf, pow_mod_orderOf]
            _ = ζ ^ (k ^ (j : ℕ)) := hval
            _ = ζ ^ (k ^ (j : ℕ) % ℓ) := by
                 rw [hζprim.eq_orderOf, pow_mod_orderOf]
        exact hζprim.pow_inj hi_lt hj_lt hpow
      have hcast : ((k ^ (i : ℕ) : ℕ) : ZMod ℓ) = ((k ^ (j : ℕ) : ℕ) : ZMod ℓ) :=
        (ZMod.natCast_eq_natCast_iff' (k ^ (i : ℕ)) (k ^ (j : ℕ)) ℓ).mpr hmod
      have hzmod : (u : ZMod ℓ) ^ (i : ℕ) = (u : ZMod ℓ) ^ (j : ℕ) := by
        simpa [u] using hcast
      have hu : u ^ (i : ℕ) = u ^ (j : ℕ) := Units.ext hzmod
      exact Fin.ext (hu_inj (i : ℕ) (j : ℕ) i.isLt j.isLt hu)
    have hcard_le : d ≤ Fintype.card f.Eigenvalues := by
      calc d = Fintype.card (Fin d) := (Fintype.card_fin d).symm
        _ ≤ Fintype.card f.Eigenvalues := Fintype.card_le_of_injective Φ hΦ_inj
    have hcard : Fintype.card f.Eigenvalues ≤ Module.finrank K V :=
      card_eigenvalues_le_finrank f
    have hd_le : d ≤ Module.finrank K V := hcard_le.trans hcard
    have hcoe : (u : ZMod ℓ) = (k : ZMod ℓ) := rfl
    have hord : orderOf (k : ZMod ℓ) = d := by
      rw [← hcoe, orderOf_units]
    rwa [hord]

theorem le_finrank_of_eigen_orbit
    {K X V : Type*} [Field K] [Group X] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : X →* (V ≃ₗ[K] V)) {t n : X} {ℓ k m : ℕ}
    (hℓ : ℓ.Prime) (hchar : (ℓ : K) ≠ 0)
    (ht : orderOf t = ℓ) (hn : n⁻¹ * t * n = t ^ k)
    (hk : orderOf (k : ZMod ℓ) = m) (hρt : ρ t ≠ 1) :
    m ≤ Module.finrank K V := by
  classical
  let K' := AlgebraicClosure K
  let V' := K' ⊗[K] V
  let T : V ≃ₗ[K] V := ρ t
  let N : V ≃ₗ[K] V := ρ n
  let T' : V' ≃ₗ[K'] V' := T.baseChange K K' V V
  let N' : V' ≃ₗ[K'] V' := N.baseChange K K' V V
  let f : Module.End K' V' := T'.toLinearMap
  let e : V' ≃ₗ[K'] V' := N'.symm
  have hTpow : T ^ ℓ = 1 := by
    change (ρ t) ^ ℓ = 1
    rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have hT'pow : T' ^ ℓ = 1 := by
    have h := congrArg (fun e : V ≃ₗ[K] V => e.baseChange K K' V V) hTpow
    simpa [T', LinearEquiv.baseChange_pow, LinearEquiv.baseChange_one] using h
  have hfpow : f ^ ℓ = 1 := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun e : V' ≃ₗ[K'] V' => e v) hT'pow
    simpa [f, LinearEquiv.pow_apply, Module.End.pow_apply] using h
  have hNconj : N⁻¹ * T * N = T ^ k := by
    change (ρ n)⁻¹ * ρ t * ρ n = (ρ t) ^ k
    rw [← map_inv, ← map_mul, ← map_mul, hn, ← map_pow]
  have hNconj' : N'⁻¹ * T' * N' = T' ^ k := by
    have h := congrArg (fun e : V ≃ₗ[K] V => e.baseChange K K' V V) hNconj
    simpa [N', T', LinearEquiv.baseChange_mul, LinearEquiv.baseChange_inv,
      LinearEquiv.baseChange_pow] using h
  have hconj : e.conj f = f ^ k := by
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun L : V' ≃ₗ[K'] V' => L v) hNconj'
    simpa [e, f, LinearEquiv.conj_apply_apply, Module.End.pow_apply, LinearEquiv.pow_apply]
      using hv
  haveI : FaithfulSMul K K' :=
    (faithfulSMul_iff_algebraMap_injective K K').mpr (RingHom.injective _)
  haveI : Module.Flat K V := Module.Flat.of_free
  have hfne : f ≠ 1 := by
    intro h
    apply hρt
    change T = 1
    apply LinearEquiv.ext
    intro v
    have h' : T.toLinearMap.baseChange K' = (1 : Module.End K V).baseChange K' := by
      simpa [f, T', LinearEquiv.coe_baseChange] using h
    have h'' := LinearMap.baseChangeHom_injective K V K' h'
    exact congrArg (fun L : V →ₗ[K] V => L v) h''
  have hchar' : (ℓ : K') ≠ 0 := by
    intro h
    apply hchar
    exact (algebraMap K K').injective (by simpa using h)
  have hmain := orderOf_zmod_le_finrank_of_conj_pow (K := K') (V := V')
    hℓ hchar' hfpow hconj hfne
  calc m = orderOf (k : ZMod ℓ) := hk.symm
    _ ≤ Module.finrank K' V' := hmain
    _ = Module.finrank K V := Module.finrank_baseChange

end CFSG.LinearAlgebra

end
