module

public import Mathlib

public section

namespace CFSG.Goldschmidt.G2

open Polynomial

variable {D : Type*} [AddCommGroup D] [Module (ZMod 2) D] [Finite D]

theorem isCyclic_of_normalizes_regular (ζ : D ≃ₗ[ZMod 2] D) {d₀ : D} (hd₀ : d₀ ≠ 0)
    (htr : ∀ v : D, v ≠ 0 → ∃ i : ℕ, (ζ ^ i) d₀ = v) (P : Subgroup (D ≃ₗ[ZMod 2] D))
    (hP : ∀ p ∈ P, ∃ i : ℕ, p * ζ * p⁻¹ = ζ ^ i) (hfix : ∀ p ∈ P, p d₀ = d₀) :
    IsCyclic P := by
  classical
  have : Finite (Module.End (ZMod 2) D) :=
    Finite.of_injective (fun g : Module.End (ZMod 2) D => (g : D → D)) DFunLike.coe_injective
  set z : Module.End (ZMod 2) D := (ζ : D →ₗ[ZMod 2] D) with hz
  set f : (ZMod 2)[X] →ₐ[ZMod 2] Module.End (ZMod 2) D := aeval z with hf
  have hpow : ∀ (i : ℕ) (v : D), (z ^ i) v = (ζ ^ i) v := by
    intro i v
    rw [Module.End.pow_apply, LinearEquiv.coe_pow]
    rfl
  have hcomm : ∀ q, Commute (f q) z := by
    intro q
    have h1 : f (q * X) = f (X * q) := by rw [mul_comm]
    show f q * z = z * f q
    simpa [map_mul, hf, aeval_X] using h1
  have hcommpow : ∀ q (i : ℕ) (v : D), f q ((ζ ^ i) v) = (ζ ^ i) (f q v) := by
    intro q i v
    have := congrArg (fun g : Module.End (ZMod 2) D => g v) ((hcomm q).pow_right i).eq
    simp only [Module.End.mul_apply, hpow] at this
    exact this
  have hinj : ∀ q, f q ≠ 0 → Function.Injective (f q) := by
    intro q hq
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    apply hq
    rw [LinearMap.mem_ker] at hv
    obtain ⟨i, rfl⟩ := htr v hv0
    rw [hcommpow] at hv
    have hfd : f q d₀ = 0 := by simpa using congrArg (ζ ^ i).symm hv
    ext u
    by_cases hu : u = 0
    · rw [hu, map_zero, LinearMap.zero_apply]
    obtain ⟨j, rfl⟩ := htr u hu
    rw [hcommpow, hfd, map_zero, LinearMap.zero_apply]
  set I := RingHom.ker f with hI
  have hprime : I.IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, RingHom.mem_ker, map_one]
      intro h1
      apply hd₀
      simpa using congrArg (fun g : Module.End (ZMod 2) D => g d₀) h1
    · intro a b hab
      rw [RingHom.mem_ker, map_mul] at hab
      rw [RingHom.mem_ker, RingHom.mem_ker]
      by_cases ha : f a = 0
      · exact Or.inl ha
      · right
        ext v
        have := congrArg (fun g : Module.End (ZMod 2) D => g v) hab
        simp only [Module.End.mul_apply, LinearMap.zero_apply] at this
        rw [LinearMap.zero_apply]
        exact hinj a ha (this.trans (map_zero (f a)).symm)
  have hne : I ≠ ⊥ := by
    intro hbot
    have hfinj : Function.Injective f := by
      rw [← RingHom.injective_iff_ker_eq_bot] at hbot
      exact hbot
    exact not_injective_infinite_finite f hfinj
  have hmax : I.IsMaximal := hprime.isMaximal hne
  let _ : Field ((ZMod 2)[X] ⧸ I) := Ideal.Quotient.field I
  have : Finite ((ZMod 2)[X] ⧸ I) :=
    Finite.of_injective _ (Ideal.kerLiftAlg_injective f)
  have hcyc : IsCyclic (((ZMod 2)[X] ⧸ I) ≃ₐ[ZMod 2] ((ZMod 2)[X] ⧸ I)) :=
    FiniteField.instIsCyclicAlgEquivOfFinite (ZMod 2) _
  set E := f.range with hE
  let c : P → Module.End (ZMod 2) D ≃ₐ[ZMod 2] Module.End (ZMod 2) D :=
    fun p => LinearEquiv.conjAlgEquiv (ZMod 2) (p : D ≃ₗ[ZMod 2] D)
  have hc : ∀ (p : P) (g : Module.End (ZMod 2) D) (v : D),
      c p g v = (p : D ≃ₗ[ZMod 2] D) (g ((p : D ≃ₗ[ZMod 2] D)⁻¹ v)) := by
    intro p g v
    simp [c, LinearEquiv.conjAlgEquiv_apply]
  have hcz : ∀ p : P, ∃ i : ℕ, c p z = z ^ i := by
    intro p
    obtain ⟨i, hi⟩ := hP p p.2
    refine ⟨i, LinearMap.ext fun v => ?_⟩
    rw [hc, hpow, ← hi]
    rfl
  have hmap : ∀ p : P, E.map (c p : Module.End (ZMod 2) D →ₐ[ZMod 2] _) ≤ E := by
    intro p
    rintro _ ⟨e, ⟨q, rfl⟩, rfl⟩
    obtain ⟨i, hi⟩ := hcz p
    refine ⟨q.comp (X ^ i), ?_⟩
    show aeval z (q.comp (X ^ i)) = c p (aeval z q)
    rw [aeval_comp, aeval_X_pow, ← aeval_algHom_apply, ← hi]
  have hmapeq : ∀ p : P, E.map (c p : Module.End (ZMod 2) D →ₐ[ZMod 2] _) = E := by
    intro p
    refine le_antisymm (hmap p) fun e he => ?_
    have h1 : c p⁻¹ e ∈ E := hmap p⁻¹ ⟨e, he, rfl⟩
    refine ⟨c p⁻¹ e, h1, ?_⟩
    apply LinearMap.ext
    intro v
    show c p (c p⁻¹ e) v = e v
    rw [hc, hc]
    simp
  let σ : P →* (E ≃ₐ[ZMod 2] E) :=
    { toFun := fun p => ((c p).subalgebraMap E).trans (Subalgebra.equivOfEq _ _ (hmapeq p))
      map_one' := by
        apply AlgEquiv.ext
        intro e
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        show c 1 (e : Module.End (ZMod 2) D) v = (e : Module.End (ZMod 2) D) v
        rw [hc]
        simp
      map_mul' := by
        intro p p'
        apply AlgEquiv.ext
        intro e
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        show c (p * p') (e : Module.End (ZMod 2) D) v =
          c p (c p' (e : Module.End (ZMod 2) D)) v
        rw [hc, hc, hc]
        simp [mul_inv_rev] }
  have hσ : ∀ (p : P) (e : E), ((σ p e : E) : Module.End (ZMod 2) D) = c p e := fun _ _ => rfl
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hzE : z ∈ E := ⟨X, aeval_X z⟩
    have h1 : c p z = z := by
      have := congrArg (fun φ : E ≃ₐ[ZMod 2] E => ((φ ⟨z, hzE⟩ : E) : Module.End (ZMod 2) D)) hp
      simpa [hσ] using this
    have h2 : ∀ v : D, (p : D ≃ₗ[ZMod 2] D) (ζ v) = ζ ((p : D ≃ₗ[ZMod 2] D) v) := by
      intro v
      have := congrArg (fun g : Module.End (ZMod 2) D => g ((p : D ≃ₗ[ZMod 2] D) v)) h1
      simp only [hc] at this
      simpa [hz] using this
    have h3 : ∀ i : ℕ, (p : D ≃ₗ[ZMod 2] D) ((ζ ^ i) d₀) = (ζ ^ i) d₀ := by
      intro i
      induction i with
      | zero => simpa using hfix p p.2
      | succ i ih => rw [pow_succ', LinearEquiv.mul_apply, h2, ih]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    by_cases hv : v = 0
    · rw [hv, map_zero, map_zero]
    obtain ⟨i, rfl⟩ := htr v hv
    simpa using h3 i
  let τ : P →* (((ZMod 2)[X] ⧸ I) ≃ₐ[ZMod 2] ((ZMod 2)[X] ⧸ I)) :=
    (AlgEquiv.autCongr (Ideal.quotientKerEquivRange f).symm).toMonoidHom.comp σ
  have hτ : Function.Injective τ :=
    (AlgEquiv.autCongr (Ideal.quotientKerEquivRange f).symm).injective.comp hσinj
  exact isCyclic_of_injective τ hτ

end CFSG.Goldschmidt.G2
