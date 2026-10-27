module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Finite.Basic

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

section Singer

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem linear_of_commute_lmul [FiniteDimensional F K] (t : K)
    (ht : IntermediateField.adjoin F {t} = ⊤) (φ : Module.End F K)
    (h : ∀ x, φ (t * x) = t * φ x) : ∀ k x, φ (k * x) = k * φ x := by
  have halg : Algebra.adjoin F {t} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element (IsAlgebraic.of_finite F t) ht
  let S : Subalgebra F K :=
    { carrier := {k | ∀ x, φ (k * x) = k * φ x}
      mul_mem' := by
        intro a b ha hb x
        rw [mul_assoc, ha, hb, mul_assoc]
      one_mem' := by intro x; simp
      add_mem' := by
        intro a b ha hb x
        rw [add_mul, map_add, ha, hb, add_mul]
      zero_mem' := by intro x; simp
      algebraMap_mem' := by
        intro c x
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_mul_assoc,
          one_mul] }
  have hle : Algebra.adjoin F {t} ≤ S := by
    rw [Algebra.adjoin_le_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact h
  intro k
  exact hle (by rw [halg]; exact Algebra.mem_top)

theorem eq_mul_of_linear (φ : Module.End F K) (h : ∀ k x, φ (k * x) = k * φ x) (x : K) :
    φ x = x * φ 1 := by
  have := h x 1
  rw [mul_one] at this
  exact this

theorem commute_of_linear (φ ψ : Module.End F K) (hφ : ∀ k x, φ (k * x) = k * φ x)
    (hψ : ∀ k x, ψ (k * x) = k * ψ x) (x : K) : φ (ψ x) = ψ (φ x) := by
  rw [eq_mul_of_linear φ hφ (ψ x), eq_mul_of_linear ψ hψ x, eq_mul_of_linear ψ hψ (φ x),
    eq_mul_of_linear φ hφ x]
  ring

end Singer

section SingerMatrix

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F] [FiniteDimensional F K]

theorem exists_singer_matrix (h3 : Module.finrank F K = 3) {r : ℕ} (hr : r.Prime)
    (hrq : ¬ r ∣ Nat.card F - 1) (t : K) (htr : t ^ r = 1) (ht1 : t ≠ 1) :
    ∃ m : Matrix.SpecialLinearGroup (Fin 3) F, m ^ r = 1 ∧
      m ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) ∧
      ∀ γ δ : Matrix.SpecialLinearGroup (Fin 3) F, γ * m = m * γ → δ * m = m * δ →
        γ * δ = δ * γ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  have hcop : Nat.Coprime r (Nat.card F - 1) := (Nat.Prime.coprime_iff_not_dvd hr).2 hrq
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.ne_zero] at htr
    exact zero_ne_one htr
  have htF : ∀ a : F, algebraMap F K a ≠ t := by
    intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact ht0 ha.symm
    have h1 : a ^ (Nat.card F - 1) = 1 := by
      rw [← hq]
      exact FiniteField.pow_card_sub_one_eq_one a ha0
    have h2 : a ^ r = 1 := by
      apply (algebraMap F K).injective
      rw [map_pow, ha, htr, map_one]
    have h4 : a ^ Nat.gcd r (Nat.card F - 1) = 1 := (pow_gcd_eq_one (a := a)).2 ⟨h2, h1⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h4
    exact ht1 (by rw [← ha, h4, map_one])
  have hsimple := IntermediateField.isSimpleOrder_of_finrank_prime F K (h3 ▸ Nat.prime_three)
  have hadj : IntermediateField.adjoin F {t} = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin F {t}) with h | h
    · exfalso
      have hmem : t ∈ IntermediateField.adjoin F {t} := IntermediateField.subset_adjoin F {t} rfl
      rw [h, IntermediateField.mem_bot] at hmem
      obtain ⟨a, ha⟩ := hmem
      exact htF a ha
    · exact h
  let b := Module.finBasisOfFinrankEq F K h3
  let e := LinearMap.toMatrixAlgEquiv b
  let T : Module.End F K := Algebra.lmul F K t
  have hTx : ∀ x, T x = t * x := fun x => rfl
  have hTr : T ^ r = 1 := by
    rw [← map_pow, htr, map_one]
  have hdet : (e T).det = 1 := by
    have h1 : (e T).det = LinearMap.det T := LinearMap.det_toMatrix b T
    rw [h1]
    have hd1 : LinearMap.det T ^ r = 1 := by
      rw [← map_pow, hTr, map_one]
    have hd0 : LinearMap.det T ≠ 0 := by
      intro h0
      rw [h0, zero_pow hr.ne_zero] at hd1
      exact zero_ne_one hd1
    have hd2 : LinearMap.det T ^ (Nat.card F - 1) = 1 := by
      rw [← hq]
      exact FiniteField.pow_card_sub_one_eq_one _ hd0
    have h4 := (pow_gcd_eq_one (a := LinearMap.det T)).2 ⟨hd1, hd2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h4
  refine ⟨⟨e T, hdet⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    refine (Matrix.SpecialLinearGroup.coe_pow _ r).trans ?_
    show (e T) ^ r = 1
    rw [← map_pow, hTr, map_one]
  · intro hm
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hm
    have hc' : Matrix.scalar (Fin 3) c = e T := hc
    have h1 : e T = algebraMap F (Matrix (Fin 3) (Fin 3) F) c := by
      rw [← hc']
      ext i j
      simp only [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal]
      rfl
    have h2 : T = algebraMap F (Module.End F K) c := by
      apply e.injective
      rw [h1, AlgEquiv.commutes]
    have h3' := congrArg (fun f : Module.End F K => f 1) h2
    simp only [hTx, mul_one] at h3'
    apply htF c
    rw [h3']
    simp [Algebra.algebraMap_eq_smul_one]
  · intro γ δ hγ hδ
    have hlin : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
        g * ⟨e T, hdet⟩ = ⟨e T, hdet⟩ * g → ∀ k x : K, (e.symm g.1) (k * x) = k * (e.symm g.1) x := by
      intro g hg
      have h1 : g.1 * e T = e T * g.1 := congrArg Subtype.val hg
      have h2 : e.symm g.1 * T = T * e.symm g.1 := by
        apply e.injective
        rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
        exact h1
      have h3'' : ∀ x, (e.symm g.1) (t * x) = t * (e.symm g.1) x := by
        intro x
        have := congrArg (fun f : Module.End F K => f x) h2
        simpa [hTx] using this
      exact linear_of_commute_lmul t hadj _ h3''
    have hφ := hlin γ hγ
    have hψ := hlin δ hδ
    apply Subtype.ext
    show γ.1 * δ.1 = δ.1 * γ.1
    apply e.symm.injective
    rw [map_mul, map_mul]
    ext x
    exact commute_of_linear (e.symm γ.1) (e.symm δ.1) hφ hψ x

end SingerMatrix

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
