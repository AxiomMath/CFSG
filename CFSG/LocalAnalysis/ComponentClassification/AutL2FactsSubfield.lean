module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSymmetricFourEndpoint

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

theorem exists_fixed_subfield (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    ∃ K₀ : Subfield F, (∀ x, x ∈ K₀ ↔ σ x = x) ∧ Nat.card F = Nat.card K₀ ^ 2 ∧
      ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨-, hpP, -⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hpP⟩
  let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    have := congrArg (fun τ : F ≃+* F => τ x) h1
    simpa using this
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    norm_num at hσ
  let σA : F ≃ₐ[ZMod (ringChar F)] F :=
    AlgEquiv.ofRingEquiv (f := σ) (fun x => by
      have h : (σ.toRingHom.comp (algebraMap (ZMod (ringChar F)) F) :
          ZMod (ringChar F) →+* F) = algebraMap (ZMod (ringChar F)) F := RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h x)
  have hσA2 : σA ^ 2 = 1 := by
    ext x
    exact hσσ x
  have hσA1 : σA ≠ 1 := by
    intro h
    apply hσ1
    ext x
    exact DFunLike.congr_fun h x
  have hσAord : orderOf σA = 2 := orderOf_eq_prime hσA2 hσA1
  let H : Subgroup (F ≃ₐ[ZMod (ringChar F)] F) := zpowers σA
  have hHcard : Nat.card H = 2 := by
    rw [Nat.card_zpowers, hσAord]
  let K := IntermediateField.fixedField H
  have hmem : ∀ x : F, x ∈ K ↔ σ x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    constructor
    · intro h
      exact h σA (mem_zpowers σA)
    · intro h τ hτ
      obtain ⟨k, hk⟩ := hτ
      simp only at hk
      subst hk
      have hpow : ∀ m : ℕ, (σA ^ m) x = x := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          rw [pow_succ, AlgEquiv.mul_apply]
          change (σA ^ m) (σ x) = x
          rw [h, ih]
      have hpow' : ∀ m : ℕ, (σA ^ m)⁻¹ x = x := by
        intro m
        conv_lhs => rw [← hpow m]
        exact (σA ^ m).symm_apply_apply x
      rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
      · simp only [zpow_natCast]
        exact hpow m
      · rw [zpow_neg, zpow_natCast]
        exact hpow' m
  have hfinrank : Module.finrank K F = 2 := by
    change Module.finrank (IntermediateField.fixedField H) F = 2
    rw [IntermediateField.finrank_fixedField_eq_card, hHcard]
  refine ⟨K.toSubfield, hmem, ?_, ?_⟩
  · have := Module.natCard_eq_pow_finrank (K := K) (V := F)
    rw [hfinrank] at this
    exact this
  · intro c hc
    let σF : F ≃ₐ[K] F := {
      toRingEquiv := σ
      commutes' := fun x => (hmem x).mp x.property }
    have hσF1 : σF ≠ 1 := by
      intro h
      apply hσ1
      ext x
      exact DFunLike.congr_fun h x
    have hGalcard : Nat.card (F ≃ₐ[K] F) = 2 := by
      rw [IsGalois.card_aut_eq_finrank K F, hfinrank]
    have hGalcases (τ : F ≃ₐ[K] F) : τ = 1 ∨ τ = σF := by
      rcases (Nat.card_eq_two_iff' (1 : F ≃ₐ[K] F)).mp hGalcard with ⟨y, -, hyuniq⟩
      have hsigy : σF = y := hyuniq σF hσF1
      by_cases hτ : τ = 1
      · exact Or.inl hτ
      · exact Or.inr ((hyuniq τ hτ).trans hsigy.symm)
    have huniv : (Finset.univ : Finset (F ≃ₐ[K] F)) = {1, σF} := by
      ext τ
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hGalcases τ
    have hnorm : algebraMap K F (Algebra.norm K c) = c * σ c := by
      rw [Algebra.norm_eq_prod_automorphisms, huniv,
        Finset.prod_insert (by simpa using hσF1.symm)]
      simp [σF]
    have hnorm1 : Algebra.norm K c = 1 := by
      apply (algebraMap K F).injective
      rw [hnorm, hc, map_one]
    have hg : ∀ τ : F ≃ₐ[K] F, τ ∈ zpowers σF := by
      intro τ
      rcases hGalcases τ with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one hg hnorm1
    exact ⟨y, hy⟩

end CFSG.ComponentClassification.AutL2Facts
