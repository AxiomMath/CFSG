module

public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSU3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

section Lift

variable {p f : ℕ} {K : Type} [Field K]

theorem isPerfect_and_center_unitarySU_of (h : UnitaryFieldData p f K) {d : ℕ} (hd : 3 ≤ d)
    (hnq : (d, p ^ f) ≠ (3, 2)) :
    Group.IsPerfect (unitarySU p f K d) ∧
      Subgroup.center (unitarySU p f K d) = unitaryScalars h d := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hF : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨hqs, hcen⟩ := isQuasisimple_statedSU_of_card (F := K) (p := p) (f := f) hF hd hnq
  exact ⟨hqs.1, hcen.trans (unitaryScalars_eq h (by omega)).symm⟩

theorem exists_lift_unitarySU_of (h : UnitaryFieldData p f K) (hp : p ≠ 2) {d : ℕ}
    (hd : 3 ≤ d) (hnq : (d, p ^ f) ≠ (3, 2)) {X : Type} [Group X]
    (θ : unitarySU p f K d →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (unitarySU p f K d)) (σ : X ≃* X) :
    ∃ (A : GL (Fin d) K) (φ : K ≃+* K)
      (hA : ∀ g : unitarySU p f K d,
        A * glAut φ (g : GL (Fin d) K) * A⁻¹ ∈ unitarySU p f K d),
      ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1 ∧
        (∀ g : unitarySU p f K d, θ (unitaryConjHom A φ hA g) = σ (θ g)) ∧
        ((∀ x, σ (σ x) = x) →
          (φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c) ∧
            (unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA) = MonoidHom.id _) := by
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ d = 2 * r + ε := ⟨d / 2, d % 2, by omega, by omega⟩
  obtain ⟨hperf, hcen⟩ := isPerfect_and_center_unitarySU_of h hd hnq
  have := hperf
  obtain ⟨β, hβ, hβinv⟩ := exists_mulEquiv_of_central_cover
    (unitaryProj_surjective h (2 * r + ε)) (by rw [ker_unitaryProj, hcen]) hθ hker σ
  obtain ⟨φ, A, hAu, hAg, hφ⟩ := exists_unitary_semilinear_psu h hp (by omega) hε hd β
  have hlift := hβ (unitaryConjHom A φ fun g => (hAg g).1) fun x => ((hAg x).2).symm
  exact ⟨A, φ, fun g => (hAg g).1, hAu, hlift, fun hσ =>
    ⟨hφ (hβinv hσ), lift_comp_self_eq_id hker hσ hlift⟩⟩

theorem su_lift_of_ne [Finite K] [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {d : ℕ} (hd : 3 ≤ d) (hnq : (d, p ^ f) ≠ (3, 2)) (X : Type)
    [Group X] (θ : Su K p f d →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f d)) (σ : X ≃* X) :
    ∃ (α : Su K p f d →* Su K p f d) (g : GL (Fin d) K) (φ : K ≃+* K),
      (∀ x, θ (α x) = σ (θ x)) ∧
      (∀ x, ((α x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (g : Matrix (Fin d) (Fin d) K) *
          φ.mapMatrix ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ∧
      ((g : Matrix (Fin d) (Fin d) K).map (unitaryInvolution K p f))ᵀ *
        (g : Matrix (Fin d) (Fin d) K) = 1 ∧
      ((∀ x, σ (σ x) = x) →
        (φ = RingEquiv.refl K ∨ φ = unitaryInvolution K p f) ∧ α.comp α = MonoidHom.id _) := by
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨e, he⟩ : ∃ e : Su K p f d ≃* unitarySU p f K d,
      ∀ x, ((e x : unitarySU p f K d) : GL (Fin d) K) = (x : GL (Fin d) K) :=
    ⟨suEquivUnitarySU K p f hK d, fun x => rfl⟩
  have he' : ∀ y : unitarySU p f K d, ((e.symm y : Su K p f d) : GL (Fin d) K) =
      (y : GL (Fin d) K) := fun y => by rw [← he, MulEquiv.apply_symm_apply]
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ := exists_lift_unitarySU_of h hp2 hd hnq
    (θ.comp e.symm.toMonoidHom) (hθ.comp e.symm.surjective)
    (fun y hy => by
      have h1 : e.symm y ∈ Subgroup.center (Su K p f d) := hker hy
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro z
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact h1 (e.symm z)) σ
  have hbar : ∀ c, h.bar c = unitaryInvolution K p f c := fun c => by
    rw [unitaryInvolution_apply, UnitaryFieldData.bar_apply]
  refine ⟨e.symm.toMonoidHom.comp ((unitaryConjHom A φ hA).comp e.toMonoidHom), A, φ,
    fun x => ?_, fun x => ?_, ?_, fun hσ => ?_⟩
  · have := hlift (e x)
    simpa using this
  · show (((e.symm (unitaryConjHom A φ hA (e x)) : Su K p f d) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = _
    rw [he', coe_unitaryConjHom, Units.val_mul, Units.val_mul, coe_glAut, he,
      RingEquiv.mapMatrix_apply]
  · have hmap : (A : Matrix (Fin d) (Fin d) K).map (unitaryInvolution K p f) =
        (A : Matrix (Fin d) (Fin d) K).map h.bar := by
      ext i j
      simp only [Matrix.map_apply, hbar]
    rw [hmap]
    exact hAu
  · obtain ⟨hφ, hsq⟩ := hinv hσ
    refine ⟨hφ.imp id fun hb => RingEquiv.ext fun c => (hb c).trans (hbar c), ?_⟩
    refine MonoidHom.ext fun x => ?_
    have := DFunLike.congr_fun hsq (e x)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      MonoidHom.id_apply] at this ⊢
    rw [this, MulEquiv.symm_apply_apply]

end Lift

section SU4

open CFSG.ClassicalInvolution.Q3.Q3PP

theorem su4_lift {X : Type} [Group X] (θ : Su F9 3 1 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su F9 3 1 4)) (σ : X ≃* X) :
    ∃ (α : Su F9 3 1 4 →* Su F9 3 1 4) (g : GL (Fin 4) F9) (φ : F9 ≃+* F9),
      (∀ x, θ (α x) = σ (θ x)) ∧
      (∀ x, ((α x : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
        (g : Matrix (Fin 4) (Fin 4) F9) *
          φ.mapMatrix ((x : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *
            ((g⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)) ∧
      ((g : Matrix (Fin 4) (Fin 4) F9).map (unitaryInvolution F9 3 1))ᵀ *
        (g : Matrix (Fin 4) (Fin 4) F9) = 1 ∧
      ((∀ x, σ (σ x) = x) →
        (φ = RingEquiv.refl F9 ∨ φ = unitaryInvolution F9 3 1) ∧ α.comp α = MonoidHom.id _) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F9 3 := inferInstance
  exact su_lift_of_ne (K := F9) (p := 3) (f := 1) card_F9 (by norm_num) le_rfl (d := 4)
    (by norm_num) (by decide) X θ hθ hker σ

end SU4

end CFSG.ClassicalInvolution.Q3.Q3MFOU4
