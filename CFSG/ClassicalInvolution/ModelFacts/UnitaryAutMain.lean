module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutModel
public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan

section Model

variable {p f : ℕ} {K : Type} [Field K]

theorem isPerfect_and_center_unitarySU (h : UnitaryFieldData p f K) (hq : 5 ≤ p ^ f) {d : ℕ}
    (hd : 3 ≤ d) :
    Group.IsPerfect (unitarySU p f K d) ∧
      Subgroup.center (unitarySU p f K d) = unitaryScalars h d := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hF : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : (d, p ^ f) ≠ (3, 2) := fun he => by
    have := congrArg Prod.snd he
    simp only at this
    omega
  obtain ⟨hqs, hcen⟩ := isQuasisimple_statedSU_of_card (F := K) (p := p) (f := f) hF hd hnq
  exact ⟨hqs.1, hcen.trans (unitaryScalars_eq h (by omega)).symm⟩

@[expose] noncomputable def unitaryConjHom {d : ℕ} (A : GL (Fin d) K) (σ : K ≃+* K)
    (hA : ∀ g : unitarySU p f K d,
      A * glAut σ (g : GL (Fin d) K) * A⁻¹ ∈ unitarySU p f K d) :
    unitarySU p f K d →* unitarySU p f K d where
  toFun g := ⟨A * glAut σ (g : GL (Fin d) K) * A⁻¹, hA g⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g₁ g₂ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]
    group

theorem coe_unitaryConjHom {d : ℕ} (A : GL (Fin d) K) (σ : K ≃+* K)
    (hA : ∀ g : unitarySU p f K d,
      A * glAut σ (g : GL (Fin d) K) * A⁻¹ ∈ unitarySU p f K d) (g : unitarySU p f K d) :
    ((unitaryConjHom A σ hA g : unitarySU p f K d) : GL (Fin d) K) =
      A * glAut σ (g : GL (Fin d) K) * A⁻¹ :=
  rfl

theorem exists_lift_unitarySU (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {d : ℕ}
    (hd : 3 ≤ d) {X : Type} [Group X] (θ : unitarySU p f K d →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (unitarySU p f K d))
    (σ : X ≃* X) :
    ∃ (A : GL (Fin d) K) (φ : K ≃+* K)
      (hA : ∀ g : unitarySU p f K d,
        A * glAut φ (g : GL (Fin d) K) * A⁻¹ ∈ unitarySU p f K d),
      ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1 ∧
        (∀ g : unitarySU p f K d, θ (unitaryConjHom A φ hA g) = σ (θ g)) ∧
        ((∀ x, σ (σ x) = x) →
          (φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c) ∧
            (unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA) = MonoidHom.id _) := by
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ d = 2 * r + ε := ⟨d / 2, d % 2, by omega, by omega⟩
  obtain ⟨hperf, hcen⟩ := isPerfect_and_center_unitarySU h hq hd
  have := hperf
  obtain ⟨β, hβ, hβinv⟩ := exists_mulEquiv_of_central_cover
    (unitaryProj_surjective h (2 * r + ε)) (by rw [ker_unitaryProj, hcen]) hθ hker σ
  obtain ⟨φ, A, hAu, hAg, hφ⟩ := exists_unitary_semilinear_psu h hp (by omega) hε hd β
  have hlift := hβ (unitaryConjHom A φ fun g => (hAg g).1) fun x => ((hAg x).2).symm
  exact ⟨A, φ, fun g => (hAg g).1, hAu, hlift, fun hσ =>
    ⟨hφ (hβinv hσ), lift_comp_self_eq_id hker hσ hlift⟩⟩

end Model

section Statement

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def suEquivUnitarySU (hK : Nat.card K = (p ^ f) ^ 2) (d : ℕ) :
    Su K p f d ≃* unitarySU p f K d :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU hK d)

variable {K p f}

theorem coe_suEquivUnitarySU (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ} (x : Su K p f d) :
    ((suEquivUnitarySU K p f hK d x : unitarySU p f K d) : GL (Fin d) K) = (x : GL (Fin d) K) :=
  rfl

theorem coe_suEquivUnitarySU_symm (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ}
    (x : unitarySU p f K d) :
    (((suEquivUnitarySU K p f hK d).symm x : Su K p f d) : GL (Fin d) K) = (x : GL (Fin d) K) :=
  rfl

variable (K p f)

@[expose] def UnitaryAutClassification (d : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (θ : Su K p f d →* X), Function.Surjective θ →
    θ.ker ≤ Subgroup.center (Su K p f d) → ∀ σ : X ≃* X,
    ∃ (α : Su K p f d →* Su K p f d) (g : GL (Fin d) K) (φ : K ≃+* K),
      (∀ x, θ (α x) = σ (θ x)) ∧
      ∀ x, ((α x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (g : Matrix (Fin d) (Fin d) K) *
          φ.mapMatrix ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)

variable {K p f}

theorem unitaryAutClassification_isometry_of_card (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {d : ℕ} (hd : 3 ≤ d) (X : Type) [Group X] (θ : Su K p f d →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (Su K p f d)) (σ : X ≃* X) :
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
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨e, he⟩ : ∃ e : Su K p f d ≃* unitarySU p f K d,
      ∀ x, ((e x : unitarySU p f K d) : GL (Fin d) K) = (x : GL (Fin d) K) :=
    ⟨suEquivUnitarySU K p f hK d, fun x => rfl⟩
  have he' : ∀ y : unitarySU p f K d, ((e.symm y : Su K p f d) : GL (Fin d) K) =
      (y : GL (Fin d) K) := fun y => by rw [← he, MulEquiv.apply_symm_apply]
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ := exists_lift_unitarySU h hp2 hq hd
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

theorem unitaryAutClassification_of_card (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {d : ℕ} (hd : 3 ≤ d) : UnitaryAutClassification K p f d := by
  intro X _ θ hθ hker σ
  obtain ⟨α, g, φ, h1, h2, -⟩ :=
    unitaryAutClassification_isometry_of_card hK hp2 hq hd X θ hθ hker σ
  exact ⟨α, g, φ, h1, h2⟩

end Statement

section Galois

variable {p f : ℕ} [Fact p.Prime]

theorem card_galoisField_two_mul_eq (hq : 5 ≤ p ^ f) :
    Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]

theorem unitaryAutClassification (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {d : ℕ} (hd : 3 ≤ d) :
    UnitaryAutClassification (GaloisField p (2 * f)) p f d :=
  unitaryAutClassification_of_card (card_galoisField_two_mul_eq hq) hp2 hq hd

theorem unitaryAutClassification_isometry (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {d : ℕ} (hd : 3 ≤ d)
    (X : Type) [Group X] (θ : Su (GaloisField p (2 * f)) p f d →* X)
    (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f d)) (σ : X ≃* X) :
    ∃ (α : Su (GaloisField p (2 * f)) p f d →* Su (GaloisField p (2 * f)) p f d)
      (g : GL (Fin d) (GaloisField p (2 * f)))
      (φ : GaloisField p (2 * f) ≃+* GaloisField p (2 * f)),
      (∀ x, θ (α x) = σ (θ x)) ∧
      (∀ x, ((α x : GL (Fin d) (GaloisField p (2 * f))) :
          Matrix (Fin d) (Fin d) (GaloisField p (2 * f))) =
        (g : Matrix (Fin d) (Fin d) (GaloisField p (2 * f))) *
          φ.mapMatrix ((x : GL (Fin d) (GaloisField p (2 * f))) :
            Matrix (Fin d) (Fin d) (GaloisField p (2 * f))) *
            ((g⁻¹ : GL (Fin d) (GaloisField p (2 * f))) :
              Matrix (Fin d) (Fin d) (GaloisField p (2 * f)))) ∧
      ((g : Matrix (Fin d) (Fin d) (GaloisField p (2 * f))).map
          (unitaryInvolution (GaloisField p (2 * f)) p f))ᵀ *
        (g : Matrix (Fin d) (Fin d) (GaloisField p (2 * f))) = 1 ∧
      ((∀ x, σ (σ x) = x) →
        (φ = RingEquiv.refl (GaloisField p (2 * f)) ∨
          φ = unitaryInvolution (GaloisField p (2 * f)) p f) ∧ α.comp α = MonoidHom.id _) :=
  unitaryAutClassification_isometry_of_card (card_galoisField_two_mul_eq hq) hp2 hq hd X θ hθ
    hker σ

end Galois

end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
