module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutAmbient
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainUMat
import CFSG.Assembly.ComponentTypeDefs
import CFSG.ClassicalInvolution.Models.Transfer.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NT

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
open scoped MatrixGroups

section Classification

variable {p f : ℕ} {K : Type} [Field K]

theorem isPerfect_and_center_unitarySU_of_odd (h : UnitaryFieldData p f K) (hp : p ≠ 2) {d : ℕ}
    (hd : 3 ≤ d) :
    Group.IsPerfect (unitarySU p f K d) ∧
      Subgroup.center (unitarySU p f K d) = unitaryScalars h d := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hF : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : (d, p ^ f) ≠ (3, 2) := fun he => by
    have h2 : p ^ f = 2 := congrArg Prod.snd he
    have hdvd : p ∣ 2 := h2 ▸ dvd_pow_self p (by have := h.one_le; omega)
    exact hp ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 hdvd)
  obtain ⟨hqs, hcen⟩ := isQuasisimple_statedSU_of_card (F := K) (p := p) (f := f) hF hd hnq
  exact ⟨hqs.1, hcen.trans (unitaryScalars_eq h (by omega)).symm⟩

theorem exists_lift_unitarySU_of_odd (h : UnitaryFieldData p f K) (hp : p ≠ 2) {d : ℕ}
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
  obtain ⟨hperf, hcen⟩ := isPerfect_and_center_unitarySU_of_odd h hp hd
  have := hperf
  obtain ⟨β, hβ, hβinv⟩ := exists_mulEquiv_of_central_cover
    (unitaryProj_surjective h (2 * r + ε)) (by rw [ker_unitaryProj, hcen]) hθ hker σ
  obtain ⟨φ, A, hAu, hAg, hφ⟩ := exists_unitary_semilinear_psu h hp (by omega) hε hd β
  have hlift := hβ (unitaryConjHom A φ fun g => (hAg g).1) fun x => ((hAg x).2).symm
  exact ⟨A, φ, fun g => (hAg g).1, hAu, hlift, fun hσ =>
    ⟨hφ (hβinv hσ), lift_comp_self_eq_id hker hσ hlift⟩⟩

end Classification

section Isometry

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem unitaryAutClassification_isometry_of_odd (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {d : ℕ} (hd : 3 ≤ d) (X : Type) [Group X] (θ : Su K p f d →* X)
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
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨e, he⟩ : ∃ e : Su K p f d ≃* unitarySU p f K d,
      ∀ x, ((e x : unitarySU p f K d) : GL (Fin d) K) = (x : GL (Fin d) K) :=
    ⟨suEquivUnitarySU K p f hK d, fun x => rfl⟩
  have he' : ∀ y : unitarySU p f K d, ((e.symm y : Su K p f d) : GL (Fin d) K) =
      (y : GL (Fin d) K) := fun y => by rw [← he, MulEquiv.apply_symm_apply]
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ := exists_lift_unitarySU_of_odd h hp2 hd
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

theorem unitaryAutClassification_ambient_of_odd (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {d : ℕ} (hd : 3 ≤ d) {Y : Type} [Group Y] (θ : Su K p f d →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f d)) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range) :
    ∃ (α : Su K p f d →* Su K p f d) (g : GL (Fin d) K) (φ : K ≃+* K),
      (∀ x, θ (α x) = σ (θ x)) ∧
      (∀ x, ((α x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (g : Matrix (Fin d) (Fin d) K) *
          φ.mapMatrix ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ∧
      ((g : Matrix (Fin d) (Fin d) K).map (unitaryInvolution K p f))ᵀ *
        (g : Matrix (Fin d) (Fin d) K) = 1 ∧
      (φ = RingEquiv.refl K ∨ φ = unitaryInvolution K p f) ∧ α.comp α = MonoidHom.id _ := by
  have hQ : ∀ y ∈ θ.range, σ y ∈ θ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  have hσ' : ∀ y, restrictInvolution σ hσ θ.range hQ (restrictInvolution σ hσ θ.range hQ y) =
      y := fun y => Subtype.ext (by simp only [coe_restrictInvolution]; exact hσ _)
  obtain ⟨α, g, φ, h1, h2, h3, h4⟩ := unitaryAutClassification_isometry_of_odd hK hp2 hf hd
    θ.range θ.rangeRestrict θ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) (restrictInvolution σ hσ θ.range hQ)
  obtain ⟨h5, h6⟩ := h4 hσ'
  exact ⟨α, g, φ, fun x => congrArg Subtype.val (h1 x), h2, h3, h5, h6⟩

end Isometry

section Center

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem center_su3_eq_bot (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h3 : ¬ 3 ∣ p ^ f + 1) : Subgroup.center (Su K p f 3) = ⊥ := by
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨-, hcen⟩ := isPerfect_and_center_unitarySU_of_odd h hp2 (le_refl 3)
  have hsc : unitaryScalars h 3 = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [card_unitaryScalars h (by norm_num)]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  rw [hsc] at hcen
  refine le_antisymm (fun c hc => ?_) bot_le
  set e := suEquivUnitarySU K p f hK 3
  have hec : e c ∈ Subgroup.center (unitarySU p f K 3) := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact hc (e.symm g)
  rw [hcen, Subgroup.mem_bot] at hec
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hec, map_one])

end Center

end CFSG.ClassicalInvolution.Q3.Q3NT
