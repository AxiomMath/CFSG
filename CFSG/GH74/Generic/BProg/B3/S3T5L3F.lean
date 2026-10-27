module

public import CFSG.GH74.Generic.BProg.B3.S3T5L3Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Field

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T5L3

open Matrix Subgroup CFSG CFSG.Assembly.Dichotomy CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Signalizer
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def fixField (σ : F ≃+* F) : Subfield F := (σ : F →+* F).eqLocusField (RingHom.id F)

@[expose] def omegaField (σ : F ≃+* F) : Subgroup SL(3, F) :=
  (SpecialLinearGroup.map (fixField σ).subtype).range

theorem mem_omegaField (σ : F ≃+* F) (g : SL(3, F)) :
    g ∈ omegaField σ ↔ SpecialLinearGroup.map σ.toRingHom g = g := by
  constructor
  · rintro ⟨g₀, rfl⟩
    ext i j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (g₀ i j).2
  · intro h
    have hent : ∀ i j, (g : Matrix (Fin 3) (Fin 3) F) i j ∈ fixField σ := fun i j => by
      have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F) i j) h
      have h2 : σ ((g : Matrix (Fin 3) (Fin 3) F) i j) = (g : Matrix (Fin 3) (Fin 3) F) i j := by
        simpa using h1
      exact h2
    let M₀ : Matrix (Fin 3) (Fin 3) (fixField σ) := Matrix.of fun i j => ⟨_, hent i j⟩
    have hM : (fixField σ).subtype.mapMatrix M₀ = g := by ext i j; rfl
    have hdet : M₀.det = 1 := by
      apply Subtype.val_injective
      change (fixField σ).subtype M₀.det = (fixField σ).subtype 1
      rw [RingHom.map_det, hM, map_one]
      exact g.2
    exact ⟨⟨M₀, hdet⟩, Subtype.ext hM⟩

@[expose] def trSL (i j : Fin 3) (hij : i ≠ j) (c : F) : SL(3, F) :=
  ⟨transvection i j c, det_transvection_of_ne i j hij c⟩

theorem map_transvection (ρ : F ≃+* F) (i j : Fin 3) (c : F) :
    (transvection i j c).map ρ = transvection i j (ρ c) := by
  ext a b
  simp only [transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem trSL_mem_omegaField (σ : F ≃+* F) (i j : Fin 3) (hij : i ≠ j) {c : F} (hc : σ c = c) :
    trSL i j hij c ∈ omegaField σ := by
  rw [mem_omegaField]
  ext a b
  change ((transvection i j c).map σ) a b = transvection i j c a b
  rw [map_transvection, hc]

@[expose] def trSet : Set SL(3, F) := {g | ∃ (i j : Fin 3) (hij : i ≠ j), g = trSL i j hij 1}

theorem trSet_subset (σ : F ≃+* F) : trSet ⊆ (omegaField σ : Set SL(3, F)) := by
  rintro _ ⟨i, j, hij, rfl⟩
  exact trSL_mem_omegaField σ i j hij (map_one σ)

theorem trSet_map (ρ : F ≃+* F) : ∀ g ∈ (trSet : Set SL(3, F)),
    (g : Matrix (Fin 3) (Fin 3) F).map ρ = g := by
  rintro _ ⟨i, j, hij, rfl⟩
  change (transvection i j 1).map ρ = transvection i j 1
  rw [map_transvection, map_one]

theorem trSet_comm (T : Matrix (Fin 3) (Fin 3) F)
    (hT : ∀ g ∈ (trSet : Set SL(3, F)),
      T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) :
    ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F) :=
  scalar_of_commute_transvection fun i j hij => hT _ ⟨i, j, hij, rfl⟩

theorem isSimpleGroup_proj_omegaField (σ : F ≃+* F) :
    IsSimpleGroup ((omegaField σ).map (LinearFlag.proj 3 F)) := by
  let ρ0 : SL(3, fixField σ) →* projectiveSL 3 F :=
    (LinearFlag.proj 3 F).comp (SpecialLinearGroup.map (fixField σ).subtype)
  have hker : scalars 3 (fixField σ) ≤ ρ0.ker := by
    intro s hs
    obtain ⟨c, hc3, hcm⟩ := mem_scalars.1 hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff]
    refine mem_scalars.2 ⟨Units.map (fixField σ).subtype.toMonoidHom c, ?_, ?_⟩
    · rw [← map_pow, hc3, map_one]
    · ext i j
      have h1 := congrFun (congrFun hcm i) j
      rw [SpecialLinearGroup.map_apply_coe]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [h1]
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, hij]
  let ρ1 : projectiveSL 3 (fixField σ) →* projectiveSL 3 F :=
    QuotientGroup.lift (scalars 3 (fixField σ)) ρ0 hker
  have hrange : ρ1.range = (omegaField σ).map (LinearFlag.proj 3 F) := by
    rw [omegaField, ← MonoidHom.range_comp]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := proj_surjective 3 (fixField σ) y
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨LinearFlag.proj 3 (fixField σ) g, rfl⟩
  have := Odd87.isSimpleGroup_projectiveSL3_fl3 (fixField σ)
  have hnt : Nontrivial ρ1.range := by
    refine ⟨⟨⟨LinearFlag.proj 3 F (trSL 0 1 (by decide) 1), ?_⟩, 1, fun h => ?_⟩⟩
    · rw [hrange]
      exact ⟨_, trSL_mem_omegaField σ 0 1 (by decide) (map_one σ), rfl⟩
    · have h1 := proj_eq_one_iff.1 (congrArg Subtype.val h)
      obtain ⟨c, -, hc⟩ := mem_scalars.1 h1
      have h01 := congrFun (congrFun hc 0) 1
      simp [trSL, transvection, Matrix.scalar_apply] at h01
  rw [← hrange]
  exact IsSimpleGroup.isSimpleGroup_of_surjective ρ1.rangeRestrict ρ1.rangeRestrict_surjective

variable [Finite F]

theorem oddCore_bot_linField {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (e₀ : K ≃* projectiveSL 3 F)
    (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) {H : Subgroup (MulAut K)}
    (hH : (MulAut.conj : K →* MulAut K).range ≤ H) (u : H) (hu : u * u = 1)
    (A : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hα : MulAut.congr e₀ (u : MulAut K) = conjAut 3 F A * fieldAut 3 F σ) :
    involutionOddCore u = ⊥ := by
  have hu' : (u : MulAut K) * u = 1 := congrArg Subtype.val hu
  have hsq : (conjAut 3 F A * fieldAut 3 F σ) ^ 2 = 1 := by
    rw [← hα, sq, ← map_mul, hu', map_one]
  obtain ⟨-, -, H₀, hH₀⟩ := linear_field_involution_descent hp hf hcard le_rfl A σ hσ hsq
  set c := conjAut 3 F H₀ with hc
  have hσσ : σ * σ = 1 := by
    have h2 : fieldAut 3 F σ * fieldAut 3 F σ = 1 := by
      have h := hsq
      rw [hH₀, sq] at h
      calc fieldAut 3 F σ * fieldAut 3 F σ
          = c⁻¹ * ((c * fieldAut 3 F σ * c⁻¹) * (c * fieldAut 3 F σ * c⁻¹)) * c := by group
        _ = 1 := by rw [h]; group
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) 1 (σ * σ)
      (by rw [map_one, one_mul, map_mul, h2])).1
  let e₁ : K ≃* projectiveSL 3 F := e₀.trans c⁻¹
  have hγ : MulAut.congr e₁ (u : MulAut K) = fieldAut 3 F σ := by
    have h1 : MulAut.congr e₁ (u : MulAut K) = c⁻¹ * MulAut.congr e₀ (u : MulAut K) * c := by
      ext y; rfl
    rw [h1, hα, hH₀]
    group
  have hperf : Group.IsPerfect (omegaField σ) := by
    have : Group.IsPerfect (SpecialLinearGroup (Fin 3) (fixField σ)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    exact Group.IsPerfect.range _
  have := isSimpleGroup_proj_omegaField σ
  refine involutionOddCore_eq_bot_of_proj e₁ hZ hH u hγ (SpecialLinearGroup.map σ.toRingHom)
    (fieldAut_proj σ) (omegaField σ) (mem_omegaField σ) hperf (trSet_subset σ) trSet_map
    trSet_comm fun τ m hm hτm hτΩ => ?_
  refine ringEquiv_eq_one_of_fix_fixed hp hf hcard hσ hσσ hm hτm fun x hx => ?_
  have h := hτΩ _ (trSL_mem_omegaField σ 0 1 (by decide) hx)
  have h01 := congrFun (congrFun h 0) 1
  simpa [trSL, transvection, Matrix.single_apply] using h01

end CFSG.GH74.Generic.BProg.B3.S3T5L3
