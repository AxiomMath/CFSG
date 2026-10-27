module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticD4
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality

public section

namespace CFSG.ClassicalInvolution.NDB.ExoticModel

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace SL3

variable {F : Type} [Field F]

@[expose] def s : SL(2, F) :=
  ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def u₁ : SL(3, F) :=
  blockSL F 3 2 0 (by omega) s

@[expose] def u₂ : SL(3, F) :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

@[expose] def u₃ : SL(3, F) :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

@[expose] def π : SL(3, F) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def e₀₁ : SL(3, F) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def e₀₂ : SL(3, F) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_u₁ :
    ((u₁ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [u₁, coe_blockSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s, Phan.blockMat_apply]

theorem u₁_mem : (u₁ : SL(3, F)) ∈ B12 F := ⟨s, rfl⟩

theorem s_comm (A : SL(2, F)) : s * A = A * s := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [s, Matrix.mul_apply, Fin.sum_univ_two]

theorem u₁_comm {b : SL(3, F)} (hb : b ∈ B12 F) : u₁ * b = b * u₁ := by
  obtain ⟨A, rfl⟩ := hb
  rw [u₁, ← map_mul, ← map_mul, s_comm]

theorem u₁_sq : (u₁ : SL(3, F)) * u₁ = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_u₁]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem π_u₁ : (π : SL(3, F)) * u₁ = u₂ * π := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_u₁]
  fin_cases i <;> fin_cases j <;> simp [u₂, π, Matrix.mul_apply, Fin.sum_univ_three]

theorem π_u₂ : (π : SL(3, F)) * u₂ = u₃ * π := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [u₃, u₂, π, Matrix.mul_apply, Fin.sum_univ_three]

theorem u₁_u₂ : (u₁ : SL(3, F)) * u₂ = u₃ := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_u₁]
  fin_cases i <;> fin_cases j <;> simp [u₂, u₃, Matrix.mul_apply, Fin.sum_univ_three]

theorem u₂_u₁ : (u₂ : SL(3, F)) * u₁ = u₃ := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_u₁]
  fin_cases i <;> fin_cases j <;> simp [u₂, u₃, Matrix.mul_apply, Fin.sum_univ_three]

theorem u₁_not_mem_center (h2 : (2 : F) ≠ 0) : (u₁ : SL(3, F)) ∉ Subgroup.center SL(3, F) := by
  intro h
  have h1 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 2)
    ((Subgroup.mem_center_iff.mp h) e₀₂)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_u₁] at h1
  simp [e₀₂, Matrix.mul_apply, Fin.sum_univ_three] at h1
  apply h2
  linear_combination h1

theorem u₃_not_mem_center (h2 : (2 : F) ≠ 0) : (u₃ : SL(3, F)) ∉ Subgroup.center SL(3, F) := by
  intro h
  have h1 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 1)
    ((Subgroup.mem_center_iff.mp h) e₀₁)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [u₃, e₀₁, Matrix.mul_apply, Fin.sum_univ_three] at h1
  apply h2
  linear_combination h1

theorem conj_mem (c : SL(3, F)) :
    c⁻¹ * u₁ * c ∈ (B12 F).map (MulAut.conj c⁻¹).toMonoidHom :=
  ⟨u₁, u₁_mem, by simp⟩

theorem conj_comm (c : SL(3, F)) :
    ∀ y ∈ (B12 F).map (MulAut.conj c⁻¹).toMonoidHom, c⁻¹ * u₁ * c * y = y * (c⁻¹ * u₁ * c) := by
  rintro _ ⟨b, hb, rfl⟩
  have e : (MulAut.conj c⁻¹).toMonoidHom b = c⁻¹ * b * c := by simp
  rw [e]
  calc c⁻¹ * u₁ * c * (c⁻¹ * b * c) = c⁻¹ * (u₁ * b) * c := by group
    _ = c⁻¹ * (b * u₁) * c := by rw [u₁_comm hb]
    _ = c⁻¹ * b * c * (c⁻¹ * u₁ * c) := by group

end SL3

section Rel

variable {X Y : Type*} [Group X] [Group Y]

structure FrameRel (v κ : X) : Prop where
  sq : v * v = 1
  ne_one : v ≠ 1
  comm : v * (κ * v * κ⁻¹) = (κ * v * κ⁻¹) * v
  ne : κ * v * κ⁻¹ ≠ v
  sq_conj : (κ * κ) * v * (κ * κ)⁻¹ = v * (κ * v * κ⁻¹)

theorem map_comm (θ : X →* Y) {H : Subgroup X} {a : X} (h : ∀ y ∈ H, a * y = y * a) :
    ∀ y ∈ H.map θ, θ a * y = y * θ a := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, h y hy]

theorem FrameRel.conj {v κ : X} (h : FrameRel v κ) (g : X) :
    FrameRel (g * v * g⁻¹) (g * κ * g⁻¹) where
  sq := by
    calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  ne_one := fun e => h.ne_one (by
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group)
  comm := by
    calc g * v * g⁻¹ * (g * κ * g⁻¹ * (g * v * g⁻¹) * (g * κ * g⁻¹)⁻¹) =
        g * (v * (κ * v * κ⁻¹)) * g⁻¹ := by group
      _ = g * ((κ * v * κ⁻¹) * v) * g⁻¹ := by rw [h.comm]
      _ = _ := by group
  ne := fun e => h.ne (by
    have e' : g * (κ * v * κ⁻¹) * g⁻¹ = g * v * g⁻¹ := by
      calc g * (κ * v * κ⁻¹) * g⁻¹ = g * κ * g⁻¹ * (g * v * g⁻¹) * (g * κ * g⁻¹)⁻¹ := by group
        _ = g * v * g⁻¹ := e
    exact mul_left_cancel (mul_right_cancel e'))
  sq_conj := by
    calc g * κ * g⁻¹ * (g * κ * g⁻¹) * (g * v * g⁻¹) * (g * κ * g⁻¹ * (g * κ * g⁻¹))⁻¹ =
        g * ((κ * κ) * v * (κ * κ)⁻¹) * g⁻¹ := by group
      _ = g * (v * (κ * v * κ⁻¹)) * g⁻¹ := by rw [h.sq_conj]
      _ = _ := by group

theorem frameRel_sl3 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (θ : SL(3, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) (c : SL(3, F)) :
    FrameRel (θ (c⁻¹ * SL3.u₁ * c)) (θ (c⁻¹ * SL3.π * c)) := by
  have hc : ∀ a b : SL(3, F), θ (c⁻¹ * a * c) * θ (c⁻¹ * b * c) = θ (c⁻¹ * (a * b) * c) := by
    intro a b
    rw [← map_mul]
    congr 1
    group
  have hinv : ∀ a : SL(3, F), (θ (c⁻¹ * a * c))⁻¹ = θ (c⁻¹ * a⁻¹ * c) := by
    intro a
    rw [← map_inv]
    congr 1
    group
  have hπ₁ : SL3.π * SL3.u₁ * SL3.π⁻¹ = (SL3.u₂ : SL(3, F)) := by
    rw [SL3.π_u₁]
    group
  have hπ₂ : SL3.π * SL3.u₂ * SL3.π⁻¹ = (SL3.u₃ : SL(3, F)) := by
    rw [SL3.π_u₂]
    group
  have hκv : θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹ =
      θ (c⁻¹ * SL3.u₂ * c) := by
    rw [hinv, hc, hc, hπ₁]
  have hcen : ∀ a : SL(3, F), a ∉ Subgroup.center SL(3, F) → θ (c⁻¹ * a * c) ≠ 1 := by
    intro a ha h1
    apply ha
    have hmem : c⁻¹ * a * c ∈ Subgroup.center SL(3, F) := hker (MonoidHom.mem_ker.mpr h1)
    have e : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
    rw [e]
    exact (inferInstance : (Subgroup.center SL(3, F)).Normal).conj_mem _ hmem c
  refine ⟨?_, hcen _ (SL3.u₁_not_mem_center h2), ?_, ?_, ?_⟩
  · rw [hc, SL3.u₁_sq]
    simp
  · rw [hκv, hc, hc, SL3.u₁_u₂, SL3.u₂_u₁]
  · rw [hκv]
    intro e
    apply hcen _ (SL3.u₃_not_mem_center h2)
    rw [← SL3.u₁_u₂, ← hc, e, hc, SL3.u₁_sq]
    simp
  · have hκw : θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₂ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹ =
        θ (c⁻¹ * SL3.u₃ * c) := by
      rw [hinv, hc, hc, hπ₂]
    calc θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) *
          (θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.π * c))⁻¹ =
        θ (c⁻¹ * SL3.π * c) * (θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) *
          (θ (c⁻¹ * SL3.π * c))⁻¹) * (θ (c⁻¹ * SL3.π * c))⁻¹ := by group
      _ = θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₂ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹ := by
        rw [hκv]
      _ = θ (c⁻¹ * SL3.u₃ * c) := hκw
      _ = θ (c⁻¹ * SL3.u₁ * c) * θ (c⁻¹ * SL3.u₂ * c) := by rw [hc, SL3.u₁_u₂]
      _ = _ := by rw [hκv]

end Rel

section Model

variable {p : ℕ} [Fact p.Prime]

theorem exists_sl3 {t : StatedLieTag} {n e : ℕ} (ht : t = .G2 ∨ t = .trialityD4)
    (hadm : StatedLieAdmissible t n p e) :
    ∃ (θ : SL(3, GaloisField p e) →* (modelUniv t n p e Fact.out).K) (c : SL(3, GaloisField p e)),
      θ.ker ≤ Subgroup.center SL(3, GaloisField p e) ∧
        ((B12 (GaloisField p e)).map (MulAut.conj c⁻¹).toMonoidHom).map θ ∈
          fundamentalSubgroups t (modelUniv t n p e Fact.out).D := by
  rcases ht with rfl | rfl
  · have hγ := ModelFacts.isLongestRoot_single .G2 n p e Fact.out trivial hadm Balance.g2Long rfl
    obtain ⟨δ, hδ, -, W, θ, c, -, hker, hUV⟩ := Balance.exists_standardPair_partner_g2 hadm hγ
    refine ⟨θ, c, hker, ?_⟩
    rcases hUV with ⟨hU, -⟩ | ⟨hU, -⟩
    · rw [hU]
      exact ⟨1, _, Or.inl hγ, (conjSub_one _).symm⟩
    · rw [hU]
      exact ⟨1, _, Or.inl hδ, (conjSub_one _).symm⟩
  · let k : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank :=
      CFSG.LieType.Steinberg.TwistedD4.ng 0
    have hγ : IsLongestRoot (modelUniv .trialityD4 n p e Fact.out).D (Pi.single k 1) :=
      ModelFacts.isLongestRoot_single .trialityD4 n p e Fact.out trivial hadm k rfl
    obtain ⟨δ, hδ, -, W, θ, c, -, hker, hUV⟩ :=
      Balance.exists_standardPair_partner_trialityD4 hadm hγ
    refine ⟨θ, c, hker, ?_⟩
    rcases hUV with ⟨hU, -⟩ | ⟨hU, -⟩
    · rw [hU]
      exact ⟨1, _, Or.inl hγ, (conjSub_one _).symm⟩
    · rw [hU]
      exact ⟨1, _, Or.inl hδ, (conjSub_one _).symm⟩

theorem exists_frameRel (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .G2 ∨ t = .trialityD4) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {x₀ : (modelUniv t n p e Fact.out).K} (hx₀R : x₀ ∈ R₀) (hx₀c : ∀ r ∈ R₀, x₀ * r = r * x₀)
    (hx₀2 : x₀ * x₀ = 1) (hx₀1 : x₀ ≠ 1) :
    ∃ k : (modelUniv t n p e Fact.out).K, FrameRel x₀ k := by
  obtain ⟨θ, c, hker, hU⟩ := exists_sl3 ht hadm
  have hrel := frameRel_sl3 (ModelFacts.two_ne_zero_galoisField e hp2) θ hker c
  have hvU := Subgroup.mem_map_of_mem θ (SL3.conj_mem c)
  have hvc := map_comm θ (SL3.conj_comm (F := GaloisField p e) c)
  obtain ⟨g, hg⟩ := Balance.Bootstrap.twoClassInvolutionsConj p t n e hp2 ht hadm _ hU R₀ hR₀ _ hvU
    x₀ hx₀R hrel.sq hx₀2 hrel.ne_one hx₀1 hvc hx₀c
  refine ⟨g * θ (c⁻¹ * SL3.π * c) * g⁻¹, ?_⟩
  have h := hrel.conj g
  rwa [hg] at h

end Model

end CFSG.ClassicalInvolution.NDB.ExoticModel
