module

public import CFSG.ClassicalInvolution.SmallCases.NDBE1

public section

namespace CFSG.ClassicalInvolution.NDB.ExoticModel

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def SpinTag (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)

namespace SL3

variable {F : Type} [Field F]

@[expose] def s₀₁ : SL(2, F) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def e₁₂ : SL(3, F) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def m₁ : SL(3, F) :=
  ⟨!![1, 0, 0; 0, 1, -2; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def m₂ : SL(3, F) :=
  ⟨!![1, -2, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem e₀₁_eq : (e₀₁ : SL(3, F)) = blockSL F 3 2 0 (by omega) s₀₁ := by
  ext i j
  rw [coe_blockSL]
  fin_cases i <;> fin_cases j <;> simp [e₀₁, s₀₁, Phan.blockMat_apply]

theorem e₀₁_mem : (e₀₁ : SL(3, F)) ∈ B12 F := ⟨s₀₁, e₀₁_eq.symm⟩

theorem u₂_eq : (u₂ : SL(3, F)) = blockSL F 3 2 1 (by omega) s := by
  ext i j
  rw [coe_blockSL]
  fin_cases i <;> fin_cases j <;> simp [u₂, s, Phan.blockMat_apply]

theorem u₂_mem : (u₂ : SL(3, F)) ∈ B23 F := ⟨s, u₂_eq.symm⟩

theorem π_e₀₁ : (π : SL(3, F)) * e₀₁ = e₁₂ * π := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [π, e₀₁, e₁₂, Matrix.mul_apply, Fin.sum_univ_three]

theorem u₁_e₁₂ : (u₁ : SL(3, F)) * e₁₂ = m₁ * (e₁₂ * u₁) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_u₁]
  fin_cases i <;> fin_cases j <;> simp [e₁₂, m₁, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem u₂_e₀₁ : (u₂ : SL(3, F)) * e₀₁ = m₂ * (e₀₁ * u₂) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [u₂, e₀₁, m₂, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem u₃_e₀₁ : (u₃ : SL(3, F)) * e₀₁ = m₂ * (e₀₁ * u₃) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [u₃, e₀₁, m₂, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem m₁_not_mem_center (h2 : (2 : F) ≠ 0) : (m₁ : SL(3, F)) ∉ Subgroup.center SL(3, F) := by
  intro h
  have h1 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 2)
    ((Subgroup.mem_center_iff.mp h) e₀₁)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [m₁, e₀₁, Matrix.mul_apply, Fin.sum_univ_three] at h1
  exact h2 h1

theorem m₂_not_mem_center (h2 : (2 : F) ≠ 0) : (m₂ : SL(3, F)) ∉ Subgroup.center SL(3, F) := by
  intro h
  have h1 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 2)
    ((Subgroup.mem_center_iff.mp h) e₁₂)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [m₂, e₁₂, Matrix.mul_apply, Fin.sum_univ_three] at h1
  exact h2 h1

end SL3

theorem not_comm_sl3 {Y F : Type*} [Group Y] [Field F] (θ : SL(3, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) (c : SL(3, F)) {a b m : SL(3, F)}
    (h : a * b = m * (b * a)) (hm : m ∉ Subgroup.center SL(3, F)) :
    θ (c⁻¹ * a * c) * θ (c⁻¹ * b * c) ≠ θ (c⁻¹ * b * c) * θ (c⁻¹ * a * c) := by
  intro e
  apply hm
  have e1 : θ (c⁻¹ * m * c) = 1 := by
    have e2 : c⁻¹ * m * c = (c⁻¹ * a * c) * (c⁻¹ * b * c) * ((c⁻¹ * b * c) * (c⁻¹ * a * c))⁻¹ := by
      rw [show (c⁻¹ * a * c) * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c by group, h]
      group
    have e4 : θ ((c⁻¹ * a * c) * (c⁻¹ * b * c) * ((c⁻¹ * b * c) * (c⁻¹ * a * c))⁻¹) =
        θ (c⁻¹ * a * c) * θ (c⁻¹ * b * c) * (θ (c⁻¹ * b * c) * θ (c⁻¹ * a * c))⁻¹ := by
      simp only [map_mul, map_inv]
    rw [e2, e4, e, mul_inv_cancel]
  have hmem : c⁻¹ * m * c ∈ Subgroup.center SL(3, F) := hker (MonoidHom.mem_ker.mpr e1)
  have e3 : m = c * (c⁻¹ * m * c) * c⁻¹ := by group
  rw [e3]
  exact (inferInstance : (Subgroup.center SL(3, F)).Normal).conj_mem _ hmem c

variable {p : ℕ} [Fact p.Prime]

section Conj

variable {Y : Type*} {F : Type} [Group Y] [Field F] (θ : SL(3, F) →* Y) (c : SL(3, F))

theorem thetaC_mul (a b : SL(3, F)) :
    θ (c⁻¹ * a * c) * θ (c⁻¹ * b * c) = θ (c⁻¹ * (a * b) * c) := by
  rw [← map_mul]
  congr 1
  group

theorem thetaC_inv (a : SL(3, F)) : (θ (c⁻¹ * a * c))⁻¹ = θ (c⁻¹ * a⁻¹ * c) := by
  rw [← map_inv]
  congr 1
  group

theorem thetaC_π_u₁ :
    θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹ =
      θ (c⁻¹ * SL3.u₂ * c) := by
  rw [thetaC_inv, thetaC_mul, thetaC_mul,
    show SL3.π * SL3.u₁ * SL3.π⁻¹ = (SL3.u₂ : SL(3, F)) by rw [SL3.π_u₁]; group]

theorem thetaC_π_e₁₂ :
    (θ (c⁻¹ * SL3.π * c))⁻¹ * θ (c⁻¹ * SL3.e₁₂ * c) * θ (c⁻¹ * SL3.π * c) =
      θ (c⁻¹ * SL3.e₀₁ * c) := by
  rw [thetaC_inv, thetaC_mul, thetaC_mul,
    show SL3.π⁻¹ * SL3.e₁₂ * SL3.π = (SL3.e₀₁ : SL(3, F)) by
      rw [mul_assoc, ← SL3.π_e₀₁]; group]

end Conj

theorem conj_ne_conj {X : Type*} [Group X] (g : X) {a b : X} (h : a * b ≠ b * a) :
    g * a * g⁻¹ * (g * b * g⁻¹) ≠ g * b * g⁻¹ * (g * a * g⁻¹) := by
  intro e
  apply h
  calc a * b = g⁻¹ * (g * a * g⁻¹ * (g * b * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * b * g⁻¹ * (g * a * g⁻¹)) * g := by rw [e]
    _ = b * a := by group

theorem frame_of_sl3 {X F : Type} [Group X] [Field F] (h2 : (2 : F) ≠ 0) (θ : SL(3, F) →* X)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) (c : SL(3, F)) {R₀ : Subgroup X} {x₀ : X}
    (hx₀ : IsUniqueInvolution R₀ x₀) (g : X)
    (hg : R₀ = conjSub g (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ)) :
    g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹ = x₀ ∧
      g * θ (c⁻¹ * SL3.π * c) * g⁻¹ * x₀ * (g * θ (c⁻¹ * SL3.π * c) * g⁻¹)⁻¹ =
        g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹ ∧
      FrameRel x₀ (g * θ (c⁻¹ * SL3.π * c) * g⁻¹) ∧
      (∃ r ∈ conjSub (g * θ (c⁻¹ * SL3.π * c) * g⁻¹) R₀, x₀ * r ≠ r * x₀) ∧
      (∃ r ∈ R₀, g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹ * r ≠ r * (g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹)) ∧
      (∃ r ∈ R₀, x₀ * (g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹) * r ≠
        r * (x₀ * (g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹))) := by
  have hrel := frameRel_sl3 h2 θ hker c
  have hmemU : ∀ {b : SL(3, F)}, b ∈ B12 F →
      θ (c⁻¹ * b * c) ∈ ((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    fun {b} hb => Subgroup.mem_map_of_mem θ ⟨b, hb, by simp⟩
  have hmemR : ∀ {b : SL(3, F)}, b ∈ B12 F → g * θ (c⁻¹ * b * c) * g⁻¹ ∈ R₀ := fun {b} hb => by
    rw [hg]
    exact conj_mem_conjSub (hmemU hb)
  have hgv : g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹ = x₀ := by
    rcases hx₀.unique _ (hmemR SL3.u₁_mem) (by
      rw [show g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹ * (g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹) =
        g * (θ (c⁻¹ * SL3.u₁ * c) * θ (c⁻¹ * SL3.u₁ * c)) * g⁻¹ by group, hrel.sq]
      group) with h | h
    · exfalso
      apply hrel.ne_one
      calc θ (c⁻¹ * SL3.u₁ * c) = g⁻¹ * (g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
  set κ := θ (c⁻¹ * SL3.π * c) with hκ
  have hk₂ : g * κ * g⁻¹ * x₀ * (g * κ * g⁻¹)⁻¹ = g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹ := by
    rw [← hgv, ← thetaC_π_u₁ θ c, ← hκ]
    group
  refine ⟨hgv, hk₂, ?_, ⟨g * θ (c⁻¹ * SL3.e₁₂ * c) * g⁻¹, ?_, ?_⟩,
    ⟨g * θ (c⁻¹ * SL3.e₀₁ * c) * g⁻¹, hmemR SL3.e₀₁_mem, ?_⟩,
    ⟨g * θ (c⁻¹ * SL3.e₀₁ * c) * g⁻¹, hmemR SL3.e₀₁_mem, ?_⟩⟩
  · rw [← hgv]
    exact hrel.conj g
  · rw [mem_conjSub_iff, hg, mem_conjSub_iff]
    have e1 : g⁻¹ * ((g * κ * g⁻¹)⁻¹ * (g * θ (c⁻¹ * SL3.e₁₂ * c) * g⁻¹) * (g * κ * g⁻¹)) * g =
        κ⁻¹ * θ (c⁻¹ * SL3.e₁₂ * c) * κ := by group
    rw [e1, hκ, thetaC_π_e₁₂]
    exact hmemU SL3.e₀₁_mem
  · rw [← hgv]
    exact conj_ne_conj g (not_comm_sl3 θ hker c SL3.u₁_e₁₂ (SL3.m₁_not_mem_center h2))
  · exact conj_ne_conj g (not_comm_sl3 θ hker c SL3.u₂_e₀₁ (SL3.m₂_not_mem_center h2))
  · rw [← hgv, show g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹ * (g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹) =
      g * θ (c⁻¹ * SL3.u₃ * c) * g⁻¹ by
        rw [show g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹ * (g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹) =
          g * (θ (c⁻¹ * SL3.u₁ * c) * θ (c⁻¹ * SL3.u₂ * c)) * g⁻¹ by group,
          thetaC_mul, SL3.u₁_u₂]]
    exact conj_ne_conj g (not_comm_sl3 θ hker c SL3.u₃_e₀₁ (SL3.m₂_not_mem_center h2))

end CFSG.ClassicalInvolution.NDB.ExoticModel
