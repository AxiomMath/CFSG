module

public import CFSG.GH74.KGroups.L3EpsUniBlock
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank CFSG.GH74.KGroups.L3Eps.Uni
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Cent

variable {p f : ℕ} {F : Type} [Field F]

@[expose] def CentOK (p f : ℕ) (Ω : Subgroup ↥(unitarySU p f F 3)) : Prop :=
  ∀ (B : GL (Fin 3) F) (σ : F ≃+* F),
    (∀ g ∈ Ω, ∃ c : Fˣ, B * glAut σ (g : GL (Fin 3) F) * B⁻¹ =
      (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c) →
    ∀ g ∈ Ω, B * glAut σ (g : GL (Fin 3) F) * B⁻¹ = (g : GL (Fin 3) F)

theorem scalar_injective_GL3 :
    Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Fˣ → GL (Fin 3) F) := by
  intro c d hcd
  have h1 := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F) 0 0) hcd
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.ext_iff] using h1

theorem centOK_of_perfect {Ω : Subgroup ↥(unitarySU p f F 3)} (hperf : Group.IsPerfect ↥Ω) :
    CentOK p f Ω := by
  classical
  intro B σ hyp g hg
  choose! c hc using hyp
  have hmul : ∀ x ∈ Ω, ∀ y ∈ Ω, c (x * y) = c x * c y := by
    intro x hx y hy
    have h1 := hc x hx
    have h2 := hc y hy
    have h3 := hc (x * y) (Ω.mul_mem hx hy)
    have h4 : (GeneralLinearGroup.scalar (Fin 3) (c (x * y)) : GL (Fin 3) F) =
        GeneralLinearGroup.scalar (Fin 3) (c x * c y) := by
      have : ((x * y : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) (c (x * y)) =
          ((x * y : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) (c x * c y) := by
        rw [← h3, Subgroup.coe_mul, map_mul]
        calc B * (glAut σ (x : GL (Fin 3) F) * glAut σ (y : GL (Fin 3) F)) * B⁻¹
            = (B * glAut σ (x : GL (Fin 3) F) * B⁻¹) * (B * glAut σ (y : GL (Fin 3) F) * B⁻¹) := by group
          _ = ((x : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) (c x)) *
              ((y : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) (c y)) := by rw [h1, h2]
          _ = (x : GL (Fin 3) F) * (y : GL (Fin 3) F) * (GeneralLinearGroup.scalar (Fin 3) (c x * c y)) := by
              have hcomm : GeneralLinearGroup.scalar (Fin 3) (c x) * (y : GL (Fin 3) F) =
                  (y : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) (c x) := by
                apply Units.ext
                rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
                exact (Matrix.scalar_commute (c x : F) (fun r => Commute.all _ r) _)
              calc ((x : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) (c x)) *
                    ((y : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) (c y))
                  = (x : GL (Fin 3) F) * (GeneralLinearGroup.scalar (Fin 3) (c x) * (y : GL (Fin 3) F)) *
                      GeneralLinearGroup.scalar (Fin 3) (c y) := by group
                _ = (x : GL (Fin 3) F) * ((y : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) (c x)) *
                      GeneralLinearGroup.scalar (Fin 3) (c y) := by rw [hcomm]
                _ = _ := by rw [map_mul]; group
      exact mul_left_cancel this
    exact scalar_injective_GL3 h4
  let cf : ↥Ω →* Fˣ := MonoidHom.mk' (fun x => c (x : ↥(unitarySU p f F 3)))
    (fun x y => hmul x x.2 y y.2)
  have hker : commutator ↥Ω ≤ cf.ker := Abelianization.commutator_subset_ker cf
  rw [hperf.commutator_eq_top] at hker
  have h1 : cf ⟨g, hg⟩ = 1 := hker (Subgroup.mem_top _)
  have hcg : c g = 1 := h1
  rw [hc g hg, hcg, map_one, mul_one]


theorem mem_unitaryScalars_of_scalar (h : UnitaryFieldData p f F) {g : ↥(unitarySU p f F 3)} {c : Fˣ}
    (hc : (g : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) c) : g ∈ unitaryScalars h 3 := by
  rw [unitaryScalars_eq h (by norm_num), Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  exact ⟨c, hc.symm⟩

theorem centOK_of_no_cube_roots (h : UnitaryFieldData p f F) {Ω : Subgroup ↥(unitarySU p f F 3)}
    (hno : ∀ c : Fˣ, c ^ 3 = 1 → c = 1) : CentOK p f Ω := by
  classical
  intro B σ hyp g hg
  obtain ⟨c, hc⟩ := hyp g hg
  have hdet1 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := det_matU_eq_one h g
  have hdg : Matrix.GeneralLinearGroup.det (g : GL (Fin 3) F) = 1 := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet1]; rfl)
  have hdσ : Matrix.GeneralLinearGroup.det (glAut σ (g : GL (Fin 3) F)) = 1 := by
    apply Units.ext
    have hmd := RingHom.map_det (σ : F →+* F) ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [RingHom.mapMatrix_apply, hdet1, map_one] at hmd
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_glAut]
    exact hmd.symm
  have hdc : Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c) = c ^ 3 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
  have h1 : Matrix.GeneralLinearGroup.det (B * glAut σ (g : GL (Fin 3) F) * B⁻¹) =
      Matrix.GeneralLinearGroup.det ((g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c) := by rw [hc]
  rw [map_mul, map_mul, map_mul, map_inv, hdσ, hdg, hdc] at h1
  have h2 : c ^ 3 = 1 := by
    have := h1
    simp at this
    exact this.symm
  rw [hno c h2, map_one, mul_one] at hc
  exact hc

end Cent

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
