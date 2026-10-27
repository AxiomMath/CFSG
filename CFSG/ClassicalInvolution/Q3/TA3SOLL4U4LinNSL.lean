module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClL4Comm
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowS

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped MatrixGroups

variable {K : Type} [Field K] (ν : Kˣ) [Fact (¬ IsSquare (ν : K))]
  (Ψ : (Fin 2 → extension (ν : K)) ≃ₗ[K] (Fin 4 → K))

@[expose] noncomputable def rowSPiSL : SL(2, extension (ν : K)) →* SL(4, K) where
  toFun x := ⟨((rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) : GL (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K), by
      rw [det_rowSPi, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, x.2, map_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    change ((rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL (x * y)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
      ((rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) *
      ((rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL y) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    rw [map_mul, map_mul, Units.val_mul])

theorem toGL_rowSPiSL (x : SL(2, extension (ν : K))) :
    Matrix.SpecialLinearGroup.toGL (rowSPiSL ν Ψ x) =
      rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) :=
  Units.ext rfl

theorem coe_rowSPiSL (x : SL(2, extension (ν : K))) :
    ((rowSPiSL ν Ψ x : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      ((rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) :=
  rfl

theorem ker_proj_rowSPiSL [Finite K] :
    ((proj 4 K).comp (rowSPiSL ν Ψ)).ker = Subgroup.center SL(2, extension (ν : K)) := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff, ← scalars_eq_center,
    mem_scalars_two_iff, mem_scalars]
  constructor
  · rintro ⟨c, -, hc⟩
    have h1 : rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) =
        GeneralLinearGroup.scalar (Fin 4) c := Units.ext (by
      rw [GeneralLinearGroup.coe_scalar]
      exact hc)
    rw [← rowSPi_scalar ν Ψ c] at h1
    have h2 := rowSPi_injective ν Ψ h1
    have hx : x ∈ scalars 2 (extension (ν : K)) := by
      refine ⟨Units.map (algebraMap K (extension (ν : K))).toMonoidHom c, ?_, ?_⟩
      · have hdet := congrArg GeneralLinearGroup.det h2
        rw [GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
        have hdet1 : GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL x) = 1 :=
          Units.ext (by rw [GeneralLinearGroup.val_det_apply,
            Matrix.SpecialLinearGroup.coe_GL_coe_matrix, x.2, Units.val_one])
        rw [hdet1] at hdet
        exact hdet.symm
      · have := congrArg (fun g : GL (Fin 2) (extension (ν : K)) =>
          (g : Matrix (Fin 2) (Fin 2) (extension (ν : K)))) h2
        simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
          using this
    exact (mem_scalars_two_iff x).mp hx
  · rintro (rfl | rfl)
    · exact ⟨1, one_pow 4, by simp⟩
    · refine ⟨-1, Even.neg_one_pow ⟨2, rfl⟩, ?_⟩
      rw [coe_rowSPiSL, toGL_neg_one, rowSPi_scalar, GeneralLinearGroup.coe_scalar]

theorem exists_conj_rowSPi {Y : GL (Fin 4) K} {ζ : K} (hζ : ζ = 1 ∨ ζ = -1)
    (hY : (Y : Matrix (Fin 4) (Fin 4) K) *
      ((rowSU ν Ψ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ζ • (((rowSU ν Ψ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (Y : Matrix (Fin 4) (Fin 4) K)))
    (x : SL(2, extension (ν : K))) :
    ∃ x' : SL(2, extension (ν : K)), Y * rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) * Y⁻¹ =
      rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x') := by
  have hdet1 : ∀ g : GL (Fin 2) (extension (ν : K)),
      ((g * Matrix.SpecialLinearGroup.toGL x * g⁻¹ : GL (Fin 2) (extension (ν : K))) :
        Matrix (Fin 2) (Fin 2) (extension (ν : K))).det = 1 := by
    intro g
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, x.2]
  rcases hζ with rfl | rfl
  · rw [one_smul] at hY
    obtain ⟨g, hg⟩ := exists_rowSPi_of_commute ν Ψ (Units.ext (by
      simp only [Units.val_mul]; exact hY))
    refine ⟨⟨_, hdet1 g⟩, ?_⟩
    have e : Matrix.SpecialLinearGroup.toGL (⟨_, hdet1 g⟩ : SL(2, extension (ν : K))) =
        g * Matrix.SpecialLinearGroup.toGL x * g⁻¹ := Units.ext rfl
    rw [e, hg, ← map_inv, ← map_mul, ← map_mul]
  · have hY' : Y * rowSU ν Ψ = GeneralLinearGroup.scalar (Fin 4) (-1) * rowSU ν Ψ * Y :=
      Units.ext (by
        simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one,
          scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
        exact hY)
    obtain ⟨g, hg⟩ := exists_rowSPi_of_anticommute ν Ψ hY'
    set σ := ((extensionConj ν : extension (ν : K) ≃ₐ[K] _) :
      extension (ν : K) →+* extension (ν : K))
    have hdet2 : ((GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL x) :
        GL (Fin 2) (extension (ν : K))) : Matrix (Fin 2) (Fin 2) (extension (ν : K))).det = 1 := by
      have h := RingHom.map_det σ (Matrix.SpecialLinearGroup.toGL x : Matrix (Fin 2) (Fin 2) _)
      rw [RingHom.mapMatrix_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, x.2,
        map_one] at h
      exact h.symm
    have hκ : (rowSKappa ν Ψ)⁻¹ = rowSKappa ν Ψ :=
      inv_eq_of_mul_eq_one_right (rowSKappa_mul_self ν Ψ)
    have hx' : ((g * GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL x) * g⁻¹ :
        GL (Fin 2) (extension (ν : K))) : Matrix (Fin 2) (Fin 2) (extension (ν : K))).det = 1 := by
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul, hdet2]
    refine ⟨⟨_, hx'⟩, ?_⟩
    have e : Matrix.SpecialLinearGroup.toGL (⟨_, hx'⟩ : SL(2, extension (ν : K))) =
        g * GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL x) * g⁻¹ := Units.ext rfl
    rw [e, hg, _root_.mul_inv_rev, hκ, map_mul, map_mul, map_inv, ← rowSKappa_conj_rowSPi]
    group

theorem comm_of_forall_rowSPi {Y Y' : GL (Fin 4) K}
    (hY : ∀ x : SL(2, extension (ν : K)), ∃ c : Kˣ,
      Y * rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) =
        GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) * Y)
    (hY' : ∀ x : SL(2, extension (ν : K)), ∃ c : Kˣ,
      Y' * rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) =
        GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL x) * Y') :
    Y * Y' = Y' * Y := by
  have : Nontrivial (extension (ν : K)) :=
    (extension_isField (ν : K) Fact.out).nontrivial
  obtain ⟨c₀, hc₀⟩ := CFSG.GH74.GLS.IVK.RowSComm.exists_mul_of_normalizes ν Ψ Y hY
  obtain ⟨c₁, hc₁⟩ := CFSG.GH74.GLS.IVK.RowSComm.exists_mul_of_normalizes ν Ψ Y' hY'
  apply eq_of_mulVec_eq
  intro w
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hc₁, hc₀, hc₀, hc₁,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, smul_smul, smul_smul, mul_comm]

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
