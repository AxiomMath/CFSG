module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherOuterQuotient
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat

public noncomputable section

namespace CFSG.QuasithinUnique.Lin2.Five

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {F : Type} [Field F]

theorem Sc_of_mem (g : GL (Fin 2 ⊕ Fin 2) F) (hg : g ∈ StatedSp 2 F) :
    Sc (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  have hc : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jm *
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = jm :=
    SymplecticTorusWeyl.mem_statedSp_iff.mp hg
  have hmem : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ∈
      Matrix.symplecticGroup (Fin 2) F := by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic] at hg
    exact TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp hg
  have hr0 := SymplecticGroup.mem_iff.mp hmem
  have hj : (jm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -Matrix.J (Fin 2) F :=
    CFSG.ClassicalGroups.Symplectic.blueprintGram_eq_neg_J
  have hr : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * jm *
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ = jm := by
    rw [hj, Matrix.mul_neg, Matrix.neg_mul, hr0]
  exact Sc.of_matrix hc hr

theorem tauS_val (t : F) :
    (((tauS t 0 0 : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 + t • rootE F := by
  rw [coe_tauS]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootE, sym2, Matrix.fromBlocks]

section Tau

variable [CharP F 2]

theorem two_eq_zero_F : (2 : F) = 0 := CharTwo.two_eq_zero

@[expose] def tauGL (g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨tauMat ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
    tauMat (((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
    by
      rw [← tauMat_mul two_eq_zero_F (Sc_of_mem g.1 g.2) (Sc_of_mem (g⁻¹).1 (g⁻¹).2)]
      have : ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          (((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
        rw [← Units.val_mul]
        simp
      rw [this, tauMat_one],
    by
      rw [← tauMat_mul two_eq_zero_F (Sc_of_mem (g⁻¹).1 (g⁻¹).2) (Sc_of_mem g.1 g.2)]
      have : (((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
        rw [← Units.val_mul]
        simp
      rw [this, tauMat_one]⟩

theorem coe_tauGL (g : StatedSp 2 F) :
    ((tauGL g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      tauMat ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := rfl

theorem tauGL_mem (g : StatedSp 2 F) : tauGL g ∈ StatedSp 2 F := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff, coe_tauGL]
  exact Sc.to_col (tauMat_sc two_eq_zero_F (Sc_of_mem g.1 g.2))

@[expose] def tauSp : StatedSp 2 F →* StatedSp 2 F where
  toFun g := ⟨tauGL g, tauGL_mem g⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show tauMat ((1 : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1
    rw [Units.val_one, tauMat_one]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    show tauMat (((g * h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      tauMat ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        tauMat ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact tauMat_mul two_eq_zero_F (Sc_of_mem g.1 g.2) (Sc_of_mem h.1 h.2)

theorem coe_tauSp (g : StatedSp 2 F) :
    (((tauSp g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      tauMat ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := rfl

@[expose] def frobAut (F : Type) [Field F] [Finite F] [CharP F 2] : F ≃+* F := frobeniusEquiv F 2

theorem frobAut_apply [Finite F] (a : F) : frobAut F a = a ^ 2 := by
  simp [frobAut, frobeniusEquiv_apply, frobenius_def]

theorem tauSp_tauSp [Finite F] (g : StatedSp 2 F) :
    tauSp (tauSp g) = fieldSp 2 F (frobAut F) g := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_fieldSp, coe_tauSp, coe_tauSp, tauMat_tauMat two_eq_zero_F (Sc_of_mem g.1 g.2)]
  ext i j
  simp [frobAut_apply]

theorem tauSp_bijective [Finite F] : Function.Bijective (tauSp : StatedSp 2 F →* StatedSp 2 F) := by
  constructor
  · intro a b hab
    apply (fieldSp 2 F (frobAut F)).injective
    rw [← tauSp_tauSp, ← tauSp_tauSp, hab]
  · intro y
    obtain ⟨g, hg⟩ := (fieldSp 2 F (frobAut F)).surjective y
    exact ⟨tauSp g, by rw [← hg, ← tauSp_tauSp]⟩

@[expose] def tauEquiv [Finite F] : StatedSp 2 F ≃* StatedSp 2 F :=
  MulEquiv.ofBijective tauSp tauSp_bijective

@[expose] def tauAut [Finite F] : MulAut (StatedProj (StatedSp 2 F)) :=
  (projEquiv F).symm.trans (tauEquiv.trans (projEquiv F))

theorem tauAut_proj [Finite F] (g : StatedSp 2 F) :
    tauAut (proj 2 F g) = proj 2 F (tauSp g) := by
  have h1 : proj 2 F g = projEquiv F g := rfl
  have h2 : proj 2 F (tauSp g) = projEquiv F (tauEquiv g) := rfl
  rw [h1, h2]
  show (projEquiv F) (tauEquiv ((projEquiv F).symm (projEquiv F g))) = _
  rw [MulEquiv.symm_apply_apply]

theorem tauAut_mul_self [Finite F] : tauAut * tauAut = fieldAut 2 F (frobAut F) := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [MulAut.mul_apply, tauAut_proj, tauAut_proj, fieldAut_proj, tauSp_tauSp]

theorem tauAut_not_mem_E [Finite F] : tauAut ∉ spSemilinearAutGroup 2 F := by
  intro hmem
  obtain ⟨A, σ, hA⟩ := mem_spSemilinearAutGroup_iff.mp hmem
  have h1 : tauAut (proj 2 F (tauS 1 0 0)) =
      (conjAut 2 F A * fieldAut 2 F σ) (proj 2 F (tauS 1 0 0)) := by rw [← hA]
  rw [tauAut_proj, MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h1
  have h2 : tauSp (tauS 1 0 0) = conjSp 2 F A (fieldSp 2 F σ (tauS 1 0 0)) :=
    (projEquiv F).injective h1
  have h3 := congrArg (fun x : StatedSp 2 F =>
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h2
  simp only [coe_tauSp, coe_conjSp, coe_fieldSp, Units.val_mul, tauS_val, one_smul] at h3
  exact tauMat_rootE_ne_conj ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) σ.toRingHom (by rw [← Units.val_mul]; simp) h3

theorem fieldAut_eq_one_of_mem_inner [Finite F] {σ : F ≃+* F}
    (h : fieldAut 2 F σ ∈ inner (StatedProj (StatedSp 2 F))) : σ = 1 := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨G, rfl⟩ := proj_surjective x
  have key : ∀ t : F, fieldSp 2 F σ (tauS t 0 0) = G * tauS t 0 0 * G⁻¹ := by
    intro t
    have h1 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 F)) =>
      α (proj 2 F (tauS t 0 0))) hx
    simp only [MulAut.conj_apply, fieldAut_proj] at h1
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact ((projEquiv F).injective h1).symm
  have hm : ∀ t : F, (1 + t • rootE F : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ =
      ((G : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (1 + t • rootE F) *
        (((G : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro t
    have h3 := congrArg (fun x : StatedSp 2 F =>
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (key t)
    simp only [coe_fieldSp, tauS_val, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv] at h3
    exact h3
  have := eq_of_twist_rootE_conj σ.toRingHom
    ((G : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (((G : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (by rw [← Units.val_mul]; simp) hm
  ext t
  simpa using this t

end Tau

end CFSG.QuasithinUnique.Lin2.Five
