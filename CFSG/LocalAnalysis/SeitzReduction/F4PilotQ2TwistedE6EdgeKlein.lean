module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourEquivariance
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmPlusData
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.Assembly.LowTwoRank

section Klein

abbrev TwF4 : Type := CFSG.LieType.Chevalley.C2E6Overlap.K

@[expose] noncomputable def twKappaLin (A : Matrix (Fin 4) (Fin 4) TwF4) :
    CFSG.LieType.Chevalley.C2E6Overlap.X →ₗ[ZMod 2] CFSG.LieType.Chevalley.C2E6Overlap.X :=
  CFSG.LieType.Chevalley.C2E6Overlap.psiLin ∘ₗ
    ((Matrix.mulVecLin (CFSG.LieType.Chevalley.C2E6Overlap.ext2 A)).restrictScalars (ZMod 2)) ∘ₗ
      CFSG.LieType.Chevalley.C2E6Overlap.paramLin

theorem twKappaLin_apply (A : Matrix (Fin 4) (Fin 4) TwF4)
    (x : CFSG.LieType.Chevalley.C2E6Overlap.X) :
    twKappaLin A x = CFSG.LieType.Chevalley.C2E6Overlap.psiLin
      (CFSG.LieType.Chevalley.C2E6Overlap.ext2 A *ᵥ CFSG.LieType.Chevalley.C2E6Overlap.param x) :=
  rfl

@[expose] def twKappa (A : Matrix (Fin 4) (Fin 4) TwF4) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => CFSG.LieType.Chevalley.C2E6Overlap.psiLin
    (CFSG.LieType.Chevalley.C2E6Overlap.ext2 A *ᵥ
      CFSG.LieType.Chevalley.C2E6Overlap.param (Pi.single j 1)) i

theorem twKappa_eq_toMatrix' (A : Matrix (Fin 4) (Fin 4) TwF4) :
    twKappa A = LinearMap.toMatrix' (twKappaLin A) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  rfl

theorem twKappa_mulVec (A : Matrix (Fin 4) (Fin 4) TwF4)
    (x : CFSG.LieType.Chevalley.C2E6Overlap.X) : twKappa A *ᵥ x = twKappaLin A x := by
  rw [twKappa_eq_toMatrix', LinearMap.toMatrix'_mulVec]

theorem twKappaLin_mul (A B : Matrix (Fin 4) (Fin 4) TwF4)
    (hB : ∀ x, CFSG.LieType.Chevalley.C2E6Overlap.ext2 B *ᵥ
      CFSG.LieType.Chevalley.C2E6Overlap.param x ∈ CFSG.LieType.Chevalley.C2E6Overlap.W₀) :
    twKappaLin (A * B) = twKappaLin A ∘ₗ twKappaLin B := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, twKappaLin_apply, twKappaLin_apply, twKappaLin_apply,
    CFSG.LieType.Chevalley.C2E6Overlap.param_psiLin (hB x),
    CFSG.LieType.Chevalley.C2E6Overlap.ext2_mul, ← Matrix.mulVec_mulVec]

theorem twKappa_mul (A B : Matrix (Fin 4) (Fin 4) TwF4)
    (hB : ∀ x, CFSG.LieType.Chevalley.C2E6Overlap.ext2 B *ᵥ
      CFSG.LieType.Chevalley.C2E6Overlap.param x ∈ CFSG.LieType.Chevalley.C2E6Overlap.W₀) :
    twKappa (A * B) = twKappa A * twKappa B := by
  rw [twKappa_eq_toMatrix', twKappa_eq_toMatrix', twKappa_eq_toMatrix', twKappaLin_mul A B hB,
    LinearMap.toMatrix'_comp]

theorem twKappa_one : twKappa 1 = 1 := by
  have h : twKappaLin 1 = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    rw [twKappaLin_apply, CFSG.LieType.Chevalley.C2E6Overlap.ext2_one, Matrix.one_mulVec,
      CFSG.LieType.Chevalley.C2E6Overlap.psiLin_param]
    rfl
  rw [twKappa_eq_toMatrix', h, LinearMap.toMatrix'_id]

theorem ext2_mulVec_param_mem {g : GL (Fin 4) TwF4} (hg : g ∈ CFSG.LieType.Chevalley.C2E6Overlap.SU)
    (x : CFSG.LieType.Chevalley.C2E6Overlap.X) :
    CFSG.LieType.Chevalley.C2E6Overlap.ext2 (g : Matrix (Fin 4) (Fin 4) TwF4) *ᵥ
      CFSG.LieType.Chevalley.C2E6Overlap.param x ∈ CFSG.LieType.Chevalley.C2E6Overlap.W₀ :=
  CFSG.LieType.Chevalley.C2E6Overlap.ext2GL_mem_W₀ hg
    (CFSG.LieType.Chevalley.C2E6Overlap.param_mem_W₀ x)

theorem Q_twKappa_mulVec {g : GL (Fin 4) TwF4} (hg : g ∈ CFSG.LieType.Chevalley.C2E6Overlap.SU)
    (x : CFSG.LieType.Chevalley.C2E6Overlap.X) :
    CFSG.LieType.Chevalley.C2E6Overlap.Q (twKappa (g : Matrix (Fin 4) (Fin 4) TwF4) *ᵥ x) =
      CFSG.LieType.Chevalley.C2E6Overlap.Q x := by
  rw [twKappa_mulVec]
  exact (CFSG.LieType.Chevalley.C2E6Overlap.suIso hg).map_app x

@[expose] noncomputable def twKappaHom :
    CFSG.LieType.Chevalley.C2E6Overlap.SU →* Matrix (Fin 6) (Fin 6) (ZMod 2) where
  toFun g := twKappa ((g : GL (Fin 4) TwF4) : Matrix (Fin 4) (Fin 4) TwF4)
  map_one' := twKappa_one
  map_mul' g g' := by
    change twKappa (((g * g' : GL (Fin 4) TwF4)) : Matrix (Fin 4) (Fin 4) TwF4) = _
    rw [Units.val_mul]
    exact twKappa_mul _ _ (ext2_mulVec_param_mem g'.2)

end Klein

section Six

@[expose] def twEnc6 : omMI6 ≃ Fin 6 where
  toFun := omMEnc6
  invFun := ![.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]
  left_inv := by decide
  right_inv := by decide

theorem omMMat6_eq_submatrix (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    omMMat6 A = A.submatrix twEnc6 twEnc6 :=
  rfl

theorem omMMat6_mul (A B : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    omMMat6 (A * B) = omMMat6 A * omMMat6 B := by
  rw [omMMat6_eq_submatrix, omMMat6_eq_submatrix, omMMat6_eq_submatrix,
    Matrix.submatrix_mul_equiv]

theorem omMMat6_one : omMMat6 (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
  rw [omMMat6_eq_submatrix, Matrix.submatrix_one_equiv]

theorem statedQuadMinus_eq_Q_comp : ∀ v : omMI6 → ZMod 2,
    StatedQuadMinus 3 (ZMod 2) 1 1 v =
      CFSG.LieType.Chevalley.C2E6Overlap.Q (v ∘ twEnc6.symm) := by
  decide +kernel

theorem omMMat6_mulVec_comp (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) (v : omMI6 → ZMod 2) :
    (omMMat6 A *ᵥ v) ∘ twEnc6.symm = A *ᵥ (v ∘ twEnc6.symm) := by
  rw [omMMat6_eq_submatrix, Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
    Equiv.self_comp_symm, Function.comp_id]

theorem statedQuadMinus_omMMat6_mulVec {A : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hA : ∀ x, CFSG.LieType.Chevalley.C2E6Overlap.Q (A *ᵥ x) =
      CFSG.LieType.Chevalley.C2E6Overlap.Q x) (v : omMI6 → ZMod 2) :
    StatedQuadMinus 3 (ZMod 2) 1 1 (omMMat6 A *ᵥ v) = StatedQuadMinus 3 (ZMod 2) 1 1 v := by
  rw [statedQuadMinus_eq_Q_comp, statedQuadMinus_eq_Q_comp, omMMat6_mulVec_comp, hA]

theorem statedQuadMinus_omMMat6_twKappa_mulVec {g : GL (Fin 4) TwF4}
    (hg : g ∈ CFSG.LieType.Chevalley.C2E6Overlap.SU) (v : omMI6 → ZMod 2) :
    StatedQuadMinus 3 (ZMod 2) 1 1
        (omMMat6 (twKappa (g : Matrix (Fin 4) (Fin 4) TwF4)) *ᵥ v) =
      StatedQuadMinus 3 (ZMod 2) 1 1 v :=
  statedQuadMinus_omMMat6_mulVec (Q_twKappa_mulVec hg) v

end Six

end CFSG.SeitzReduction.F4Pilot
