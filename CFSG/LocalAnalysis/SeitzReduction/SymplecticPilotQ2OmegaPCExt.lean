module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank

section Ext

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {K : Type}
  [Field K]

@[expose] def pcExtMat (M : Matrix κ ι K) (R : Matrix ι κ K) (g : Matrix ι ι K) : Matrix κ κ K :=
  1 + M * (g - 1) * R

variable {M : Matrix κ ι K} {R : Matrix ι κ K}

omit [Fintype κ] in
theorem pcExtMat_one : pcExtMat M R 1 = 1 := by simp [pcExtMat]

theorem pcExtMat_mul (hRM : R * M = 1) (g h : Matrix ι ι K) :
    pcExtMat M R (g * h) = pcExtMat M R g * pcExtMat M R h := by
  simp only [pcExtMat]
  have e1 : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  have e2 : M * (g - 1) * R * (M * (h - 1) * R) = M * ((g - 1) * (h - 1)) * R := by
    calc M * (g - 1) * R * (M * (h - 1) * R) = M * (g - 1) * (R * M) * (h - 1) * R := by
          simp only [Matrix.mul_assoc]
      _ = M * ((g - 1) * (h - 1)) * R := by
          rw [hRM, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have e3 : M * (g * h - 1) * R = M * (g - 1) * R + M * (h - 1) * R +
      M * (g - 1) * R * (M * (h - 1) * R) := by
    rw [e2, e1, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  rw [e3]
  noncomm_ring

theorem pcExtMat_conj (hRM : R * M = 1) (g : Matrix ι ι K) : R * pcExtMat M R g * M = g := by
  rw [pcExtMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hRM]
  calc 1 + R * (M * (g - 1) * R) * M = 1 + (R * M) * (g - 1) * (R * M) := by
        simp only [Matrix.mul_assoc]
    _ = g := by rw [hRM, Matrix.one_mul, Matrix.mul_one, add_sub_cancel]

theorem pcExtMat_injective (hRM : R * M = 1) : Function.Injective (pcExtMat M R) := by
  intro g h hgh
  rw [← pcExtMat_conj hRM g, ← pcExtMat_conj hRM h, hgh]

theorem pcExtMat_mulVec (g : Matrix ι ι K) (x : κ → K) :
    pcExtMat M R g *ᵥ x = x + M *ᵥ (g *ᵥ (R *ᵥ x) - R *ᵥ x) := by
  rw [pcExtMat, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem pcExtMat_mulVec_fix (hRM : R * M = 1) {g : Matrix ι ι K} {v : ι → K} (hv : g *ᵥ v = v) :
    pcExtMat M R g *ᵥ (M *ᵥ v) = M *ᵥ v := by
  have hRv : R *ᵥ (M *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hRM, Matrix.one_mulVec]
  rw [pcExtMat_mulVec, hRv, hv, sub_self, Matrix.mulVec_zero, add_zero]

variable (M R) in
@[expose] def pcExtGL (hRM : R * M = 1) : GL ι K →* GL κ K where
  toFun g :=
    { val := pcExtMat M R (g : Matrix ι ι K)
      inv := pcExtMat M R ((g⁻¹ : GL ι K) : Matrix ι ι K)
      val_inv := by rw [← pcExtMat_mul hRM, Units.mul_inv, pcExtMat_one]
      inv_val := by rw [← pcExtMat_mul hRM, Units.inv_mul, pcExtMat_one] }
  map_one' := Units.ext pcExtMat_one
  map_mul' g h := Units.ext (pcExtMat_mul hRM (g : Matrix ι ι K) h)

theorem pcExtGL_injective (hRM : R * M = 1) : Function.Injective (pcExtGL M R hRM) :=
  fun _ _ h => Units.ext (pcExtMat_injective hRM (congrArg Units.val h))

theorem pcExt_isometry {Qg : (κ → K) → K} {Qm : (ι → K) → K}
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x))
    {g : Matrix ι ι K} (hg : ∀ w, Qm (g *ᵥ w) = Qm w) (x : κ → K) :
    Qg (pcExtMat M R g *ᵥ x) = Qg x := by
  rw [pcExtMat_mulVec]
  have h := hQ x (g *ᵥ (R *ᵥ x) - R *ᵥ x)
  rw [add_sub_cancel, hg] at h
  exact sub_eq_zero.1 (h.trans (sub_self _))

theorem map_statedOmega_le_pcExt {Qg : (κ → K) → K} {Qm : (ι → K) → K} (hRM : R * M = 1)
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x)) :
    (StatedOmega Qm).map (pcExtGL M R hRM) ≤ StatedOmega Qg := by
  rw [StatedOmega, StatedOmega, Subgroup.map_commutator, MonoidHom.map_closure]
  have h : Subgroup.closure ((pcExtGL M R hRM) '' {A : GL ι K | ∀ v,
      Qm ((A : Matrix ι ι K) *ᵥ v) = Qm v}) ≤
        Subgroup.closure {A : GL κ K | ∀ v, Qg ((A : Matrix κ κ K) *ᵥ v) = Qg v} := by
    refine Subgroup.closure_mono ?_
    rintro _ ⟨A, hA, rfl⟩
    exact fun v => pcExt_isometry hQ hA v
  exact Subgroup.commutator_mono h h

variable (M R) in
@[expose] noncomputable def pcExtOmega {Qg : (κ → K) → K} {Qm : (ι → K) → K} (hRM : R * M = 1)
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x)) :
    StatedOmega Qm →* StatedOmega Qg :=
  ((pcExtGL M R hRM).comp (StatedOmega Qm).subtype).codRestrict (StatedOmega Qg) fun A =>
    map_statedOmega_le_pcExt hRM hQ ⟨A, A.2, rfl⟩

theorem pcExtOmega_injective {Qg : (κ → K) → K} {Qm : (ι → K) → K} (hRM : R * M = 1)
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x)) :
    Function.Injective (pcExtOmega M R hRM hQ) := fun _ _ h =>
  Subtype.ext (pcExtGL_injective hRM (congrArg Subtype.val h))

end Ext

end CFSG.SeitzReduction.SymplecticPilot
