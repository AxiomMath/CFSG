module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55D4ThreeFix
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteW
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Struct
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SubfieldMaximalSL2
public import CFSG.GH74.GLS.SP.Local.SPLRestrict
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingOddProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThree
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.SeitzGeneration.ExcOuterTriality
public import CFSG.LieType.SeitzGeneration.OrthLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxDone
public import Certificates.Kernel.SporSch.Th.Plane2320

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] def JTw (σ : K →+* K) : Subgroup (twistedGroup σ) :=
  MonoidHom.eqLocus ((Units.map (entrywiseHom σ)).comp (twistedIncl σ)) (twistedIncl σ)

theorem mem_JTw {x : twistedGroup σ} :
    x ∈ JTw σ ↔ Units.map (entrywiseHom σ) (twistedIncl σ x) = twistedIncl σ x := Iff.rfl

include hσ in
theorem slLong_mem_JTw (A : SL(2, fixedField σ)) : slLong σ hσ A ∈ JTw σ := by
  have hh : MonoidHom.eqLocus
      ((Units.map (entrywiseHom σ)).comp ((twistedIncl σ).comp (slLong σ hσ)))
      ((twistedIncl σ).comp (slLong σ hσ)) = ⊤ := by
    rw [eq_top_iff,
      ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixedField σ),
      Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have hc : σ (c : K) = c := c.2
      show Units.map (entrywiseHom σ) (twistedIncl σ (slLong σ hσ (uSL c))) =
        twistedIncl σ (slLong σ hσ (uSL c))
      rw [twistedIncl_slLong_upper hσ, coe_xPar_single_two, units_map_entrywiseHom_xUnit, hc]
    · have hc : σ (c : K) = c := c.2
      show Units.map (entrywiseHom σ) (twistedIncl σ (slLong σ hσ (vSL c))) =
        twistedIncl σ (slLong σ hσ (vSL c))
      rw [twistedIncl_slLong_lower hσ, coe_xPar_neg_single_two, units_map_entrywiseHom_yUnit, hc]
  have : A ∈ (⊤ : Subgroup SL(2, fixedField σ)) := trivial
  rw [← hh] at this
  exact this

include hσ in
theorem entrywise_slB [Finite K] (B : SL(2, K)) :
    Units.map (entrywiseHom σ) (twistedIncl σ (slB σ hσ B)) =
      twistedIncl σ (slB σ hσ (Matrix.SpecialLinearGroup.map σ B)) := by
  let σE : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have hcan : Units.map (entrywiseHom σ) (canonicalRep (coxeterSystem d4) K tdNhat) =
      canonicalRep (coxeterSystem d4) K tdNhat := by
    have := entrywise_canonicalRep (τ := d4) σE tdNhat
    rwa [hσE] at this
  have hh : MonoidHom.eqLocus
      ((Units.map (entrywiseHom σ)).comp ((twistedIncl σ).comp (slB σ hσ)))
      (((twistedIncl σ).comp (slB σ hσ)).comp (Matrix.SpecialLinearGroup.map σ)) = ⊤ := by
    rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K),
      Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have hu : Matrix.SpecialLinearGroup.map σ (sl2Upper c) = sl2Upper (σ c) := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.map_apply_coe]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2Upper]
      show Units.map (entrywiseHom σ) (twistedIncl σ (slB σ hσ (uSL c))) =
        twistedIncl σ (slB σ hσ (Matrix.SpecialLinearGroup.map σ (uSL c)))
      rw [uSL_eq_sl2Upper, hu, ← uSL_eq_sl2Upper, ← uSL_eq_sl2Upper, twistedIncl_slB hσ,
        twistedIncl_slB hσ, map_mul, map_mul, map_inv, hcan, twistedIncl_slShort_upper hσ,
        twistedIncl_slShort_upper hσ, entrywise_xOuter σ (Or.inl rfl), hσ c]
    · have hu : Matrix.SpecialLinearGroup.map σ (sl2Lower c) = sl2Lower (σ c) := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.map_apply_coe]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2Lower]
      show Units.map (entrywiseHom σ) (twistedIncl σ (slB σ hσ (vSL c))) =
        twistedIncl σ (slB σ hσ (Matrix.SpecialLinearGroup.map σ (vSL c)))
      rw [vSL_eq_sl2Lower, hu, ← vSL_eq_sl2Lower, ← vSL_eq_sl2Lower, twistedIncl_slB hσ,
        twistedIncl_slB hσ, map_mul, map_mul, map_inv, hcan, twistedIncl_slShort_lower hσ,
        twistedIncl_slShort_lower hσ, entrywise_xOuter σ (Or.inr rfl), hσ c]
  have : B ∈ (⊤ : Subgroup SL(2, K)) := trivial
  rw [← hh] at this
  exact this

include hσ in
theorem slB_mem_JTw_iff [Finite K] (B : SL(2, K)) :
    slB σ hσ B ∈ JTw σ ↔ B ∈ CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.sl2Range
      (fixedField σ) K := by
  rw [mem_JTw, entrywise_slB hσ]
  constructor
  · intro h
    have h1 : slB σ hσ (Matrix.SpecialLinearGroup.map σ B) = slB σ hσ B :=
      twistedIncl_injective σ h
    have h2 : Matrix.SpecialLinearGroup.map σ B = B := slB_injective hσ h1
    have h3 : ∀ i j, σ ((B : Matrix (Fin 2) (Fin 2) K) i j) = (B : Matrix (Fin 2) (Fin 2) K) i j :=
      fun i j => by
        have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) i j) h2
        simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
    let y : Matrix (Fin 2) (Fin 2) (fixedField σ) :=
      Matrix.of fun i j => ⟨(B : Matrix (Fin 2) (Fin 2) K) i j, h3 i j⟩
    have hy : y.map (algebraMap (fixedField σ) K) = (B : Matrix (Fin 2) (Fin 2) K) := by
      ext i j; rfl
    have hdet : y.det = 1 := by
      apply (algebraMap (fixedField σ) K).injective
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hy, B.2, map_one]
    exact ⟨⟨y, hdet⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    have : Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map
        (algebraMap (fixedField σ) K) y) = Matrix.SpecialLinearGroup.map
        (algebraMap (fixedField σ) K) y := by
      apply Subtype.ext
      ext i j
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact (y i j).2
    rw [this]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
