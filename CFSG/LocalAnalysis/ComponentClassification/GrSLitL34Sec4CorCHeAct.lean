module

public import CFSG.Sporadic.HeldB.OuterCent
public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentAux
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
import Certificates.Kernel.SporSch.HeT.Q2117
import Certificates.Kernel.SporSch.HeT.Q22972K
import CFSG.Certificates.Kernel.SporSch.ChainClsSound
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCHeOut
public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCHeUniq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCDiagUniq
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayerNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCDiagCover

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem oddQuotConj_eq_one_iff {M : Subgroup X} (n : ↥(normalizer (M : Set X))) :
    oddQuotConj M n = 1 ↔ (n : X) ∈ coreActionKernel M := by
  have hO : ∀ y : ↥M, (y : X) ∈ (pPrimeCore 2 ↥M).map M.subtype ↔ y ∈ pPrimeCore 2 ↥M :=
    fun y => ⟨fun ⟨z, hz, hzy⟩ => Subtype.ext hzy ▸ hz, fun h => ⟨y, h, rfl⟩⟩
  have hact : ∀ (m : ↥(normalizer (M : Set X))) (j : ↥M),
      oddQuotConj M m (j : ↥M ⧸ pPrimeCore 2 ↥M) =
        ((⟨m * j * (m : X)⁻¹, (mem_normalizer_iff.mp m.2 j).mp j.2⟩ : ↥M) :
          ↥M ⧸ pPrimeCore 2 ↥M) := fun m j => rfl
  constructor
  · intro h
    refine mem_coreActionKernel.mpr ⟨n.2, fun j hj => ?_⟩
    have h1 : oddQuotConj M n⁻¹ = 1 := by rw [map_inv, h, inv_one]
    have h2 := congrArg (fun φ => φ ((⟨j, hj⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M)) h1
    simp only [MulAut.one_apply] at h2
    rw [hact, eq_comm, QuotientGroup.eq] at h2
    have h3 := (hO _).mpr h2
    convert h3 using 1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H j =>
      rw [hact, MulAut.one_apply, QuotientGroup.eq, ← hO]
      have hj' : (n : X) * j * (n : X)⁻¹ ∈ M := (mem_normalizer_iff.mp n.2 j).mp j.2
      have h1 := (mem_coreActionKernel.mp h).2 _ hj'
      convert h1 using 1
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group

end CFSG.ComponentClassification.GSThmB.CorC
