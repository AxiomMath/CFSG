module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankOmega
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.LieType.BorelTits.OrthogonalSingular
public import CFSG.LieType.BorelTits.Families
public import CFSG.RankThree.PartOne.AUTSL.OmegaModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4YB

open scoped Matrix
open CFSG.StandardType CFSG.StandardType.D4Rank CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.BorelTits

section Flag

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def omForm : QuadForm K (Fin (2 * 4) → K) :=
  CFSG.RankThree.OrthogonalInvolutions.toQuadForm (coordinateQuadPlus 4 K)
    (regular_coordinateQuadPlus 4 K (by norm_num)).1

theorem omForm_Q (v : Fin (2 * 4) → K) : (omForm (K := K)).Q v = coordinateQuadPlus 4 K v := rfl

theorem omRep_Q (x : Om8 K) (v : Fin (2 * 4) → K) :
    (omForm (K := K)).Q (omRep x v) = (omForm (K := K)).Q v := by
  rw [omForm_Q, omForm_Q, omRep_apply]
  exact (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.mem_matrixIsometries_iff _ _).1
    (matrixDerived_le_isometries _ x.2) v

theorem omRep_injective : Function.Injective (omRep (K := K)) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h : ((x : GL (Fin (2 * 4)) K).val *ᵥ (Pi.single j 1 : Fin (2 * 4) → K)) i =
      ((y : GL (Fin (2 * 4)) K).val *ᵥ (Pi.single j 1 : Fin (2 * 4) → K)) i :=
    congrArg (fun f : Module.End K (Fin (2 * 4) → K) => f (Pi.single j 1) i) hxy
  simpa [Matrix.mulVec_single_one] using h

theorem noQuotientReflection_omRep : NoQuotientReflection (omForm (K := K)) (omRep (K := K)) := by
  intro h Z hZ a ha hQa hrefl
  have hmem : (h : GL (Fin (2 * 4)) K) ∈ CFSG.Open.StatedOmega (omForm (K := K)).Q := by
    exact (Subgroup.ext_iff.mp (CFSG.RankThree.PartOne.AUTSL.matrixDerived_eq_statedOmega
      (coordinateQuadPlus 4 K)) _).1 h.2
  refine not_reflection_on_quotient_of_mem_statedOmega (omForm (K := K)) hmem hZ ha hQa fun v hv => ?_
  have := hrefl v hv
  rwa [omRep_apply] at this

theorem exists_totallySingular (R : Subgroup (Om8 K)) (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥) :
    ∃ Z : Submodule K (Fin (2 * 4) → K), Z ≠ ⊥ ∧ (∀ v ∈ Z, coordinateQuadPlus 4 K v = 0) ∧
      ∀ n ∈ Subgroup.normalizer (R : Set (Om8 K)), ∀ v ∈ Z, omRep n v ∈ Z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := omRep_Q (K := K)
  have hker := le_flagKernel_singFlag 2 hQ noQuotientReflection_omRep R hR2
  refine ⟨singSeq (omForm (K := K)) (omRep (K := K)) R (Module.finrank K (Fin (2 * 4) → K)), ?_,
    fun v hv => hv.2, fun n hn v hv => apply_mem_singSeq hQ R _ hn hv⟩
  intro hbot
  apply hR
  rw [eq_bot_iff]
  intro g hg
  have hk := (hker hg).2 (Module.finrank K (Fin (2 * 4) → K))
  rw [singFlag_finrank_succ, singFlag_finrank, hbot, ReflForm.perp_bot] at hk
  rw [Subgroup.mem_bot]
  apply omRep_injective
  refine LinearMap.ext fun v => ?_
  have := hk v Submodule.mem_top
  rw [Submodule.mem_bot, sub_eq_zero] at this
  rw [this, map_one]
  rfl

end Flag

end CFSG.LocalAnalysis.GLTheoremA.D4YB
