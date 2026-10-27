module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalKernel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCLex

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def CorCHeldTargetStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (a : X) (J E : Subgroup X), CorC.Config a J E → CorC.LexMax a J →
    ∀ S : Subgroup X, S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
      (∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
        (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) →
      E ≤ S →
    ∀ (b y : X) (M : Subgroup X), orderOf b = 2 → b ∈ S ⊓ coreActionKernel J →
      ¬ (∀ e ∈ E, e * b = b * e) → y ∈ S → GSUnbalancingTriple b y M →
      conjugate M a = M → UnbalancedGS.gsFixedLayer J b ≤ M →
      (pPrimeCore 2 (UnbalancedGS.gsFixedLayer J b)).index < (pPrimeCore 2 M).index →
      ¬ GrSLit.IsHeldType (M ⧸ Open.fusionZStar M)

@[expose] def CorCDiagonalStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (a : X) (J E : Subgroup X), CorC.Config a J E → CorC.LexMax a J →
    ∀ S : Subgroup X, S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
      (∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
        (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) →
      E ≤ S →
    ∀ (b y : X) (M : Subgroup X), orderOf b = 2 → b ∈ S ⊓ coreActionKernel J →
      ¬ (∀ e ∈ E, e * b = b * e) → y ∈ S → GSUnbalancingTriple b y M →
      conjugate M a ≠ M → UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a →
      Nonempty (M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin 7)) → False

namespace CorC

variable {X : Type} [Group X] [Finite X]

theorem fusionZStar_eq_of_alternating {T : Type*} [Group T]
    (h7 : Nonempty (T ⧸ pPrimeCore 2 T ≃* alternatingGroup (Fin 7))) :
    Open.fusionZStar T = pPrimeCore 2 T := by
  obtain ⟨e7⟩ := h7
  have hs : IsSimpleGroup (T ⧸ pPrimeCore 2 T) :=
    @MulEquiv.isSimpleGroup _ _ _ _
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))) e7
  refine UnbalancedCorr.fusionZStar_eq_pPrimeCore_of_isSimpleGroup hs ?_
  obtain ⟨u, v, huv⟩ := SolAltLit.alternating_nonabelian (by norm_num : 4 ≤ 7)
  refine ⟨e7.symm u, e7.symm v, fun h => huv ?_⟩
  simpa using congrArg e7 h

theorem not_isL2Type_of_alternating {T : Type} [Group T] {q : ℕ} (hq : q ≠ 2)
    (h7 : Nonempty (T ⧸ pPrimeCore 2 T ≃* alternatingGroup (Fin 7)))
    (hL : GrSLit.IsL2Type q (T ⧸ Open.fusionZStar T)) : False := by
  have hZ := fusionZStar_eq_of_alternating h7
  obtain ⟨e7⟩ := h7
  have hc := GSThmB.card_of_lieModel_psl_two hq hL
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv, Nat.card_congr e7.toEquiv,
    GSThmB.card_alternatingGroup_seven] at hc
  exact GSThmB.ordA_one_ne_2520 _ hc.symm

end CorC

end CFSG.ComponentClassification.GSThmB
