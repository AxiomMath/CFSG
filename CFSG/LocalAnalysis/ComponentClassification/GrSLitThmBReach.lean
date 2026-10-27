module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakCorr
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def TheoremBReachInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J →
      (∀ (u v : X) (K : Subgroup X), GSUnbalancingTriple u v K → GSWeakReach J K →
        (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index) →
      (Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
        Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2) →
      ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
          Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∧
        ∃ (b : X) (L : Subgroup X) (ρ e : ℕ), orderOf b = 2 ∧ L ≤ centralizer ({b} : Set X) ∧
          IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set X))) ∧ ρ.Prime ∧ ρ ≠ 2 ∧
          1 ≤ e ∧ Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 ρ (2 * e) ∧
          zpowers b ≤ coreActionKernel L ∧
          ∃ P : Sylow 2 ↥(coreActionKernel L),
            (P : Subgroup _) = (zpowers b).subgroupOf (coreActionKernel L)) ∨
      ((∀ b : X, orderOf b = 2 → b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
          (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
          ∃ K : Subgroup X, UnbalancedGS.GSIsoCorr a J b K) ∧
        ∀ (b : X) (K : Subgroup X), orderOf b = 2 →
          b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
          (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
          UnbalancedGS.GSIsoCorr a J b K →
          ∀ S : Subgroup X, S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
            (∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
              (P : Subgroup _) =
                S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) →
            b ∈ S → (∀ s ∈ S, s * b = b * s) →
            S ≤ centralizer ({b} : Set X) ⊓ normalizer (K : Set X) ∧
              ∃ P : Sylow 2 ↥(centralizer ({b} : Set X) ⊓ normalizer (K : Set X)),
                (P : Subgroup _) =
                  S.subgroupOf (centralizer ({b} : Set X) ⊓ normalizer (K : Set X)))

theorem theoremBBoundedInput_of_theoremBReachInput (h : TheoremBReachInput) :
    GSLit.TheoremBBoundedInput :=
  fun X _ _ _ hnonab hK hz hU a x J hJ hbound htype =>
    h X hnonab hK hz hU a x J hJ (fun u v K hK' _ => hbound u v K hK') htype

theorem theoremBReachInput_of_theoremBInput (h : GSLit.TheoremBInput) : TheoremBReachInput :=
  fun X _ _ _ hnonab hK hz hU a x J hJ _ htype => (h X hnonab hK hz hU).1 a x J hJ htype

end CFSG.ComponentClassification.GrSLit
