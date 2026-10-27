module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitThmBReach

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def TheoremBIsoInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J →
      (∀ y b : X, y ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
        GSUnbalancingTriple a y J → orderOf b = 2 → a * b = b * a → y * b = b * y →
        b ∈ coreActionKernel J →
        ∃ M : Subgroup X, UnbalancedGS.GSIsoCorr a J b M ∧ GSUnbalancingTriple b y M) →
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

theorem theoremBReachInput_of_iso (hS : SchreierFor Blueprint.Catalog) (h : TheoremBIsoInput) :
    GrSLit.TheoremBReachInput :=
  fun X _ _ _ hnonab hK hz hU a x J hJ hbound htype =>
    h X hnonab hK hz hU a x J hJ
      (fun _ _ hy hUy hb hab hyb hbJ =>
        isoCorr_of_commuting_involution_of_bound hS hnonab hK hJ hbound hy hUy hb hab hyb hbJ)
      htype

end CFSG.ComponentClassification.GSThmB
