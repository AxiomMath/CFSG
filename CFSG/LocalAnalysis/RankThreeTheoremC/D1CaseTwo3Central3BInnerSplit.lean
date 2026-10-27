module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def InducesOuterOn {X : Type} [Group X] (a : X) (L : Subgroup X) : Prop :=
  a ∈ Subgroup.normalizer (L : Set X) ∧ ¬ ∃ y ∈ L, ∀ w ∈ L, a * w * a⁻¹ = y * w * y⁻¹

@[expose] def IsFieldOmegaA (p : ℕ) (M H R : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G) : Prop :=
  E ≤ R ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
    (E.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L ≠ ⊥ ∧
    ∃ a ∈ (E.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
      InducesOuterOn a L

@[expose] def D1CaseTwoCentral3InnerQ (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) →
    ∀ z : H, D1CaseTwoCand p M H R z →
      (∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({(z : G)} : Set G)) →
      ¬ D1CaseTwoAlphaR p M H R →
      ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
        ¬ L ≤ d1X0 p M H ∧ ∃ E : Subgroup G, IsFieldOmegaA p M H R L E ∧
          rankThreeGamma 1 p E ≤ M

end CFSG.LocalAnalysis.RankThreeTheoremC
