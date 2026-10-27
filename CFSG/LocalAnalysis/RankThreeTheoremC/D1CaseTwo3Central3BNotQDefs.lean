module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111DataBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111

variable {G : Type} [Group G] [Finite G]

@[expose] def innerNotQJ (p : ℕ) (H : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  Subgroup.normalClosure (L : Set (H ⧸ primeComplementCore (G := H) p))

theorem le_innerNotQJ (p : ℕ) (H : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) : L ≤ innerNotQJ p H L :=
  Subgroup.le_normalClosure

theorem innerNotQJ_eq_of_normal (p : ℕ) (H : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) [L.Normal] : innerNotQJ p H L = L :=
  Subgroup.normalClosure_eq_self L

structure InnerNotQConfig (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G) : Prop where
  cfg : D1ComponentConfig3 p P M H R Rbar
  cyclic : ∀ L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L' ⊤ →
    IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L' :
      Subgroup (H ⧸ primeComplementCore (G := H) p))
  cand : D1CaseTwoCand p M H R z
  central : ∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
    Subgroup.centralizer ({(z : G)} : Set G)
  notAlphaR : ¬ D1CaseTwoAlphaR p M H R
  isComponent : IsComponentOf L ⊤
  not_le : ¬ L ≤ d1X0 p M H
  fieldOmega : IsFieldOmegaA p M H R L E
  gamma : rankThreeGamma 1 p E ≤ M

@[expose] def InnerNotQNineThree (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G),
    InnerNotQConfig p P M H R Rbar z L E → Hyp111NineThree p M H (innerNotQJ p H L)

@[expose] def innerNotQBaseA (p : ℕ) (H R : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G) : Subgroup G :=
  d1LiftX p H R (innerNotQJ p H L) ⊔ E

theorem le_innerNotQBaseA (p : ℕ) (H R : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G) :
    E ≤ innerNotQBaseA p H R L E :=
  le_sup_right

theorem innerNotQBaseA_le {p : ℕ} {H R : Subgroup G}
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {E : Subgroup G} (hER : E ≤ R) :
    innerNotQBaseA p H R L E ≤ R :=
  sup_le (d1LiftX_le p H R _) hER

@[expose] def InnerNotQBlockA (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G),
    InnerNotQConfig p P M H R Rbar z L E →
    ∃ Lm : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) Lm ∧ (Lm.subgroupOf M).Normal ∧
      ∀ a ∈ innerNotQBaseA p H R L E, ∀ l ∈ Lm, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 M

end CFSG.LocalAnalysis.RankThreeTheoremC
