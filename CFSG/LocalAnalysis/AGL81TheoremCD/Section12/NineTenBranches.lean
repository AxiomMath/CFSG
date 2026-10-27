module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTen

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem nineTen_branchC_of_twelveCtx
    (h10 : NineTenGen) (h : TwelveCtx G M p Q H)
    {E : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) (hbot : pLayerIn p H = ⊥) :
    NineTenThreeCorrected p M H :=
  (nineTenConclusion_of_twelveCtx h10 h hEQ hE hEc hΓ).2.2 hbot

theorem nineTen_branchA_of_twelveCtx
    (h10 : NineTenGen) (h : TwelveCtx G M p Q H)
    {E : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) (hA : ¬ pLayerIn p H ≤ M) :
    (xSub p M H ≤ M ∧ H = kSub p M H ⊔ (H ⊓ M) ∧ ((kSub p M H).subgroupOf H).Normal) ∨
      (p = 3 ∧
        (IsPSLType 2 (GaloisField 2 3) ↥(kStar p M H) ∨
          IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
            (fun B _ => Nat.card B = 3) ↥(kStar p M H) ∨
          IsSLType 3 (GaloisField 2 2) ↥(kStar p M H)) ∧
        CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 ∧
        ¬ xSub p M H ≤ M ∧ CFSG.HallHigman.IsPSolvable p ↥(xSub p M H)) :=
  (nineTenConclusion_of_twelveCtx h10 h hEQ hE hEc hΓ).1 hA

theorem nineTen_branchB_of_twelveCtx
    (h10 : NineTenGen) (h : TwelveCtx G M p Q H)
    {E : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) (hne : pLayerIn p H ≠ ⊥) (hle : pLayerIn p H ≤ M) :
    (p = 3 ∧
        (∃ S : Set (Subgroup G), S.ncard = 3 ∧
          (∀ J ∈ S, IsPComponentIn p J H ∧ CFSG.Open.pRank p J = 1) ∧
          pLayerIn p H = sSup S ∧
          ∀ J ∈ S, ∀ J' ∈ S, ∃ e ∈ E, J' = J.map (MulAut.conj e).toMonoidHom) ∧
        CFSG.pCore p (StarGroup p H) = ⊥ ∧
        IsPSLType 2 (ZMod 3) ↥(oPPrimeHull p (⊤ : Subgroup (QuotKer M H)))) ∨
      (3 < p ∧ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 ∧
        CFSG.Open.pRank p (pLayerIn p H) = 1 ∧
        oPPrimeHull p (⊤ : Subgroup (StarGroup p H)) =
          starImg p H (pLayerIn p H) ⊔ oPPrimeHull p (cStarL p H) ∧
        IsExtNotation (fun A _ => IsSLType 2 (ZMod p) A) (fun B _ => IsHomocyclicRank2 p B)
          ↥(oPPrimeHull p (cStarL p H))) ∨
      (p = 3 ∧ CFSG.Open.pRank p (starImg p H (pLayerIn p H)) ≤ 2 ∧
        CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 ∧
        CFSG.IsQuasisimple ↥(starImg p H (pLayerIn p H)) ∧
        IsPSLType 2 (ZMod 3) ↥(oPPrimeHull p (⊤ : Subgroup (QuotKer M H)))) :=
  (nineTenConclusion_of_twelveCtx h10 h hEQ hE hEc hΓ).2.1 hne hle

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
