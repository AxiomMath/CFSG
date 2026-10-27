module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def NineTenOne {G : Type} [Group G] [Finite G] (p : ℕ) (M H : Subgroup G) : Prop :=
  (xSub p M H ≤ M ∧ H = kSub p M H ⊔ (H ⊓ M) ∧ ((kSub p M H).subgroupOf H).Normal) ∨
    (p = 3 ∧
      (IsPSLType 2 (GaloisField 2 3) ↥(kStar p M H) ∨
        IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
          (fun B _ => Nat.card B = 3) ↥(kStar p M H) ∨
        IsSLType 3 (GaloisField 2 2) ↥(kStar p M H)) ∧
      CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 ∧
      ¬ xSub p M H ≤ M ∧ CFSG.HallHigman.IsPSolvable p ↥(xSub p M H))

@[expose] def NineTenTwo {G : Type} [Group G] [Finite G] (p : ℕ) (M H E : Subgroup G) : Prop :=
  (p = 3 ∧
      (∃ S : Set (Subgroup G), S.ncard = 3 ∧
        (∀ J ∈ S, IsPComponentIn p J H ∧ CFSG.Open.pRank p J = 1) ∧ pLayerIn p H = sSup S ∧
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
      IsPSLType 2 (ZMod 3) ↥(oPPrimeHull p (⊤ : Subgroup (QuotKer M H))))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
