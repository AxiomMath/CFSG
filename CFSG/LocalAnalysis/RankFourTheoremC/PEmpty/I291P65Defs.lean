module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Facts
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def SCCaseTwo : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X), Plane63 p X P x z →
    ∀ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ →
      (∀ K : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf K ⊤ → K = L) →
      ¬ IsLinearOrUnitaryAt p (↥L ⧸ center ↥L) →
      ∀ W : Subgroup X, Nat.Coprime p (Nat.card W) →
        zpowers x ⊔ zpowers z ≤ normalizer (W : Set X) → W ≤ primeComplementCore (G := X) p

@[expose] def Is29a (L : Type) [Group L] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), 5 ∣ Nat.card K - 1 ∧
      (Nonempty (L ≃* ↥(StatedSL 5 K)) ∨ Nonempty (L ≃* StatedProj (StatedSL 5 K)))) ∨
    (∃ (q : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧ 5 ∣ q + 1 ∧
      (Nonempty (L ≃* ↥(StatedSU 5 q K)) ∨ Nonempty (L ≃* StatedProj (StatedSU 5 q K))))

@[expose] def KD29LinUni : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 5 Y) (x z : Y), Plane63 5 Y P x z →
    ∀ L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf K ⊤ → K = L) →
      IsLinearOrUnitaryAt 5 (↥L ⧸ center ↥L) → Is29a ↥L

@[expose] def KD309 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 5 Y) (x z : Y), Plane63 5 Y P x z →
    ∀ L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf K ⊤ → K = L) →
      Is29a ↥L →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
        (ρ : Representation (ZMod 2) Y V), IsPGroup 2 ρ.ker →
          20 < Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65
