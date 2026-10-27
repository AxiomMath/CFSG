module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

structure Chev204Hyp (p : ℕ) {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  core : GLAPPrimeCore p X = ⊥
  comp : GLAPComponent p ⊤ K
  scp : IsSCp p ⊤ B
  norm : B ≤ Subgroup.normalizer (K : Set X)
  chev : IsChevSimple p (↥K ⧸ Subgroup.center ↥K)

@[expose] def ChevExc (p : ℕ) {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop :=
  p = 3 ∧ ((IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K) ∧ ¬ InducesInnerIn B K) ∨
    (IsHatSix ↥K ∧ autOrderIn B K = 3))

@[expose] def DefCharOuterCoreFree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p → ¬ (p = 3 ∧ IsLTwoTwentySeven S) →
        ∀ d : MulAut S, orderOf d = p → d ∉ innerAut S → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
          GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut S))) = ⊥

@[expose] def ChevCentralizerStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X), Chev204Hyp p K B →
    I271LieType (· = p) K → Subgroup.center ↥K = ⊥ → ∀ a ∈ B, a ≠ 1 →
      ¬ (∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) →
      (∀ I J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) I →
        GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → I = J) ∧
      (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        IsChevSimple p (↥(barX p (Subgroup.centralizer ({a} : Set X)) J) ⧸
          Subgroup.center ↥(barX p (Subgroup.centralizer ({a} : Set X)) J)) ∧
        ¬ ChevExc p (barX p (Subgroup.centralizer ({a} : Set X)) J)
          (barX p (Subgroup.centralizer ({a} : Set X)) B))

@[expose] def ChevCyclicCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X), Chev204Hyp p K B →
    I271LieType (· = p) K → autOrderIn B K ≤ p → IsStronglyBalancedIn p B K ∨ ChevExc p K B

@[expose] def ChevAmbCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X), Chev204Hyp p K B →
    catalogIs (↥K ⧸ Subgroup.center ↥K) (ambiguousChev p) → ¬ ChevExc p K B →
      IsStronglyBalancedIn p B K

end CFSG.HardMathSupport.Dickson.I271
