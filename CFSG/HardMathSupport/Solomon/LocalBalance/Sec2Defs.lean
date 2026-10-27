module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

abbrev CBar (p : ℕ) (b : G) : Type _ :=
  ↥(Subgroup.centralizer ({b} : Set G)) ⧸ GLAPPrimeCore p ↥(Subgroup.centralizer ({b} : Set G))

@[expose] def barImageAt (p : ℕ) (b : G) (Y : Subgroup G) : Subgroup (CBar p b) :=
  (Y.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
    (QuotientGroup.mk' (GLAPPrimeCore p ↥(Subgroup.centralizer ({b} : Set G))))

@[expose] def barCenterAt (p : ℕ) (b : G) (K : Subgroup G) : Subgroup (CBar p b) :=
  (Subgroup.center ↥(barImageAt p b K)).map (barImageAt p b K).subtype

@[expose] def IsSLThreeExc (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), (Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) ∧
    Nonempty (X ≃* ↥(StatedSL 3 K))

@[expose] def IsSUThreeExc (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧
    (q % 9 = 2 ∨ q % 9 = 5) ∧ Nonempty (X ≃* ↥(StatedSU 3 q K))

@[expose] def IsSLThree (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nonempty (X ≃* ↥(StatedSL 3 K))

@[expose] def IsSUThree (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧
    Nonempty (X ≃* ↥(StatedSU 3 q K))

@[expose] def delta2At (p : ℕ) (B D : Subgroup G) (b : G) : Subgroup G :=
  ⁅GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G), B⁆

structure Lemma24Setup [Finite G] (p : ℕ) (B D : Subgroup G) (b : G) (L : Subgroup G) : Prop where
  isBOneMax : IsBOneMax p B
  isEk : IsEkIn p 2 B D
  mem : b ∈ B
  ne_one : b ≠ 1
  not_le : ¬ delta2At p B D b ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))
  isComp : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L
  not_centralizes :
    ¬ ⁅L, delta2At p B D b⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))

@[expose] def Lemma24Conclusion (B D : Subgroup G) (b : G) (L : Subgroup G) : Prop :=
  (Subgroup.normalizer (L : Set G)).relIndex B = 3 ∧
  (IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) ∧
  (D ≤ Subgroup.normalizer (L : Set G) ∧ delta2At 3 B D b ≤ Subgroup.normalizer (L : Set G) ∧
    (((delta2At 3 B D b).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) ≠ ⊥ ∧
      ((delta2At 3 B D b).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) ≤
        localDeltaIn 3
          (((delta2At 3 B D b ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L))
          ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L)))) ∧
  (IsElemAbelian 3 (Subgroup.center ↥(barImageAt 3 b (bClosure B L))) ∧
    Nat.card (Subgroup.center ↥(barImageAt 3 b (bClosure B L))) ≤ 9) ∧
  (barCenterAt 3 b (bClosure B L) ⊓ Subgroup.centralizer (barImageAt 3 b B : Set (CBar 3 b)) ≤
    barImageAt 3 b B)

@[expose] def IsBConjugate (B L L' : Subgroup G) : Prop :=
  ∃ g ∈ B, L' = GLBConj g L

end CFSG.HardMathSupport.Solomon.LocalBalance
