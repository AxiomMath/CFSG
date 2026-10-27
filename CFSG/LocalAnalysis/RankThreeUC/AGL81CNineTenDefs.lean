module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups

@[expose] def oPPrimeHull (p : ℕ) {X : Type*} [Group X] (A : Subgroup X) : Subgroup X :=
  Subgroup.closure {x : X | x ∈ A ∧ ∃ k : ℕ, orderOf x = p ^ k}

@[expose] noncomputable def starImg {G : Type} [Group G] (p : ℕ) (H A : Subgroup G) :
    Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))

@[expose] def kerIn {G : Type} [Group G] (M K : Subgroup G) : Subgroup G :=
  (Subgroup.normalCore ((M ⊓ K).subgroupOf K)).map K.subtype

@[expose] def omegaOnePSub {G : Type} [Group G] (p : ℕ) (R : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ R ∧ x ^ p = 1}

@[expose] def IsSLType (n : ℕ) (F : Type) [CommRing F] (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* SL(n, F))

@[expose] def IsPSLType (n : ℕ) (F : Type) [CommRing F] (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* PSL(n, F))

@[expose] def IsHomocyclicRank2 (p : ℕ) (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    Nonempty (X ≃* (Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))))

@[expose] def IsQ8D8Type (X : Type) [Group X] : Prop :=
  ∃ Q E : Subgroup X, Nonempty (↥Q ≃* QuaternionGroup 2) ∧ Nonempty (↥E ≃* DihedralGroup 4) ∧
    (∀ q ∈ Q, ∀ e ∈ E, q * e = e * q) ∧ Q ⊔ E = ⊤ ∧ Nat.card ↥(Q ⊓ E) = 2

@[expose] def IsExtNotation (PA PB : ∀ (V : Type) [Group V], Prop) (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), PB ↥N ∧ PA (X ⧸ N) ∧
    ¬ ∃ H : Subgroup X, H.Normal ∧ N ⊓ H = ⊥ ∧ N ⊔ H = ⊤

@[expose] def IsTwoPrimeComponentIn {G : Type} [Group G] (L H : Subgroup G) : Prop :=
  L ≤ H ∧ (L.subgroupOf H).IsSubnormal ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
    L = Subgroup.closure {x : G | x ∈ L ∧ Odd (orderOf x)}

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
