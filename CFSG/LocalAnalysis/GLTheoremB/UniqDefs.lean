module

public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.Open.StatedDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.GLBDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsCharIn (T₀ T : Subgroup G) : Prop :=
  T₀ ≤ T ∧ ∀ ψ : ↥T ≃* ↥T, ∀ x : ↥T, (x : G) ∈ T₀ → ((ψ x : ↥T) : G) ∈ T₀

@[expose] def gammaOne (T : Subgroup G) : Subgroup G :=
  T ⊓ ⨅ (T₀ : Subgroup G) (_ : T₀ ≠ ⊥ ∧ IsCharIn T₀ T),
    pCoreOf 2 (Subgroup.normalizer (T₀ : Set G))

@[expose] def gammaIter (T : Subgroup G) : ℕ → Subgroup G
  | 0 => T
  | n + 1 => gammaOne (gammaIter T n)

@[expose] def gammaInf (T : Subgroup G) : Subgroup G :=
  ⨅ n : ℕ, gammaIter T (n + 1)

@[expose] def sigmaStar (D : Subgroup G) : Subgroup G :=
  ⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1), pCoreOf 2 (Subgroup.centralizer ({d} : Set G))

@[expose] def sigmaOf (D : Subgroup G) : Subgroup G :=
  pCoreOf 2 (sigmaStar D)

@[expose] def gammaD (D : Subgroup G) : Subgroup G :=
  gammaInf (sigmaOf D)

@[expose] def IsHatSeven (X : Type*) [Group X] : Prop :=
  commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 7))

@[expose] def alphaOf (p : ℕ) (M : Subgroup G) : Subgroup G :=
  pCoreOf 2 M ⊔ ⨆ (J : Subgroup G) (_ : p = 3 ∧ J ≤ M ∧ IsSubnormal J M ∧ ⁅J, J⁆ = J ∧
    IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J)), J

@[expose] def IsOmegaTwo (ε : Bool) (n : ℕ) (X : Type*) [Group X] : Prop :=
  match ε with
  | true => Nonempty (X ≃* ↥(StatedOmega (StatedQuadPlus n (ZMod 2))))
  | false => Nonempty (X ≃* ↥(StatedOmega (StatedQuadMinus n (ZMod 2) 1 1)))

@[expose] def HasFixedPointFreeOrder (ε : Bool) (n p : ℕ) : Prop :=
  match ε with
  | true => ∃ A ∈ StatedOmega (StatedQuadPlus n (ZMod 2)), orderOf A = p ∧
      ∀ v : Fin n ⊕ Fin n → ZMod 2, Matrix.mulVec (A : Matrix _ _ (ZMod 2)) v = v → v = 0
  | false => ∃ A ∈ StatedOmega (StatedQuadMinus n (ZMod 2) 1 1), orderOf A = p ∧
      ∀ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 2,
        Matrix.mulVec (A : Matrix _ _ (ZMod 2)) v = v → v = 0

@[expose] def IsPiGroup (p : ℕ) (L : Type*) [Group L] : Prop :=
  IsQuasisimple L ∧ GLAPPrimeCore p L = ⊥ ∧
    ((∃ k : ℕ, Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin (k * p + 2)))) ∨
      (∃ (n : ℕ) (ε : Bool), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (L ⧸ Subgroup.center L) ∧
        HasFixedPointFreeOrder ε n p) ∨
      (p = 3 ∧ Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7))))

@[expose] def piLayer (p : ℕ) (H : Subgroup G) : Subgroup G :=
  ⨆ (L : Subgroup G) (_ : GLAPComponent p H L ∧ IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L)), L

@[expose] def piOf (p : ℕ) (x : G) : Subgroup G :=
  piLayer p (Subgroup.centralizer ({x} : Set G))

@[expose] def piStar (p : ℕ) (D : Subgroup G) : Subgroup G :=
  ⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1),
    piOf p d ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))

@[expose] def gammaStar (p : ℕ) (D : Subgroup G) : Subgroup G :=
  gammaD D ⊓ pCoreOf 2 (piStar p D)

@[expose] def IsPreUniquenessTwoLocal [Finite G] (p : ℕ) (B M : Subgroup G) : Prop :=
  GLAIsMaxTwoLocal M ∧ lambdaStarGroup p B ≤ M ∧ GLBCore p 3 B ≤ M

@[expose] def IsTwoPrimeComp (X J : Subgroup G) : Prop :=
  J ≤ X ∧ IsSubnormal J X ∧ ⁅J, J⁆ = J ∧
    IsComponentOf ((J.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ⊤

@[expose] def IsSLThreeFour (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧ Nonempty (X ≃* ↥(StatedSL 3 K))

@[expose] def IsLThreeFour (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
    Nonempty (X ≃* StatedProj (StatedSL 3 K))

structure IsUniquenessTwoLocal [Finite G] (p : ℕ) (A N : Subgroup G) : Prop where
  maxTwoLocal : GLAIsMaxTwoLocal N
  le : A ≤ N
  elemAbelian : IsElemAbelian p A
  two_le_rank : 2 ≤ pRank p A
  clause_a : ∀ a ∈ A, a ≠ 1 →
    GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) ⊔ piOf p a ≤ N
  clause_b : ∀ a ∈ A, a ≠ 1 →
    pCoreOf 2 (alphaOf p N ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      pCoreOf 2 (Subgroup.centralizer ({a} : Set G))
  clause_c : ∀ D : Subgroup G, D ≤ A → IsPPlane p D →
    pCoreOf 2 N ≤ gammaStar p D ∧ ∀ T : Subgroup G, pCoreOf 2 N ≤ T → T ≤ gammaStar p D →
      Subgroup.normalizer (T : Set G) ≤ N
  clause_d : GLBCore p 2 A ≤ N
  clause_e : p = 3 → ∀ a ∈ A, a ≠ 1 → ∀ L : Subgroup G,
    GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) L →
      (IsLThreeFour (↥L ⧸ GLAPPrimeCore 3 ↥L) ∨ IsSLThreeFour (↥L ⧸ GLAPPrimeCore 3 ↥L)) → L ≤ N
  clause_f : p = 3 → ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup G,
    IsTwoPrimeComp (alphaOf p N ⊓ Subgroup.centralizer ({a} : Set G)) J →
      IsTwoPrimeComp (Subgroup.centralizer ({a} : Set G)) J

end CFSG.LocalAnalysis.GLTheoremB
