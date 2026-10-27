module

public import CFSG.LocalAnalysis.AGLEmbedding.Escape
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Vocabulary

variable {G : Type} [Group G]

@[expose] def barM (M X : Subgroup G) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
  (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))

structure IsTwoPrimeComponent (M L : Subgroup G) : Prop where
  le : L ≤ M
  subnormal : IsSubnormal L M
  perfect : ⁅L, L⁆ = L
  component : IsComponentOf (barM M L) ⊤

structure IsWeakSBlock (M S L : Subgroup G) : Prop extends IsTwoPrimeComponent M L where
  not_le_normalizer : ¬ L ≤ Subgroup.normalizer (S : Set G)

@[expose] def blockV (S L : Subgroup G) : Subgroup G := omegaOneCenterOf (pCoreOf 2 (L ⊔ S))

@[expose] def HasIrreducibleCommutatorQuotient (L V : Subgroup G) : Prop :=
  ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) < ⁅V, L⁆ ∧
    ∀ W : Subgroup G, ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ W → W ≤ ⁅V, L⁆ →
      L ≤ Subgroup.normalizer (W : Set G) →
        W = ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) ∨ W = ⁅V, L⁆

@[expose] def InClassXBlock (L : Subgroup G) : Prop :=
  IsShort2 L ∧ ((∃ n : ℕ, 1 ≤ n ∧ IsLin2Type L n) ∨ ∃ n : ℕ, 1 ≤ n ∧ IsAltType L (2 * n + 1))

@[expose] def IsParabolicTwo {X : Type*} [Group X] (L J : Subgroup X) : Prop :=
  J ≤ L ∧ ∃ T : Subgroup X, IsSylowTwoOf T L ∧ L ⊓ Subgroup.normalizer (T : Set X) ≤ J

@[expose] def IsClassicalOrG2Index : TauCeti.LieTypeIndex → Prop
  | .A _ q | .twistedA _ q | .B _ q | .D _ q | .twistedD _ q | .G2 q => q.p = 2
  | _ => False

@[expose] def IsClassicalTwoOrG2 (Y : Type) [Group Y] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2Index d.1 ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group))

@[expose] def IsOrthogonalTwo (Y : Type) [Group Y] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, (∃ m : ℕ, ∃ q : TauCeti.PrimePower, q.card = 2 ∧
      (d.1 = .D m q ∨ d.1 = .twistedD m q ∨ (m = 3 ∧ d.1 = .twistedA 3 q))) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))

@[expose] def NineThreeOne (L : Subgroup G) : Prop := InClassXBlock L

@[expose] def NineThreeTwo (M S L : Subgroup G) : Prop :=
  IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
    IsParabolicTwo (barM M L) (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∧
    barM M (S ⊓ L) = pCoreOf 2 (barM M (Subgroup.normalizer (S : Set G) ⊓ L))

@[expose] def NineThreeThree (M S L : Subgroup G) : Prop :=
  IsShort2 L ∧ IsOrthogonalTwo ↥(barM M L) ∧
    HasIrreducibleCommutatorQuotient L (blockV S L) ∧
    ∃ s ∈ S, S ≤ Subgroup.zpowers s ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ∧
      s ∉ L ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ∧
      Nat.card ↥⁅blockV S L, Subgroup.zpowers s⁆ = 2

@[expose] def NineThreeFour (M S L : Subgroup G) : Prop :=
  IsShort2 L ∧ Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) ∧
    Nat.card (blockU L) = 2 ^ 6 ∧
    Nonempty (↥(((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).map
      (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))) ≃* Equiv.Perm (Fin 4))

@[expose] def NineThreeFive (M L : Subgroup G) : Prop :=
  IsShort2 L ∧ Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) ∧ Nat.card (blockU L) = 2 ^ 4

@[expose] def NineThreeSix (M S L : Subgroup G) : Prop :=
  HasIrreducibleCommutatorQuotient L (blockV S L) ∧ ∃ n : ℕ,
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin (2 * n))) ∧
    Nonempty (↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin n))

@[expose] def NineThreeSeven (M S L : Subgroup G) : Prop :=
  HasIrreducibleCommutatorQuotient L (blockV S L) ∧ ∃ n : ℕ,
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin (4 * n))) ∧
    Nonempty (↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin n))

@[expose] def NineThreeEight (M S L : Subgroup G) : Prop :=
  let J := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  IsShort2 L ∧ ∃ N r : ℕ, Even N ∧ 2 * r ≤ N ∧ N - 2 * r ≠ 0 ∧ N - 2 * r ≠ 2 ∧
    N - 2 * r ≠ 4 ∧ Nonempty (↥(barM M L) ≃* alternatingGroup (Fin N)) ∧
    ∃ φ : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))),
      barM M (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤
          Subgroup.normalizer ((((MonoidHom.snd _ _).comp
            (φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)))).ker.map J.subtype :
              Subgroup _) : Set _) ∧
      barM M (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤
          Subgroup.normalizer ((((MonoidHom.fst _ _).comp
            (φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)))).ker.map J.subtype :
              Subgroup _) : Set _)

@[expose] def NineThreeConclusion (M S L : Subgroup G) : Prop :=
  NineThreeOne L ∨ NineThreeTwo M S L ∨ NineThreeThree M S L ∨ NineThreeFour M S L ∨
    NineThreeFive M L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L

structure IsFooteBlock (H J : Subgroup G) : Prop where
  le : J ≤ H
  subnormal : IsSubnormal J H
  residual : ∀ (N : Subgroup J) [N.Normal], IsPGroup 2 (J ⧸ N) → N = ⊤
  quasisimple : Open.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)
  chief : blockZ J < blockU J ∧ ∀ W : Subgroup G, blockZ J ≤ W → W ≤ blockU J →
    J ≤ Subgroup.normalizer (W : Set G) → W = blockZ J ∨ W = blockU J

structure Asc81bHyp (X S : Subgroup G) : Prop where
  twoRadical : IsTwoRadicalIn X S
  charTwo : CharTwo X
  cgs : cgsIn X S = X ⊓ Subgroup.normalizer (S : Set G)

end Vocabulary

structure D1PhaseThree {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M H R : Subgroup G) : Prop extends D1Escape p P M H R where
  glob : CFSG.AGLEmbeddingD2.AGLGlobal G
  twoCore_inf : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H

end CFSG.AGLEmbedding
