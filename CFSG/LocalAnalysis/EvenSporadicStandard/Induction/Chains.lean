module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

abbrev GroupClass : Type 1 := ∀ (X : Type) [Group X], Prop

@[expose] def centerIn (A : Subgroup H) : Subgroup H := (center ↥A).map A.subtype

@[expose] def StdModulo (Y Z K : Subgroup H) : Prop :=
  ∃ hZ : (Z.subgroupOf Y).Normal,
    @StdBare (↥Y ⧸ Z.subgroupOf Y) (@QuotientGroup.Quotient.group ↥Y _ _ hZ)
      ((K.subgroupOf Y).map (@QuotientGroup.mk' ↥Y _ _ hZ))

@[expose] def OddLieFour (X : Type) [Group X] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
    (CFSG.Blueprint.LieModel X .PSL 4 p f ∨ CFSG.Blueprint.LieModel X .PSU 4 p f ∨
      CFSG.Blueprint.LieModel X .PSp 2 p f ∨ CFSG.Blueprint.LieModel X .G2 0 p f)

@[expose] def IsSL2Odd (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) K)

@[expose] def FS79Link5b (Li Lp Ti : Subgroup H) : Prop :=
  Li = conjClosure Lp (layerIn (centralizer (Ti : Set H))) ∧ IsSL2Odd ↥Lp ∧
    OddLieFour (↥Li ⧸ center ↥Li)

@[expose] def Sol78Link5a (Li Lp : Subgroup H) (s : H) : Prop :=
  Li ≠ Li.map (MulAut.conj s).toMonoidHom ∧ Nonempty ((↥Li ⧸ center ↥Li) ≃* (↥Lp ⧸ center ↥Lp))

@[expose] def Sol78Link5b (Li Lp : Subgroup H) (s : H) : Prop :=
  Li = Li.map (MulAut.conj s).toMonoidHom ∧
    StdModulo (Li ⊔ zpowers s) (centralizer (Li : Set H)) Lp

structure Sol78Chain23 (H : Type) [Group H] (N : Subgroup H) (n : ℕ) (L T : ℕ → Subgroup H)
    (s : ℕ → H) : Prop where
  last : L n = N
  inj : ∀ i ≤ n, ∀ j ≤ n, L i = L j → i = j
  comp : ∀ i ≤ n, IsPGroup 2 (T i) ∧ IsCompIn (L i) (centralizer (T i : Set H))
  elem : ∀ i, 1 ≤ i → i ≤ n → IsPGroup 2 (zpowers (s i)) ∧ s i ∈ normalizer (T i : Set H) ∧
    s i ^ 2 ∈ T i ∧
      IsCompIn (L (i - 1)) (centralizer ((T i ⊔ zpowers (s i) : Subgroup H) : Set H))
  incl : ∀ i, 1 ≤ i → i ≤ n →
    L (i - 1) ≤ L i ⊔ (L i).map (MulAut.conj (s i)).toMonoidHom ∧
      L i ⊔ (L i).map (MulAut.conj (s i)).toMonoidHom =
        conjClosure (L (i - 1)) (layerIn (centralizer (T i : Set H)))
  link : ∀ i, 1 ≤ i → i ≤ n →
    Sol78Link5a (L i) (L (i - 1)) (s i) ∨ Sol78Link5b (L i) (L (i - 1)) (s i)

@[expose] def IsKChain (IsK : GroupClass) (N : Subgroup H) (m : ℕ) : Prop :=
  ∃ (L T : ℕ → Subgroup H) (s : ℕ → H), Sol78Chain23 H N m L T s ∧ IsK ↥(L 0)

@[expose] def IsMaxKChain (IsK : GroupClass) (N : Subgroup H) (n : ℕ) : Prop :=
  IsKChain IsK N n ∧ ∀ m, IsKChain IsK N m → m ≤ n

end CFSG.EvenSporadicStandard.Induction
