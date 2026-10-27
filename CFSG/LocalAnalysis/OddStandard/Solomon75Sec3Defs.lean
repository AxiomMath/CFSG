module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Balance
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Quot

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

@[expose] def IsIntrinsicIn (X : Type) [Group X] (H L : Subgroup X) (u : X) : Prop :=
  orderOf u = 2 ∧ u ∈ L ∧ IsPCompIn 2 H L ∧
    L = pPrimeCoreOf 2 L ⊔ oPrimeResidualOf 2 (L ⊓ centralizer ({u} : Set X)) ∧
    ∃ Lu : Subgroup X, IsAhatIntr X u Lu ∧
      Lu = pPrimeCoreOf 2 Lu ⊔ oPrimeResidualOf 2 (L ⊓ centralizer ({u} : Set X))

@[expose] def K0 (X : Type) [Group X] (n : ℕ) (H : Subgroup X) : Subgroup X :=
  sSup {L : Subgroup X | (∃ u : X, IsIntrinsicIn X H L u) ∧
    IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) n}

@[expose] def IsSylowTwoIn {X : Type} [Group X] (W Z : Subgroup X) : Prop :=
  Z ≤ W ∧ IsPGroup 2 ↥Z ∧ ¬ 2 ∣ Z.relIndex W

structure IsSec5Pair (X : Type) [Group X] (n : ℕ) (z : X) (Z : Subgroup X) : Prop where
  orderOf_z : orderOf z = 2
  mem : z ∈ Z
  sylow : IsSylowTwoIn (zStar (K0 X n (centralizer ({z} : Set X)))) Z

@[expose] def pTwoCoreOf {X : Type} [Group X] (H : Subgroup X) : Subgroup X :=
  (pCore 2 ↥H).map H.subtype

@[expose] def Lemma33a (X : Type) [Group X] (n : ℕ) (Z : Subgroup X) : Prop :=
  ∀ s : X, s ∈ normalizer (Z : Set X) → orderOf s = 2 →
    (∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) →
    centralizer ({s} : Set X) =
      oddCoreOf (centralizer ({s} : Set X)) ⊔ (normalizer (Z : Set X) ⊓ centralizer ({s} : Set X))

@[expose] def Lemma33b (X : Type) [Group X] (n : ℕ) (Z : Subgroup X) : Prop :=
  Z = pTwoCoreOf (K0 X n (normalizer (Z : Set X))) ∧
    IsSylowTwoIn (oddTwoCoreOf (K0 X n (normalizer (Z : Set X)))) Z

theorem oPrimeResidualOf_two_eq_oTwoPrimeOf {X : Type} [Group X] (H : Subgroup X) :
    oPrimeResidualOf 2 H = oTwoPrimeOf H := by
  unfold oPrimeResidualOf oPrimeResidual oTwoPrimeOf
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩

theorem oTwoPrimeOf_eq_self_of_primeResidual {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (h : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 2 ↥L = ⊤) :
    oTwoPrimeOf L = L := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (oTwoPrimeOf_le L) fun x hx => ?_
  have hxT : (⟨x, hx⟩ : ↥L) ∈
      CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 2 ↥L := by
    rw [h]; exact Subgroup.mem_top _
  rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure] at hxT
  have hmap : (Subgroup.closure {y : ↥L | ∃ k : ℕ, orderOf y = 2 ^ k}).map L.subtype ≤
      oTwoPrimeOf L := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
    refine mem_oTwoPrimeOf y.2 k ?_
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, ← hk, pow_orderOf_eq_one, Subgroup.coe_one]
  exact hmap ⟨⟨x, hx⟩, hxT, rfl⟩

theorem IsAhatIntr.isIntrinsicIn {X : Type} [Group X] [Finite X] {u : X} {L : Subgroup X}
    (hu : orderOf u = 2) (h : IsAhatIntr X u L) :
    IsIntrinsicIn X (centralizer ({u} : Set X)) L u := by
  have hq : IsTwoGenQuasi ↥L := isTwoGenQuasi_of_isAhatIntr h
  have heq : L = pPrimeCoreOf 2 L ⊔ oPrimeResidualOf 2 (L ⊓ centralizer ({u} : Set X)) := by
    rw [inf_of_le_left h.1, oPrimeResidualOf_two_eq_oTwoPrimeOf,
      oTwoPrimeOf_eq_self_of_primeResidual hq.1]
    refine (sup_eq_right.2 ?_).symm
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  exact ⟨hu, h.2.1, ⟨h.1, h.2.2.1⟩, heq, L, h, heq⟩

end CFSG.OddStandard.Solomon75
