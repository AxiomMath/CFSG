module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement LinearAlgebra.Projectivization MatrixGroups

variable {G : Type} [Group G]

@[expose] def perfCore (C : Subgroup G) : Subgroup G :=
  sSup {P : Subgroup G | P ≤ C ∧ ⁅P, P⁆ = P}

@[expose] def NonCentral (p : ℕ) [Fact p.Prime] {Q : Type*} [Group Q] (x : Q) : Prop :=
  ∀ S : Sylow p Q, x ∉ (Subgroup.center ↥(S : Subgroup Q)).map (S : Subgroup Q).subtype

structure Cover217 [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) : Prop where
  pair : Sec21Pair G A E U c L
  quot : Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3)
  mem : c ∈ L
  cover : Sec4.IsTripleCover (lBar L) NativeSporadic.J3
  card : Nat.card A = 3 ^ 4
  ext : Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3))

variable [Finite G]

theorem Cover217.c_comm {A E U : Subgroup G} {c : G} {L : Subgroup G} (h : Cover217 A E U c L) :
    ∀ x ∈ L, c * x = x * c := by
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hLc hx)).symm

theorem Cover217.isElemAbelian_A {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) : CFSG.Assembly.IsElemAbelian 3 A :=
  h.pair.mem_S.1.1

theorem Cover217.c_mem_A {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) : c ∈ A :=
  h.pair.mem_E.2 (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).1.1

structure Frame217 (E : Subgroup G) (c : G) (L : Subgroup G) (a : G) : Prop where
  mem : a ∈ E
  not_mem : a ∉ Subgroup.zpowers c
  proj : ∃ l : L, (∃ w ∈ Subgroup.centralizer (L : Set G), a = (l : G) * w) ∧
    NonCentral 3 (l : ↥L ⧸ Subgroup.center ↥L)

structure Valid217 (A : Subgroup G) (c : G) (L : Subgroup G) (a : G) : Prop where
  mem : a ∈ A
  not_mem : a ∉ Subgroup.zpowers c
  proj : ∃ l : L, (∃ w ∈ Subgroup.centralizer (L : Set G), a = (l : G) * w) ∧
    NonCentral 3 (l : ↥L ⧸ Subgroup.center ↥L)

theorem Frame217.valid {A E : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    (h : Frame217 E c L a) (hEA : E ≤ A) : Valid217 A c L a :=
  ⟨hEA h.mem, h.not_mem, h.proj⟩

@[expose] def iCore (L : Subgroup G) (a : G) : Subgroup G :=
  perfCore (Subgroup.centralizer ({a} : Set G) ⊓ L)

@[expose] def Sec217Frame : Prop :=
  ∀ (A E U : Subgroup G) (c : G) (L : Subgroup G), Cover217 A E U c L →
    ∃ a : G, Frame217 E c L a

@[expose] def Sec217ThetaOne : Prop :=
  ∀ (A E U : Subgroup G) (c : G) (L : Subgroup G), Cover217 A E U c L →
    aschbacherSolvableCore 3 L = ⊥

@[expose] def Sec217ALe : Prop :=
  ∀ (A E U : Subgroup G) (c : G) (L : Subgroup G), Cover217 A E U c L → A ≤ L

@[expose] def dGroup (a c : G) : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers c

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
