module

public import CFSG.GH74.GLS.LU.Compat
public import CFSG.GH74.M12.Statements
public import CFSG.GH74.GLS.Statements

public section

namespace CFSG.GH74.GLS.Stage12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

structure Std (G : Type) [Group G] [Finite G] : Prop where
  kps : IsKProperSimple G
  gen4 : Gen4 G
  kgh : KGH G
  rank : 3 ≤ pRank 2 G ∧ pRank 2 G ≤ 4
  nonab : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)
  lb2 : IsLB2Type G
  noUniq : ¬ HasTwoUniquenessSubgroup G

structure Std0 (G : Type) [Group G] [Finite G] : Prop where
  kps : IsKProperSimple G
  gen4 : Gen4 G
  kgh : KGH G
  rank : 3 ≤ pRank 2 G ∧ pRank 2 G ≤ 4
  nonab : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)

theorem Std.toStd0 {G : Type} [Group G] [Finite G] (h : Std G) : Std0 G :=
  ⟨h.kps, h.gen4, h.kgh, h.rank, h.nonab⟩

inductive Kind : Type
  | g2 | m12 | psp4 | l4 (ε : Bool) | mcl | ly

@[expose] def Asc03Data (G : Type) [Group G] : Prop :=
  ∃ z : G, IsCentralInvolution z ∧ M12.Asc03Hyp G z ∧
    ∃ K ∈ M12.q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), K.Normal

@[expose] def StageFourInput (G : Type) [Group G] [Finite G] : Prop :=
  Asc03Data G ∨ ∃ (Gs : Type) (_ : Group Gs), IsTwoCentralG2Type G Gs

@[expose] def OneClassDoubleCover (G : Type) [Group G] (n : ℕ) : Prop :=
  ∃ z : G, IsCentralInvolution z ∧ (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) ∧
    IsDoubleCoverOfAlt ↥(centralizer ({z} : Set G)) n

@[expose] def McLLyData (G : Type) [Group G] : Prop :=
  OneClassDoubleCover G 8 ∨ OneClassDoubleCover G 11

@[expose] def S_noTwoAnNineTen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → ¬ OneClassDoubleCover G 9 ∧ ¬ OneClassDoubleCover G 10

@[expose] def TwoCentralClassicalData (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] :
    Prop :=
  LU.IsTwoCentralClassicalTypeCompat G Gs

@[expose] def Max6A (G : Type) [Group G] (p f : ℕ) : Prop :=
  ∀ z : G, IsCentralInvolution z → ∀ M : Subgroup G, IsCoatom M → centralizer ({z} : Set G) < M →
    IsCoatom ((centralizer ({z} : Set G)).subgroupOf M) ∧
      LieModel ↥(generalizedFitting ↥M) .PSp 2 p f

@[expose] def StageFiveClassical (G : Type) [Group G] [Finite G] : Prop :=
  ∃ (Gs : Type) (_ : Group Gs),
    ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧ LieModel Gs .PSp 2 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
        ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f)) ∧
        Max6A G p f)) ∧
    TwoCentralClassicalData G Gs

@[expose] def StageFiveInput (G : Type) [Group G] [Finite G] : Prop :=
  McLLyData G ∨ StageFiveClassical G

@[expose] def S_McL_leaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    OneClassDoubleCover G 8 → NativeSporadic.IsSporadic G .McL

@[expose] def S_Ly_leaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    OneClassDoubleCover G 11 → NativeSporadic.IsSporadic G .Ly

@[expose] def S_stage1_thm2_Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std0 G →
    (∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ pRank 2 ↥K = 1) →
      ∃ z : G, IsStronglyClassicalInvolution G z ∧
        ∃ t : G, t ∈ centralizer ({z} : Set G) ∧ IsConj z t ∧ t ∉ zStar (rigidProduct z)

@[expose] def S_stage4_Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 → IsLBStar2Type G → StageFourInput G

@[expose] def S_stage2Four_Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 4 → HasTwoThinConfiguration G →
    StageFiveInput G

@[expose] def S_ch6_Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 → StageFourInput G →
    (∃ f : ℕ, LieModel G .twistedG2 0 3 f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 < p ^ f ∧ LieModel G .G2 0 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel G .trialityD4 0 p f) ∨
      Asc03Data G

@[expose] def S_C2starFour_Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 4 → HasTwoThinConfiguration G →
    C2StarList G

end CFSG.GH74.GLS.Stage12
