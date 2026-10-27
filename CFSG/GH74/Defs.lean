module

public import CFSG.Foundations.Basic
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.GH74

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def SectionalTwoRankLE (X : Type*) [Group X] (r : ℕ) : Prop :=
  ∀ P : Subgroup X, IsPGroup 2 P →
    ∃ s : Finset X, s.card ≤ r ∧ Subgroup.closure (s : Set X) = P

@[expose] def Gen4 (X : Type*) [Group X] : Prop :=
  SectionalTwoRankLE X 4

@[expose] noncomputable def sectionalTwoRank (X : Type*) [Group X] : ℕ :=
  sInf {r | SectionalTwoRankLE X r}

@[expose] def IsTwoConstrained (Y : Type*) [Group Y] : Prop :=
  IsCharacteristicP 2 (Y ⧸ pPrimeCore 2 Y)

@[expose] def IsCentralInvolution {G : Type*} [Group G] (z : G) : Prop :=
  orderOf z = 2 ∧ ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), s * z = z * s

abbrev CentralizerBar {G : Type*} [Group G] (x : G) : Type _ :=
  ↥(centralizer ({x} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({x} : Set G))

@[expose] def layerBar {G : Type*} [Group G] (x : G) : Subgroup (CentralizerBar x) :=
  layer (CentralizerBar x)

@[expose] def AllComponentsNonsimple {G : Type*} [Group G] (x : G) : Prop :=
  ∀ K : Subgroup (CentralizerBar x), IsComponent K → ¬ IsSimpleGroup K

@[expose] def HasSimpleComponent {G : Type*} [Group G] (x : G) : Prop :=
  ∃ K : Subgroup (CentralizerBar x), IsComponent K ∧ IsSimpleGroup K

@[expose] def GHList (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
  (NativeSporadic.IsSporadic X .M11 ∨ NativeSporadic.IsSporadic X .M12 ∨
    NativeSporadic.IsSporadic X .M22 ∨ NativeSporadic.IsSporadic X .M23 ∨
    NativeSporadic.IsSporadic X .J1 ∨ NativeSporadic.IsSporadic X .J2 ∨
    NativeSporadic.IsSporadic X .J3 ∨ NativeSporadic.IsSporadic X .McL ∨
    NativeSporadic.IsSporadic X .Ly) ∨
  (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧
    ((p ≠ 2 ∧ (LieModel X .PSL 2 p f ∨ LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f ∨
        LieModel X .PSp 2 p f ∨ LieModel X .G2 0 p f ∨ LieModel X .trialityD4 0 p f)) ∨
      (p ≠ 2 ∧ p ^ f % 8 ≠ 1 ∧ LieModel X .PSL 4 p f) ∨
      (p ≠ 2 ∧ p ^ f % 8 ≠ 7 ∧ LieModel X .PSU 4 p f) ∨
      (p ^ f % 4 = 3 ∧ LieModel X .PSL 5 p f) ∨
      (p ^ f % 4 = 1 ∧ LieModel X .PSU 5 p f) ∨
      LieModel X .twistedG2 0 3 f ∨
      (p = 2 ∧ (LieModel X .PSL 2 2 3 ∨ LieModel X .PSL 2 2 4 ∨ LieModel X .PSL 3 2 2 ∨
        LieModel X .PSU 3 2 2 ∨ LieModel X .twistedB2 0 2 3))))

@[expose] def KGH (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, H ≠ ⊤ → ∀ (N : Subgroup H) (_ : N.Normal),
    IsSimpleGroup (H ⧸ N) → (∃ a b : H ⧸ N, a * b ≠ b * a) → GHList (H ⧸ N)

@[expose] def R1 (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ 3 ≤ Open.twoRank G ∧
    (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) ∧ Gen4 G ∧ KGH G ∧
    (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) ∧
    (∀ x : G, orderOf x = 2 → Group.IsSolvable (centralizer ({x} : Set G)) ∨
      ¬ IsTwoConstrained (centralizer ({x} : Set G))) ∧
    ¬ ∃ x : G, orderOf x = 2 ∧ sectionalTwoRank (layerBar x) = 4 ∧ AllComponentsNonsimple x

abbrev QuaternionDihedralCentralProduct : Type :=
  (QuaternionGroup 2 × DihedralGroup 4) ⧸
    Subgroup.normalClosure {((QuaternionGroup.a 2 : QuaternionGroup 2), (DihedralGroup.r 2 :
      DihedralGroup 4))}

end CFSG.GH74
