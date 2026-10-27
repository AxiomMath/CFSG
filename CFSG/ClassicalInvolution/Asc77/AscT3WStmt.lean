module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIStmt
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Vocabulary

variable {G : Type} [Group G]

@[expose] def ModularOn (K W : Subgroup G) (b u : G) (k : ℕ) : Prop :=
  2 ≤ k ∧ Subgroup.zpowers u = K ⊓ W ∧ orderOf u = 2 ^ (k + 1) ∧
    ((∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
      ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k - 1))

structure FieldInv20 (S : Sylow 2 G) (K K' W : Subgroup G) (z t b : G) : Prop where
  mem : b ∈ (S : Subgroup G)
  sq : b * b = 1
  not_mem_X : b ∉ sec20X (CoreAssembly.conjClass K) z K K'
  comm_t : b * t = t * b
  fuse : ∃ c : G, c * b = b * c ∧ c * z * c⁻¹ = t
  modular : ∃ (u : G) (k : ℕ), ModularOn K W b u k

end Vocabulary

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Res10aInv' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z → 8 < Nat.card R →
          ∃ b : G, FieldInv20 S K K' W z t b

@[expose] def Res10aY' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z → 8 < Nat.card R →
          ∀ b : G, FieldInv20 S K K' W z t b →
            (∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G),
                ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K') ∧
              ∀ g : G, (g * z * g⁻¹) * b = b * (g * z * g⁻¹) →
                ∃ c : G, c * b = b * c ∧ c * z * c⁻¹ = g * z * g⁻¹

@[expose] def Res10aCyc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z → 8 < Nat.card R →
          ∀ b : G, FieldInv20 S K K' W z t b →
            ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G),
              ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K'

@[expose] def Res10aFus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z → 8 < Nat.card R →
          ∀ b : G, FieldInv20 S K K' W z t b →
            ∀ g : G, (g * z * g⁻¹) * b = b * (g * z * g⁻¹) →
              ∃ c : G, c * b = b * c ∧ c * z * c⁻¹ = g * z * g⁻¹

variable {p f}

theorem res10aY'_of_parts (h1 : Res10aCyc p f) (h2 : Res10aFus p f) : Res10aY' p f :=
  fun G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb =>
    ⟨h1 G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb,
      h2 G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb⟩

theorem Res10aY'.cyc (h : Res10aY' p f) : Res10aCyc p f :=
  fun G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb =>
    (h G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb).1

theorem Res10aY'.fus (h : Res10aY' p f) : Res10aFus p f :=
  fun G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb =>
    (h G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb).2

end CFSG.ClassicalInvolution.Asc77.T3CII
