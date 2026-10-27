module

public import CFSG.ClassicalInvolution.Q3.TL3Induct
public import CFSG.ClassicalInvolution.SmallCases.SectionalFourBranch

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

@[expose] def fstarCenter (Y : Type) [Group Y] : Subgroup Y :=
  (Subgroup.center ↥(genFittingFStar Y)).map (genFittingFStar Y).subtype

@[expose] def SmallM11 (F : Type) [Group F] : Prop := NativeSporadic.IsSporadic F .M11

@[expose] def SmallM12 (F : Type) [Group F] : Prop := NativeSporadic.IsSporadic F .M12

@[expose] def SmallL2 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Assembly.LowTwoRank.StatedClassicalModel F .PSL 2 p f

@[expose] def SmallL3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Assembly.LowTwoRank.StatedClassicalModel F .PSL 3 p f

@[expose] def SmallU3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 p f

@[expose] def SmallG2 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel F .G2 0 p f

@[expose] def SmallD4 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel F .trialityD4 0 p f

@[expose] def SmallPSp4 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel F .PSp 2 p f

@[expose] def SmallTwistedG2 (F : Type) [Group F] : Prop :=
  ∃ f : ℕ, LieModel F .twistedG2 0 3 f

@[expose] def SmallL4 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧ LieModel F .PSL 4 p f

@[expose] def SmallU4 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧ LieModel F .PSU 4 p f

@[expose] def SmallL5 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ LieModel F .PSL 5 p f

@[expose] def SmallU5 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ LieModel F .PSU 5 p f

@[expose] def SmallFamily (F : Type) [Group F] : Prop :=
  SmallG2 F ∨ SmallD4 F ∨ SmallPSp4 F ∨ SmallTwistedG2 F ∨ SmallL4 F ∨ SmallU4 F ∨ SmallL5 F ∨
    SmallU5 F ∨ SmallM12 F ∨ SmallL2 F ∨ SmallL3 F ∨ SmallU3 F ∨ SmallM11 F

@[expose] def SmallSimpleLeaf (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)],
    CIT3Below (Nat.card Y) → (∃ a b : genFittingFStar Y, a * b ≠ b * a) →
    TwoSubgroupsFourGenerated (genFittingFStar Y) → P (genFittingFStar Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightEx Y R S t ∨ GoodThreeElement R t

@[expose] def SmallTwinLeaf : Prop :=
  GH74SectionalModels →
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → TightFStarQuasisimple Y →
    TwoSubgroupsFourGenerated (genFittingFStar Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → ∀ c ∈ fstarCenter Y, c ≠ 1 → (∃ y : Y, y * t * y⁻¹ = t * c) →
        GoodThreeElement R t

structure SmallLeaves : Prop where
  m11 : SmallSimpleLeaf SmallM11
  m12 : SmallSimpleLeaf SmallM12
  l2 : SmallSimpleLeaf SmallL2
  l3 : SmallSimpleLeaf SmallL3
  u3 : SmallSimpleLeaf SmallU3
  g2 : SmallSimpleLeaf SmallG2
  d4 : SmallSimpleLeaf SmallD4
  psp4 : SmallSimpleLeaf SmallPSp4
  twistedG2 : SmallSimpleLeaf SmallTwistedG2
  l4 : SmallSimpleLeaf SmallL4
  u4 : SmallSimpleLeaf SmallU4
  l5 : SmallSimpleLeaf SmallL5
  u5 : SmallSimpleLeaf SmallU5
  twin : SmallTwinLeaf

end CFSG.ClassicalInvolution.Q3.TA3
