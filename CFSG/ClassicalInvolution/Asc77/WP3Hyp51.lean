module

public import CFSG.ClassicalInvolution.Asc77.WP2Defs
public import CFSG.ClassicalInvolution.Asc77.WP3Fuzzy

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected

section Induced

variable {H : Type} [Group H]

@[expose] def conjOnNormalizer (L : Subgroup H) :
    ↥(Subgroup.normalizer (L : Set H)) →* MulAut ↥L where
  toFun x :=
    { toFun := fun y => ⟨(x : H) * y * (x : H)⁻¹, (Subgroup.mem_normalizer_iff.mp x.2 y).mp y.2⟩
      invFun := fun y => ⟨(x : H)⁻¹ * y * (x : H), (Subgroup.mem_normalizer_iff.mp x.2 _).mpr (by
        have e : (x : H) * ((x : H)⁻¹ * y * (x : H)) * (x : H)⁻¹ = y := by group
        rw [e]
        exact y.2)⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun y z => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext y
    simp
  map_mul' := fun x x' => by
    ext y
    simp [mul_assoc]

@[expose] def inducedAutOn (L : Subgroup H) : Subgroup (MulAut ↥L) :=
  (conjOnNormalizer L).range

@[expose] def toInducedAutOn (L : Subgroup H) :
    ↥(Subgroup.normalizer (L : Set H)) →* ↥(inducedAutOn L) :=
  (conjOnNormalizer L).rangeRestrict

@[expose] def inducedImage (L : Subgroup H) (B : Subgroup H) : Subgroup ↥(inducedAutOn L) :=
  (B.subgroupOf (Subgroup.normalizer (L : Set H))).map (toInducedAutOn L)

end Induced

section Hyp51

variable {G : Type} [Group G]

@[expose] def MovedByAll (B : Subgroup G) (c : G) (L : Subgroup (OddQuot c)) : Prop :=
  ∀ x ∈ modOdd c B, x ∉ modOdd c (Subgroup.zpowers c) → ∃ y ∈ L, x * y ≠ y * x

@[expose] def Hyp51At (B : Subgroup G) (c : G) : Prop :=
  (∀ L₁ L₂ : Subgroup (OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      MovedByAll B c L₁ → MovedByAll B c L₂ → L₁ = L₂) ∧
    ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      alphaOf (inducedImage L (modOdd c B)) = ⊥

@[expose] def Hyp51 (B : Subgroup G) : Prop :=
  IsElemAbelian 2 B ∧ Nat.card B = 8 ∧ ∀ c ∈ B, c ≠ 1 → Hyp51At B c

end Hyp51

@[expose] def Lemma52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G), Hyp51 B → RankThreeBalance B

section Frames

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure FuzzyFrameDataD (Ω : Set (Subgroup G)) (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G)
    (S : Set (Subgroup G)) (a : G) : Prop where
  mem : L₀ ∈ Ω
  cls : IsClassicalMember p f L₀ z₀
  z₀A : z₀ ∈ A
  tq : A ≤ trivialOnQuot L₀
  frame : FrameSideTwoD p f Ω A S
  aA : a ∈ A
  a1 : a ≠ 1
  aClassical : ∃ M ∈ Ω, IsClassicalMember p f M a
  cover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
    ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀)
  nine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
    InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x

variable {p f}

theorem FuzzyFrameDataD.toBalanced {Ω : Set (Subgroup G)} {L₀ : Subgroup G} {z₀ : G}
    {A : Subgroup G} {S : Set (Subgroup G)} {a : G} (h : FuzzyFrameDataD p f Ω L₀ z₀ A S a)
    (hbal : RankThreeBalance A) : FuzzyBalancedDataD p f Ω L₀ z₀ A S a :=
  ⟨h.mem, h.cls, h.z₀A, h.tq, hbal, h.frame, h.aA, h.a1, h.aClassical, h.cover, h.nine⟩

@[expose] def FrameExistsD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        FuzzyFrameDataD p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧ Hyp51 A

@[expose] def FrameExistsAllD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        FuzzyFrameDataD p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧ Hyp51 A

theorem fuzzyBalancedExistsD_of_frameExistsD (h52 : Lemma52) (h : FrameExistsD p f) :
    FuzzyBalancedExistsD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  exact ⟨L₀, z₀, A, S, a, hfr.toBalanced (h52 G A hA)⟩

theorem exactP1D_of_frameExistsAllD (h52 : Lemma52) (h : FrameExistsAllD p f) :
    ExactP1D p f := by
  refine exactP1D_of_fuzzyBalancedExistsAllD ?_
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD
  obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ := h G hnab hp2 hq hBelow K z hz h3 h4 hD
  exact ⟨L₀, z₀, A, S, a, hfr.toBalanced (h52 G A hA)⟩

end Frames

end CFSG.ClassicalInvolution.Asc77
