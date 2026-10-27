module

public import CFSG.ClassicalInvolution.Asc77.AscBSCResid
public import CFSG.ClassicalInvolution.Asc77.AscBSCShape
import CFSG.ClassicalInvolution.Asc77.WP3S28BIndep
import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll
import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem noFuzzyFrame {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (hS : BootSetting p f K z) :
    ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (CoreAssembly.conjClass K) A := by
  intro A hA
  have hΩ := NDB.Cover.hypOmegaMod hS.nonabelian hS.odd hS.five hS.member hS.below
  exact hS.noTriple (S28B.indepTriple_of_fuzzy (Balance.Bootstrap.layerGenerationHybrid p)
    (ModelFacts.commutingFundamentalFactsFive_all hS.odd) hS.nonabelian hS.odd hS.five hS.member
    hΩ hS.below hS.dconn ⟨A, hA⟩)

@[expose] def BootShapeCoverWeak (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
        ChainShape p f (CoreAssembly.conjClass K) z ∨ NDB.TwinShapeWeak p f K z

theorem bootShapeCoverWeak_of_residuals (res : BootShapeResidualsW p f) :
    BootShapeCoverWeak p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  have hS : BootSetting p f K z := ⟨hnab, hp2, hq, hz, hBelow, hconn, hdata, hT⟩
  have hno := noFuzzyFrame hS
  obtain ⟨D⟩ := NDB.Cover.nonempty_lieSystem hnab hp2 hq hz hBelow
  let C := NDB.Cover.toXCtx hnab hp2 hq hz hBelow D
  obtain ⟨j₀, hj₀, hK₀⟩ := C.exists_A1_of_K
  have hnotall := res.noAllA1 G K z hS C.D
  obtain ⟨b, hb⟩ : ∃ b : Fin C.D.card, ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := by
    by_contra h
    exact hnotall fun i => by_contra fun hi => h ⟨i, hi⟩
  have hjb : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  have hcard2 : 2 ≤ C.D.card := by
    have h1 := j₀.2
    have h2 := b.2
    have h3 : j₀.val ≠ b.val := fun h => hjb (Fin.ext h)
    omega
  rcases tag_cases_of_noFrame C hno b hb with hGD | hM3 | hX
  · exact absurd hGD (res.noG2D4 G K z hS C.D b)
  ·
    have hc : C.D.card ≤ 2 := res.noM3Twin G K z hS C.D b hM3.1 hM3.2
    left
    exact ⟨C.D, by omega, j₀, b, hjb, hj₀.1, hj₀.2, hM3.1, Or.inl hM3.2⟩
  · have hc3 : C.D.card ≤ 3 := res.noManyTwins G K z hS C.D b hX
    have hc23 : C.D.card = 2 ∨ C.D.card = 3 := by omega
    rcases hc23 with hc2 | hc3'
    ·
      by_cases hch : (C.D.tag b = .PSL ∨ C.D.tag b = .PSU) ∧ C.D.rank b = 4
      · left
        exact ⟨C.D, hc2, j₀, b, hjb, hj₀.1, hj₀.2, hch.1, Or.inr hch.2⟩
      · exfalso
        refine res.noSmallSingle G K z hS C.D hc2 b ?_
        rcases hX with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h | h | h
        · exact Or.inl h
        · exact absurd ⟨Or.inl h1, h2⟩ hch
        · exact absurd ⟨Or.inr h1, h2⟩ hch
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    ·
      right
      obtain ⟨e, hej, heb⟩ := Fin.exists_ne_and_ne_of_two_lt j₀ b (by omega)
      obtain ⟨he, hetwin⟩ := nbar_eq_of_A1 C hno hb heb
      obtain ⟨m⟩ := exists_compMem C e
      have hm := hetwin m
      obtain ⟨hcl, -⟩ := classical_of_nbar_eq C he m hm
      have hTK : m.N ≠ C.K := twin_ne_K C hj₀ hK₀ hej he m hm
      exact ⟨⟨C.D, hc3', j₀, b, e, hjb, heb.symm, hej.symm, hj₀.1, hj₀.2, he.1, he.2, hX⟩,
        m.N, m.hN.1, hTK, hcl⟩

theorem bootShapeCover_of_residuals (res : BootShapeResiduals p f) : BootShapeCover p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  have hS : BootSetting p f K z := ⟨hnab, hp2, hq, hz, hBelow, hconn, hdata, hT⟩
  rcases bootShapeCoverWeak_of_residuals res.toBootShapeResidualsW G hnab hp2 hq K z hz hBelow
      hconn hdata hT with hch | ⟨hlie, T, hTΩ, hTK, hTz⟩
  · exact Or.inl hch
  · exact Or.inr ⟨hlie, T, hTΩ, res.twinsCommute G K z hS T hTΩ hTK hTz, hTz⟩

end CFSG.ClassicalInvolution.Asc77.BSC
