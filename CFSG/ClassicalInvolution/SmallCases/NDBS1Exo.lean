module

public import CFSG.ClassicalInvolution.SmallCases.NDBS1Cover
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

@[expose] def ExoticTag (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  t = .G2 ∨ t = .trialityD4 ∨ (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)

section Defs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def ExoticNoTwin {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop :=
  ¬ HasTwin p f K z ∧ (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) ∧
    ∃ (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) (i : Fin D.card),
      ExoticTag (D.tag i) (D.rank i)

abbrev ExoticNoTwinPred : Asc77.ShapePred :=
  fun _ _ _ K z => ExoticNoTwin p f K z

@[expose] def BootNoG2D4Twin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Asc77.BSC.BootSetting p f K z → HasTwin p f K z →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
        ¬ (D.tag i = .G2 ∨ D.tag i = .trialityD4)

@[expose] def BootShapeCoverX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (𝒞 K) → BootData p f (𝒞 K) →
        ¬ IndepTriple p f (𝒞 K) →
          Asc77.ChainShape p f (𝒞 K) z ∨ TwinShapeWeak p f K z ∨ PSpShape p f (𝒞 K) z ∨
            ExoticNoTwin p f K z

structure BootShapeResidualsX : Prop where
  noAllA1 : Asc77.BSC.BootNoAllA1 p f
  noG2D4Twin : BootNoG2D4Twin p f
  noM3Twin : Asc77.BSC.BootNoM3Twin p f
  noManyTwins : Asc77.BSC.BootNoManyTwins p f

end Defs

variable {p f : ℕ} [Fact p.Prime]

theorem bootShapeCoverX_of_residuals (res : BootShapeResidualsX p f) : BootShapeCoverX p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  have hS : Asc77.BSC.BootSetting p f K z := ⟨hnab, hp2, hq, hz, hBelow, hconn, hdata, hT⟩
  have hno := Asc77.BSC.noFuzzyFrame hS
  obtain ⟨D⟩ := Cover.nonempty_lieSystem hnab hp2 hq hz hBelow
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
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
  rcases Asc77.BSC.tag_cases_of_noFrame C hno b hb with hGD | hM3 | hX
  ·
    by_cases hTw : HasTwin p f K z
    · exact absurd hGD (res.noG2D4Twin G K z hS hTw C.D b)
    · refine Or.inr (Or.inr (Or.inr ⟨hTw, hno, D, b, ?_⟩))
      rcases hGD with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
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
      · have hTw : ¬ HasTwin p f K z := S1.noTwin_of_card_two C hc2 hb
        rcases hX with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h | h | h
        · exact Or.inr (Or.inr (Or.inl
            (pspShape_of_card_two hnab hp2 hq hz hBelow hno D hc2 b h.1 h.2)))
        · exact absurd ⟨Or.inl h1, h2⟩ hch
        · exact absurd ⟨Or.inr h1, h2⟩ hch
        · exact Or.inr (Or.inr (Or.inr ⟨hTw, hno, D, b, Or.inr (Or.inr (Or.inl h))⟩))
        · exact absurd h (noSpinPlusSingle_of_card_two hnab hp2 hq hz hBelow hno D hc2 b)
        · exact Or.inr (Or.inr (Or.inr ⟨hTw, hno, D, b, Or.inr (Or.inr (Or.inr h))⟩))
    ·
      right
      left
      obtain ⟨e, hej, heb⟩ := Fin.exists_ne_and_ne_of_two_lt j₀ b (by omega)
      obtain ⟨he, hetwin⟩ := Asc77.BSC.nbar_eq_of_A1 C hno hb heb
      obtain ⟨m⟩ := Asc77.BSC.exists_compMem C e
      have hm := hetwin m
      obtain ⟨hcl, -⟩ := Asc77.BSC.classical_of_nbar_eq C he m hm
      have hTK : m.N ≠ C.K := Asc77.BSC.twin_ne_K C hj₀ hK₀ hej he m hm
      exact ⟨⟨C.D, hc3', j₀, b, e, hjb, heb.symm, hej.symm, hj₀.1, hj₀.2, he.1, he.2, hX⟩,
        m.N, m.hN.1, hTK, hcl⟩

end CFSG.ClassicalInvolution.NDB
