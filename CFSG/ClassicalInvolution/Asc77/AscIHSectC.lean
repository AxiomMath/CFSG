module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectB
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscE184Sub

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

section Bridge

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

def OmegaLie.toLieSystemData (D : OmegaLie p f Φ) (hgen : omegaGen Φ = ⊤) :
    LieSystemData p f X Φ where
  card := D.card
  tag := D.tag
  rank := D.rank
  exp := D.exp
  hom := D.hom
  isFundTag := D.isFundTag
  admissible := D.admissible
  exp_eq := D.exp_eq
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate.trans hgen
  fundamental := D.fundamental
  meets := D.meets

theorem LieSystemData.exists_of_hasLieType (hgen : omegaGen Φ = ⊤) {t : StatedLieTag} {n : ℕ}
    (h : HasLieType p f Φ t n) :
    ∃ D : LieSystemData p f X Φ, D.card = 1 ∧ ∃ i : Fin D.card, D.tag i = t ∧ D.rank i = n := by
  obtain ⟨D, hcard, i, ht, hn⟩ := h
  exact ⟨D.toLieSystemData hgen, hcard, i, ht, hn⟩

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {Y : Subgroup G}

theorem sectionLieType_of_hasLieType
    (hgen : omegaGen (oddQuotientFamily (restrictFamily Ω Y)) = ⊤) {t : StatedLieTag} {n : ℕ}
    (h : HasLieType p f (oddQuotientFamily (restrictFamily Ω Y)) t n) :
    SectionLieType p f Ω Y t n :=
  LieSystemData.exists_of_hasLieType hgen h

theorem sectionOrthType_of_hasOrthType
    (hgen : omegaGen (oddQuotientFamily (restrictFamily Ω Y)) = ⊤) {d : ℕ} {ε : Bool}
    (h : HasOrthType p f (oddQuotientFamily (restrictFamily Ω Y)) d ε) :
    SectionOrthType p f Ω Y d ε := by
  obtain ⟨t, n, hd, ht⟩ := h
  exact ⟨t, n, hd, sectionLieType_of_hasLieType hgen ht⟩

end Bridge

section Ambient

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem transSection_oddQuotient (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (Y : Subgroup G)
    (hgen : omegaGen (oddQuotientFamily (restrictFamily Ω Y)) = ⊤)
    (htrans : ∀ K ∈ oddQuotientFamily (restrictFamily Ω Y),
      ∀ L ∈ oddQuotientFamily (restrictFamily Ω Y),
        ∃ g : ↥Y ⧸ classicalInvolutionOddCore ↥Y, conjSub g K = L)
    (hA : ∀ L ∈ oddQuotientFamily (restrictFamily Ω Y),
      AEmpty (oddQuotientFamily (restrictFamily Ω Y)) L) :
    TransSection p f (oddQuotientFamily (restrictFamily Ω Y)) :=
  { hyp := oddQuotHyp p f hp hq ↥Y (restrictFamily Ω Y) (hΩ.restrict Y)
      (classicalInvolutionOddCore ↥Y) (CFSG.ComponentClassification.OddCore.odd_card ↥Y)
    oddCore := CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
    gen := hgen
    trans := htrans
    aEmpty := hA }

theorem sectionLie_of_thm6 {n : ℕ} (h6 : Thm6SectBelow p f n) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (Y : Subgroup G) (hlt : Nat.card (↥Y ⧸ classicalInvolutionOddCore ↥Y) < n)
    (hS : TransSection p f (oddQuotientFamily (restrictFamily Ω Y)))
    (hne : (oddQuotientFamily (restrictFamily Ω Y)).Nonempty)
    (htop : (⊤ : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y)) ∉
      oddQuotientFamily (restrictFamily Ω Y))
    (hDE : DEdgeless (oddQuotientFamily (restrictFamily Ω Y))) :
    SectionLieType p f Ω Y .PSL 3 ∨ SectionLieType p f Ω Y .PSU 3 ∨
      SectionLieType p f Ω Y .G2 0 ∨ SectionLieType p f Ω Y .trialityD4 0 := by
  rcases h6 hp hq _ hlt _ hS hne htop hDE with h | h | h | h
  · exact Or.inl (sectionLieType_of_hasLieType hS.gen h)
  · exact Or.inr (Or.inl (sectionLieType_of_hasLieType hS.gen h))
  · exact Or.inr (Or.inr (Or.inl (sectionLieType_of_hasLieType hS.gen h)))
  · exact Or.inr (Or.inr (Or.inr (sectionLieType_of_hasLieType hS.gen h)))

theorem sectionOrth_of_thm7 {n : ℕ} (h7 : Thm7SectBelow p f n) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (Y : Subgroup G) (hlt : Nat.card (↥Y ⧸ classicalInvolutionOddCore ↥Y) < n)
    (hS : TransSection p f (oddQuotientFamily (restrictFamily Ω Y)))
    {K : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y)}
    (hK : K ∈ oddQuotientFamily (restrictFamily Ω Y))
    (htw : ∃ K' ∈ twinSet (oddQuotientFamily (restrictFamily Ω Y)) K, K' ≠ K) :
    ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ SectionOrthType p f Ω Y d ε := by
  obtain ⟨d, ε, hd, h⟩ := h7 hp hq _ hlt _ hS K hK htw
  exact ⟨d, ε, hd, sectionOrthType_of_hasOrthType hS.gen h⟩

theorem sectionOrth_of_thm8 {n : ℕ} (h8 : Thm8SectBelow p f n) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (Y : Subgroup G) (hlt : Nat.card (↥Y ⧸ classicalInvolutionOddCore ↥Y) < n)
    (hS : TransSection p f (oddQuotientFamily (restrictFamily Ω Y)))
    (hne : (oddQuotientFamily (restrictFamily Ω Y)).Nonempty)
    (hNE : ¬ DEdgeless (oddQuotientFamily (restrictFamily Ω Y)))
    (hNC : ¬ DConnected (oddQuotientFamily (restrictFamily Ω Y))) :
    ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ SectionOrthType p f Ω Y d ε := by
  obtain ⟨d, ε, hd, hd8, h⟩ := h8 hp hq _ hlt _ hS hne hNE hNC
  exact ⟨d, ε, hd, hd8, sectionOrthType_of_hasOrthType hS.gen h⟩

end Ambient

section Simple

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem TransSection.of_simple (hΩ : HypOmegaMod p f Ω) (hne : Ω.Nonempty)
    (htrans : ∀ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, conjSub g K = L) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    TransSection p f Ω := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact { hyp := hΩ
          oddCore := ih8_oddCore_eq_bot_of_simple hz.orderOf_eq_two
          gen := ih8_omegaGen_eq_top hΩ.conjInvariant hK (ih8_member_ne_bot hz)
          trans := htrans
          aEmpty := hA }

omit [Finite G] in
theorem top_notMem_of_simple (hΩ : HypOmegaMod p f Ω) : (⊤ : Subgroup G) ∉ Ω := by
  intro h
  obtain ⟨z, hz⟩ := hΩ.classical _ h
  exact ih8_not_top_member hz

end Simple

theorem thm6TypedBelow_of_sect {n : ℕ} (h : Thm6SectBelow p f n) : Thm6TypedBelow p f n := by
  intro hp2 hq G _ _ _ hlt Ω hΩ hA hne htrans hDE
  exact h hp2 hq G hlt Ω (TransSection.of_simple hΩ hne htrans hA) hne (top_notMem_of_simple hΩ)
    hDE

theorem thm7TypedBelow_of_sect {n : ℕ} (h : Thm7SectBelow p f n) : Thm7TypedBelow p f n := by
  intro hp2 hq G _ _ _ hlt Ω hΩ hA htrans K hK htw
  exact h hp2 hq G hlt Ω (TransSection.of_simple hΩ ⟨K, hK⟩ htrans hA) K hK htw

theorem thm8TypedBelow_of_sect {n : ℕ} (h : Thm8SectBelow p f n) : Thm8TypedBelow p f n := by
  intro hp2 hq G _ _ _ hlt Ω hΩ hA hne htrans hNE hNC
  exact h hp2 hq G hlt Ω (TransSection.of_simple hΩ hne htrans hA) hne hNE hNC

end CFSG.ClassicalInvolution.Asc77
