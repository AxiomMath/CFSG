module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CayleySpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Sl25Strict
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem conjEqOK_spec (hg : gensOK = true) {c : List ℕ} {tx ty : Table}
    {x y : Equiv.Perm (Fin 1408)} (hx : Rep 1408 tx x) (hy : Rep 1408 ty y)
    (h : conjEqOK c tx ty = true) : elemW c * x * (elemW c)⁻¹ = y := by
  simp only [conjEqOK, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hinv⟩, heq⟩ := h
  exact (tblEq_iff_eq (rep_conjTab hg hc hinv hx) hy).1 heq

theorem shapeD5OK_spec (h : shapeD5OK = true) :
    ∃ D : Subgroup (Equiv.Perm (Fin 1408)),
      D ≤ P1408 ⊓ centralizer ({elemW fix5C.rep} : Set (Equiv.Perm (Fin 1408))) ∧
        Nonempty (↥D ≃* SL25) := by
  simp only [shapeD5OK, Bool.and_eq_true] at h
  obtain ⟨⟨hwr, hcomm⟩, hcay⟩ := h
  obtain ⟨hg, hw⟩ := enumW_gens_words (enumW_of_cayleyOK hcay)
  have hrr : Rep 1408 (tabW fix5C.rep) (elemW fix5C.rep) := rep_elemW_of_gensOK hg hwr
  obtain ⟨e⟩ := nonempty_mulEquiv_of_cayleyOK hcay card_SL25S
  exact ⟨closure (elemW '' {w | w ∈ d5Words}), closure_words_le_inf_centralizer hg hw hrr hcomm,
    ⟨e.trans SL25S.mulEquiv⟩⟩

theorem shapeUOK_spec (h : shapeUOK = true) :
    elemW u0Word * elemW u0Word = 1 ∧ elemW u0Word ≠ 1 ∧ elemW u0Word ≠ elemA ∧
      elemW u0Word * elemW fix5B.rep = elemW fix5B.rep * elemW u0Word ∧
        elemW c0Word * elemZ₁ * (elemW c0Word)⁻¹ = elemW u0Word := by
  simp only [shapeUOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hg, hwr⟩, hwu⟩, hord⟩, hne⟩, hcomm⟩, hconj⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hru : Rep 1408 (tabW u0Word) (elemW u0Word) := rep_elemW_of_gensOK hg hwu
  have hrr : Rep 1408 (tabW fix5B.rep) (elemW fix5B.rep) := rep_elemW_of_gensOK hg hwr
  have hrA : Rep 1408 (tabW wordA) elemA := rep_elemW_of_gensOK hg (by decide)
  have hrz : Rep 1408 (tabW wordZ₁) elemZ₁ := rep_elemW_of_gensOK hg (by decide)
  have hu2 : orderOf (elemW u0Word) = 2 := orderOf_eq_of_primeOrderOK hru hord
  refine ⟨mul_self_eq_one_of_orderOf_eq_two hu2, ne_one_of_orderOf_eq_two hu2, ?_,
    (commTT_iff hru hrr).1 hcomm, conjEqOK_spec hg hrz hru hconj⟩
  intro hh
  have := (tblEq_iff_eq hru hrA).2 hh
  rw [this] at hne
  exact absurd hne (by decide)

theorem shapeA8OK_spec (h : shapeA8OK = true) :
    orderOf (elemW rpWord) = 5 ∧ elemW rpWord * elemB = elemB * elemW rpWord ∧
      ∀ k : ℕ, 0 < k → k < 5 → ∃ c ∈ P1408, c * elemW fix5C.rep * c⁻¹ = elemW rpWord ^ k := by
  simp only [shapeA8OK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, hwr⟩, hwp⟩, hord⟩, hcomm⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrp : Rep 1408 (tabW rpWord) (elemW rpWord) := rep_elemW_of_gensOK hg hwp
  have hrr : Rep 1408 (tabW fix5C.rep) (elemW fix5C.rep) := rep_elemW_of_gensOK hg hwr
  have hrB : Rep 1408 (tabW wordB) elemB := rep_elemW_of_gensOK hg (by decide)
  refine ⟨orderOf_eq_of_primeOrderOK hrp hord, (commTT_iff hrp hrB).1 hcomm, ?_⟩
  intro k hk0 hk5
  have key : ∀ (k : ℕ) (w : List ℕ), rpConjOK k w = true →
      elemW w * elemW fix5C.rep * (elemW w)⁻¹ = elemW rpWord ^ k := fun k w hk =>
    conjEqOK_spec hg hrr (Rep.powT (by norm_num) hrp k) hk
  have hmem : ∀ w : List ℕ, elemW w ∈ P1408 := elemW_mem
  interval_cases k
  · exact ⟨_, hmem _, key 1 _ h1⟩
  · exact ⟨_, hmem _, key 2 _ h2⟩
  · exact ⟨_, hmem _, key 3 _ h3⟩
  · exact ⟨_, hmem _, key 4 _ h4⟩

end CFSG.EvenSporadicStandard.HNRecog
