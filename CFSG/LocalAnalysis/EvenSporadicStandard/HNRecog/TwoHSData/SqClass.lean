module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux
public import Certificates.Certificate26774

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

theorem card_centralizer_eq_of_isConj {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card ↥(centralizer ({y} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (Nat.card_congr (TwoHSData.centralizerMulEquiv (MulAut.conj c) x).toEquiv).symm

section Cert

theorem sqFacts_P (hP : Nat.card ↥P1408 = 177408000) : SqFacts :=
  Certificates.certificate26774 hP

theorem exists_sq_eq_P (hP : Nat.card ↥P1408 = 177408000) : ∃ g : ↥P1408, g ^ 2 = pA :=
  (sqFacts_P hP).exists_sq

theorem isConj_of_sq_eq_P (hP : Nat.card ↥P1408 = 177408000) {g g' : ↥P1408} (hg : g ^ 2 = pA)
    (hg' : g' ^ 2 = pA) : IsConj g g' :=
  (sqFacts_P hP).isConj_sq hg hg'

theorem card_centralizer_sq (hP : Nat.card ↥P1408 = 177408000) {g : ↥P1408} (hg : g ^ 2 = pA) :
    Nat.card ↥(centralizer ({g} : Set ↥P1408)) = 5760 :=
  (sqFacts_P hP).card_cent hg

theorem not_isSectionOf_A8_P (hP : Nat.card ↥P1408 = 177408000) {g : ↥P1408} (hg : g ^ 2 = pA) :
    ¬ CFSG.SignalizerFunctorTheorem.IsSectionOf (alternatingGroup (Fin 8))
      ↥(centralizer ({g} : Set ↥P1408)) := by
  rintro ⟨K, f, hf⟩
  have h1 : Nat.card ↥(alternatingGroup (Fin 8)) ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective f hf
  have h2 : Nat.card ↥K ≤ Nat.card ↥(centralizer ({g} : Set ↥P1408)) :=
    Nat.card_le_card_of_injective _ K.subtype_injective
  have h3 : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h4 := card_centralizer_sq hP hg
  omega

end Cert

end CFSG.EvenSporadicStandard.HNRecog
