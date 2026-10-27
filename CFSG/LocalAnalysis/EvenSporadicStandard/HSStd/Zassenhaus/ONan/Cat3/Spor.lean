module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.RuFi23
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM11
public import CFSG.RankThree.PartTwo.KFacts.KP4

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private theorem card_centralizer_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({e x} : Set H)) := by
  have h : (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have := congrArg e hy
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    · intro hy
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  rw [← h, Subgroup.card_map_of_injective e.injective]

private theorem spor_ord_cases : ∀ s : TauCeti.SporadicName,
    9 ∣ CFSG.AGLEmbedding.sporOrd s → ¬ 27 ∣ CFSG.AGLEmbedding.sporOrd s →
      s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS := by
  decide +kernel


private theorem carrier_M11_card_centralizer {x : Carrier .M11} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (Carrier .M11))) = 18 :=
  CFSG.RankThree.PartTwo.Sec4.Item434SporM11.card_centralizer_eq hx3 hx1

theorem sporadic_cases {L : Type} [Group L] [Finite L] (h : SporadicRep L)
    (h3 : (Nat.card L).factorization 3 = 2) (hC : CentHyp L) :
    IsSporadic L .HS ∨ IsSporadic L .M23 := by
  obtain ⟨s, ⟨e⟩⟩ := h
  have hcard : Nat.card L = CFSG.AGLEmbedding.sporOrd s :=
    (Nat.card_congr e.toEquiv).trans
      ((CFSG.ComponentClassification.CatFC.card_carrier_eq_sporOrder_all s).trans
        (CFSG.ComponentClassification.CatFC.sporOrder_eq_sporOrd s))
  have hpos : 0 < Nat.card L := Nat.card_pos
  have h9 : 9 ∣ CFSG.AGLEmbedding.sporOrd s := by
    rw [← hcard]
    have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 2) (n := Nat.card L)
      Nat.prime_three hpos.ne').mpr (by omega)
    simpa using this
  have hn27 : ¬ 27 ∣ CFSG.AGLEmbedding.sporOrd s := by
    rw [← hcard]
    intro hd
    have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 3) (n := Nat.card L)
      Nat.prime_three hpos.ne').mp (by simpa using hd)
    omega
  have h3dvd : 3 ∣ Nat.card L := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 1) (n := Nat.card L)
      Nat.prime_three hpos.ne').mpr (by omega)
    simpa using this
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases spor_ord_cases s h9 hn27 with rfl | rfl | rfl | rfl
  ·
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 h3dvd
    exfalso
    have hx3' : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx3 : (e x) ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
    have hx1 : e x ≠ 1 := by
      intro h1
      have hx1' : x = 1 := e.injective (by rw [h1, map_one])
      rw [hx1', orderOf_one] at hx
      norm_num at hx
    have hc := hC.card_centralizer hx
    rw [card_centralizer_equiv e x, carrier_M11_card_centralizer hx3 hx1] at hc
    rcases hc with hc | hc <;> omega
  ·
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 h3dvd
    exfalso
    have hfacts :=
      CFSG.RankThree.PartTwo.KFacts.KP4.m22_centralizer_facts_of_orderOf ⟨e⟩ ha
    have h36 : Nat.card (Subgroup.centralizer ({a} : Set L)) = 36 := hfacts.1
    have hc := hC.card_centralizer ha
    rw [h36] at hc
    rcases hc with hc | hc <;> omega
  · exact Or.inr ⟨e⟩
  · exact Or.inl ⟨e⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
