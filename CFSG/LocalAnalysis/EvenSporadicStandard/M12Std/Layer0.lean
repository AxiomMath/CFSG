module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M12
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Center
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Entry
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.M12Cover
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

theorem nonempty_zpowers_equiv_z2 {X : Type*} [Group X] {t : X} (ht : orderOf t = 2) :
    Nonempty (zpowers t ≃* Multiplicative (ZMod 2)) := by
  have hcard : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨(zmodCyclicMulEquiv (inferInstance : IsCyclic (zpowers t))).symm.trans
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv)⟩

section Certified


theorem center_eq_bot_of_isSporadic_m12 {Y : Type} [Group Y] (h : IsSporadic Y .M12) :
    center Y = ⊥ := by
  obtain ⟨e⟩ := h
  exact HypOne.center_eq_bot_of_mulEquiv e.symm m12_center

theorem index_dvd_two_of_isSporadic_m12 {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M12) :
    (innAut Y).index ∣ 2 := by
  have hY : center Y = ⊥ := center_eq_bot_of_isSporadic_m12 h
  obtain ⟨e⟩ := h
  have hinj := HypOne.conj_injective_of_center_eq_bot hY
  have h1 : Nat.card (MulAut Y) = Nat.card (MulAut NativeSporadic.M12) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have h2 : Nat.card Y = Nat.card NativeSporadic.M12 := Nat.card_congr e.toEquiv
  exact HypOne.index_dvd_two_of_card_le hinj (by rw [h1, h2]; exact m12_mulAut_card)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_eq_two_m12 (h : StdHyp G L)
    (hL : IsSporadic L .M12) (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_m12 hL
  have hLq : IsSporadic (L ⧸ center L) .M12 := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact h.card_sylow_eq_two_of_fours
    (HypOne.M12.fullRowData_of_isSporadic hLq).rowData.hypothesisOne
    (HypOne.M12.foursGroupCondition_of_isSporadic hL) S

theorem m12_dichotomy (h : StdHyp G L) (hL : IsSporadic L .M12) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    (centralizer ({t} : Set G) = L ⊔ zpowers t ∧ Disjoint L (zpowers t) ∧
      zpowers t ≤ centralizer (L : Set G)) ∨
    (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_m12 hL
  have hS := h.card_sylow_eq_two_m12 hL
  have hLq : IsSporadic (L ⧸ center L) .M12 := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  by_cases hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)
  · exact Or.inl (h.centralizer_eq_prod_of_center_eq_bot hS ht ht2 hinn hZ)
  · right
    have hN : ¬ normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) := fun hN =>
      hinn ((h.centralizer_le_normalizer ht ht2).trans hN)
    have hdvd := (Fin76b.relIndex_normalizer_dvd (G := G) h.standard.1.1).trans
      (index_dvd_two_of_isSporadic_m12 hLq)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact absurd (Subgroup.relIndex_eq_one.1 h1) hN
    · exact h2

theorem m12_inner_nonempty_equiv (h : StdHyp G L) (hL : IsSporadic L .M12) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    Nonempty (centralizer ({t} : Set G) ≃* Multiplicative (ZMod 2) × Carrier .M12) := by
  obtain ⟨e1⟩ := h.nonempty_mulEquiv_prod_of_center_eq_bot (h.card_sylow_eq_two_m12 hL) ht ht2
    hinn (center_eq_bot_of_isSporadic_m12 hL)
  obtain ⟨e2⟩ := hL
  obtain ⟨e3⟩ := nonempty_zpowers_equiv_z2 ht2
  exact ⟨e1.trans ((MulEquiv.prodCongr e2 e3).trans MulEquiv.prodComm)⟩

end Certified

end CFSG.EvenSporadicStandard.M12Std
