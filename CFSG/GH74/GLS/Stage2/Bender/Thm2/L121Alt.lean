module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.GH74.GLS.Basic

public section

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L121

section Aut

theorem exists_conj_of_odd {G' : Type*} [Group G'] {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (e : G' ≃* alternatingGroup (Fin n)) (σ : MulAut G') (hσ : Odd (orderOf σ)) :
    ∃ a : G', σ = MulAut.conj a := by
  have h2 := CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six hn e
  let q : MulAut G' →* CFSG.ComponentClassification.OuterAutomorphisms.Outer G' :=
    QuotientGroup.mk' _
  have h3 : orderOf (q σ) ∣ 2 := (orderOf_dvd_natCard (q σ)).trans h2
  have h4 : orderOf (q σ) ∣ orderOf σ := orderOf_map_dvd q σ
  have h5 : orderOf (q σ) = 1 := by
    have hcop : Nat.Coprime 2 (orderOf σ) := (Nat.coprime_two_left).mpr hσ
    exact Nat.eq_one_of_dvd_coprimes hcop h3 h4
  have h6 : q σ = 1 := orderOf_eq_one_iff.mp h5
  have h7 : σ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G' :=
    (QuotientGroup.eq_one_iff σ).mp h6
  obtain ⟨a, ha⟩ := h7
  exact ⟨a, ha.symm⟩

end Aut

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L121
