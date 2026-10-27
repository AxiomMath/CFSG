module

public import CFSG.Quasithin.H13.A7Nat1233
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NatMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

section Main

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem A7_natural_or_four_F4 (h1222 : Stmt12_2_2_F4) (hI16 : AsI16AltSevenCover) {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V)
    (hA7 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7))) :
    (∃ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) ∧
      ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) ∨
    (Nat.card V = 2 ^ 4 ∧ ∃ φ : ↥L →* ↥(alternatingGroup (Fin 7)), Function.Surjective φ ∧
      φ.ker = (centralizer (V : Set G)).subgroupOf L) := by
  classical

  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hab, hmod⟩ := hall V hyp.irrPlus

  have hQ := card_eq_of_quot_center_alternating_seven hA7
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hyp.quasisimple
  have hzpos : 0 < Nat.card (center (↥L ⧸ CFSG.pCore 2 ↥L)) := Nat.card_pos
  obtain ⟨k, hk⟩ := hodd
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφs, -⟩, hnat⟩ | hfour | ⟨hlie, -⟩ | ⟨-, -, ⟨e⟩, -⟩
  ·
    exfalso
    have hc := Nat.card_congr e.toEquiv
    rcases hn with rfl | rfl | rfl
    · rw [nat_card_SL_three_zmod_two, hQ] at hc
      omega
    · rw [nat_card_SL_four_zmod_two, hQ] at hc
      omega
    · rw [nat_card_SL_five_zmod_two, hQ] at hc
      omega
  · exfalso
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_SL_three_zmod_two, hQ] at hc
    omega
  · exfalso
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_SL_five_zmod_two, hQ] at hc
    omega
  ·
    have hn7 := eq_seven_of_surjective_alternating hyp.quasisimple hQ ⟨k, hk⟩ hn5 hn8 hφs
    subst hn7
    have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
    have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
      obtain ⟨-, hEA, -⟩ := hred
      intro v hv
      have hv' : (⟨v, le_sup_right (b := T) (a := L) (hVT hv)⟩ : ↥(L ⊔ T)) ∈
          V.subgroupOf (L ⊔ T) := hv
      have h1 := (BlueprintB2.isElementaryAbelian_iff.1 hEA).2 _ hv'
      exact congrArg Subtype.val h1
    have hCV := hI16 G L V hsq hLV hyp.irrPlus.2.2.2.1 hnat
    exact Or.inl (exists_coord_of_alternatingNatural hLV hnat hCV)
  · exact Or.inr hfour
  ·
    exfalso
    obtain ⟨e⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hlie
    have hc := Nat.card_congr e.toEquiv
    have h5 : 5 ∣ Nat.card (CFSG.Open.PSU3 3 1) := by
      rw [← hc, hQ]
      exact Dvd.dvd.mul_right (by norm_num) _
    have h6 := h5.trans nat_card_psu331_dvd
    norm_num at h6
  ·
    exfalso
    obtain ⟨e₇⟩ := hA7
    have hc := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e₇.toEquiv)
    rw [nat_card_alternating_seven, nat_card_alternating_fin 6 (by norm_num)] at hc
    norm_num [Nat.factorial] at hc

end Main

@[expose] def A7FourExcluded_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ¬ (Nat.card V = 2 ^ 4 ∧ ∃ φ : ↥L →* ↥(alternatingGroup (Fin 7)), Function.Surjective φ ∧
      φ.ker = (centralizer (V : Set G)).subgroupOf L)

theorem stmt12_3_3_of_four_F4 (h1222 : Stmt12_2_2_F4) (hI16 : AsI16AltSevenCover)
    (hfour : A7FourExcluded_F4) : Stmt12_3_3_F4 := by
  intro G _ _ T L V hyp hA7
  rcases A7_natural_or_four_F4 h1222 hI16 hyp hA7 with h | h
  · exact h
  · exact absurd h (hfour G T L V hyp hA7)

end CFSG.Quasithin.H13.A7
