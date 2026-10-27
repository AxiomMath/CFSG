module

public import CFSG.RankThree.GroupTheory.SteinbergBYSymplecticCritical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55.I336

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P]

theorem eq_zpowers_of_le {z : P} (hz : orderOf z = 2) {A : Subgroup P} (hA : A ≤ zpowers z)
    (hA1 : A ≠ ⊥) : A = zpowers z := by
  have hcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have h1 : Nat.card A ∣ 2 := hcard ▸ Subgroup.card_dvd_of_le hA
  have h2 : Nat.card A ≠ 1 := fun h => hA1 (Subgroup.card_eq_one.mp h)
  have h3 : Nat.card A = 2 := ((Nat.dvd_prime Nat.prime_two).mp h1).resolve_left h2
  exact Subgroup.eq_of_le_of_card_ge hA (by rw [hcard, h3])

theorem class_two_of_char_abelian_le [Nontrivial P] (hP : IsPGroup 2 P) {z : P}
    (hz : orderOf z = 2)
    (h : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → A ≤ zpowers z) :
    z ∈ center P ∧ ∀ x y : P, ⁅x, y⁆ ∈ zpowers z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨C, hC⟩, hCne⟩ := thompson_critical_subgroup hP
  have hCne' : C ≠ ⊥ := hCne C hC inferInstance
  have hzc : z ∈ center P := by
    have hnt : Nontrivial (center P) := hP.center_nontrivial
    have hne : center P ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hnt
    have := eq_zpowers_of_le hz (h (center P) inferInstance inferInstance) hne
    rw [this]
    exact mem_zpowers z
  obtain ⟨hCchar, hΦ, hPC, hcen⟩ := hC
  have hCchar' : C.Characteristic := hCchar
  have hCcentchar : (centralizer (C : Set P)).Characteristic := characteristic_centralizer C
  have hZchar : (C ⊓ centralizer (C : Set P)).Characteristic := characteristic_inf C _
  have hZab : IsMulCommutative ↥(C ⊓ centralizer (C : Set P)) :=
    ⟨⟨fun a b => Subtype.ext (by
      have := mem_centralizer_iff.mp a.2.2 b b.2.1
      simpa using this.symm)⟩⟩
  have hZne : C ⊓ centralizer (C : Set P) ≠ ⊥ := by
    rw [← map_center_subtype C]
    have : Nontrivial ↥C := (Subgroup.nontrivial_iff_ne_bot C).mpr hCne'
    have hnt : Nontrivial (center ↥C) := (hP.to_subgroup C).center_nontrivial
    intro hbot
    have h1 : center ↥C ≤ ⊥ := by
      intro x hx
      have : (x : P) ∈ (center ↥C).map C.subtype := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt (le_bot_iff.mp h1)
  have hZ : C ⊓ centralizer (C : Set P) = zpowers z :=
    eq_zpowers_of_le hz (h _ hZchar hZab) hZne
  have hcen' : (center ↥C).map C.subtype = zpowers z := by rw [map_center_subtype, hZ]
  have hzC : z ∈ C := by
    have : z ∈ C ⊓ centralizer (C : Set P) := by rw [hZ]; exact mem_zpowers z
    exact this.1
  have hZ' : ⁅(⊤ : Subgroup P), C⁆ ≤ zpowers z := hZ ▸ hPC
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ zpowers z := fun x _ y hy =>
    hZ' (commutator_mem_commutator (mem_top x) hy)
  have hΦ' : frattini ↥C ≤ center ↥C :=
    CFSG.RankThree.GroupTheory.SteinbergBY.frattini_le_center_of_thompsonCritical
      ⟨hCchar, hΦ, hPC, hcen⟩
  have hsq : ∀ x ∈ C, x ^ 2 ∈ zpowers z := by
    intro x hx
    have h1 := (CFSG.LocalAnalysis.GorensteinLyons.sq_mem_center_and_comm_mem_center
      (hP.to_subgroup C) hΦ').1 ⟨x, hx⟩
    rw [← hcen']
    exact ⟨_, h1, rfl⟩
  have hPC' : ∀ g : P, g ∈ C := by
    intro g
    obtain ⟨t, htC, ht⟩ := CFSG.RankThree.GroupTheory.SteinbergBY.exists_inner_of_conj_mem_zpowers
      hzC hz hzc hcomm hsq hcen' (g := g) (fun e he => by
        have : e⁻¹ * (g * e * g⁻¹) = (⁅g, e⁻¹⁆)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [this]
        exact (zpowers z).inv_mem (hZ' (commutator_mem_commutator (mem_top g) (inv_mem he))))
    have hcg : t⁻¹ * g ∈ centralizer (C : Set P) := by
      rw [mem_centralizer_iff]
      intro e he
      have h1 := ht e he
      calc e * (t⁻¹ * g) = t⁻¹ * (t * e * t⁻¹) * g := by group
        _ = t⁻¹ * (g * e * g⁻¹) * g := by rw [h1]
        _ = t⁻¹ * g * e := by group
    have hmem : t⁻¹ * g ∈ C := by
      have : t⁻¹ * g ∈ C ⊓ centralizer (C : Set P) := hcen ▸ hcg
      exact this.1
    have := mul_mem htC hmem
    rwa [mul_inv_cancel_left] at this
  exact ⟨hzc, fun x y => hZ' (commutator_mem_commutator (mem_top x) (hPC' y))⟩

end CFSG.LocalAnalysis.GLTheoremA.P55.I336
