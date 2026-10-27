module

public import CFSG.LargeExtraspecial.A2ModBasic
public import CFSG.LargeExtraspecial.OrthoF2Timmesfeld12
public import CFSG.LargeExtraspecial.OrthoF2Radical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul)

namespace A2Action

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem mem_pointRadical_of_mem_commSpace (hA : A2Action D Q ρ) {P : V} (hP : P ≠ 0) {d : X}
    (hd : d ∈ D) (hPd : P ∈ commSpace (ρ d)) : ρ d ∈ pointRadical Q P := by
  obtain ⟨x, hli, hsp⟩ := exists_pair_of_mem_of_finrank_eq_two (hA.isTypeA hd).2.2.2.1 hPd hP
  obtain ⟨hqP, -, hPx, hE⟩ := eq_eichler_of_isTypeA hA.nondegenerate (hA.isTypeA hd) hli hsp.symm
  rw [hE]
  exact eichler_mem_pointRadical hqP hPx

theorem closure_le_comap_pointRadical (hA : A2Action D Q ρ) {P : V} (hP : P ≠ 0)
    (hPD : ∀ d ∈ D, P ∈ commSpace (ρ d)) :
    Subgroup.closure D ≤ (pointRadical Q P).comap ρ := by
  rw [Subgroup.closure_le]
  intro d hd
  exact hA.mem_pointRadical_of_mem_commSpace hP hd (hPD d hd)

theorem exists_eichler_of_mem_closure (hA : A2Action D Q ρ) {P : V} (hP : P ≠ 0)
    (hPD : ∀ d ∈ D, P ∈ commSpace (ρ d)) (hD : D.Nonempty) {g : X}
    (hg : g ∈ Subgroup.closure D) : ∃ u, polar Q P u = 0 ∧ ρ g = eichler Q P u := by
  obtain ⟨d₀, hd₀⟩ := hD
  have hqP : Q P = 0 := (hA.isTypeA hd₀).2.2.2.2 P (hPD d₀ hd₀)
  exact (mem_pointRadical_iff hA.nondegenerate hP hqP).mp
    (hA.closure_le_comap_pointRadical hP hPD hg)

theorem mul_self_of_mem_closure_of_common_point (hA : A2Action D Q ρ) {P : V} (hP : P ≠ 0)
    (hPD : ∀ d ∈ D, P ∈ commSpace (ρ d)) {g : X} (hg : g ∈ Subgroup.closure D) : g * g = 1 := by
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, Subgroup.closure_empty, Subgroup.mem_bot] at hg
    rw [hg, one_mul]
  obtain ⟨u, hPu, hu⟩ := hA.exists_eichler_of_mem_closure hP hPD hD hg
  apply hA.injective
  rw [map_mul, map_one, hu]
  exact eichler_mul_self hPu

theorem commute_of_common_point (hA : A2Action D Q ρ) {P : V} (hP : P ≠ 0)
    (hPD : ∀ d ∈ D, P ∈ commSpace (ρ d)) {g h : X} (hg : g ∈ Subgroup.closure D)
    (hh : h ∈ Subgroup.closure D) : g * h = h * g := by
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, Subgroup.closure_empty, Subgroup.mem_bot] at hg
    rw [hg, one_mul, mul_one]
  obtain ⟨u, hPu, hu⟩ := hA.exists_eichler_of_mem_closure hP hPD hD hg
  obtain ⟨u', hPu', hu'⟩ := hA.exists_eichler_of_mem_closure hP hPD hD hh
  apply hA.injective
  rw [map_mul, map_mul, hu, hu', eichler_mul hPu hPu', eichler_mul hPu' hPu, add_comm]

theorem false_of_common_point (hA : A2Action D Q ρ) (hgen : Subgroup.closure D = ⊤)
    (hX : ¬ IsPGroup 2 X) {P : V} (hP : P ≠ 0) (hPD : ∀ d ∈ D, P ∈ commSpace (ρ d)) : False :=
  hX fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact hA.mul_self_of_mem_closure_of_common_point hP hPD (hgen ▸ Subgroup.mem_top g)⟩

end A2Action

end CFSG.LargeExtraspecial.A2Mod
