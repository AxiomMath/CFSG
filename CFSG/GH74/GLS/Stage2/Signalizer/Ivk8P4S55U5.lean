module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Cross
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Simple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

theorem excl55_fu5 : Excl55 FU5 := by
  classical
  intro k Y _ hF hinv
  obtain ⟨A, _, _, J, hJ, ⟨eJ⟩, hall⟩ := hinv
  obtain ⟨p0, f, hp0, hf, hq4, hL⟩ := hF
  obtain ⟨K, _, _, h, hcard, ⟨e⟩⟩ := exists_unitaryData_equiv hp0 hf hL
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have := Nat.even_iff.mp this
    omega
  have : Fact p0.Prime := ⟨hp0⟩
  have : CharP K p0 := h.charP
  let ψJ : ↥J →* hypPSU h 2 1 :=
    (e.toMonoidHom.comp eJ.toMonoidHom).comp (QuotientGroup.mk' (center ↥J))
  have hψJ : Function.Surjective ψJ :=
    (e.surjective.comp eJ.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : ψJ.ker ≤ center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk' (center ↥J)) x = 1 := by
      apply eJ.injective
      apply e.injective
      rw [map_one, map_one]
      exact hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hnsY : ¬ Group.IsSolvable (↥J ⧸ center ↥J) := by
    intro hs
    have hcomm := (@IsSimpleGroup.comm_iff_isSolvable _ _ hJ.1.2.1).2 hs
    obtain ⟨a, b, hab⟩ := hJ.1.2.2
    exact hab (hcomm a b)
  obtain ⟨ub, hub⟩ : ∃ u : ↥J ⧸ center ↥J, orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine exists_prime_orderOf_dvd_card' 2 ?_
    by_contra h2
    exact hnsY (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)))
  let s : hypPSU h 2 1 := e (eJ ub)
  have hs : orderOf s = 2 := by
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hub
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hα2 : (MulAut.conj s) ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
  rcases unitary5_involution_cases h hp02 (MulAut.conj s) hα2 with
    ⟨ψ, hψi, hfix⟩ | ⟨hnot, -⟩
  · have hP3 := isPerfect_statedSU_three_odd (K := K) hcard hp02
    let ρ : ↥(StatedSU 3 (p0 ^ f) K) →* hypPSU h 2 1 := (hypProj h 2 1).comp ψ
    have hcomm : ∀ g, s * ρ g = ρ g * s := by
      intro g
      have h1 := hfix (ρ g) ⟨g, rfl⟩
      rw [MulAut.conj_apply] at h1
      calc s * ρ g = (s * ρ g * s⁻¹) * s := by group
        _ = ρ g * s := by rw [h1]
    obtain ⟨x, hx2, hsec⟩ := exists_involution_section ψJ hψJ hker hs ρ hψi hcomm
    have hsec' : IsSection (StatedProj (StatedSU 3 (p0 ^ f) K)) ↥(centralizer ({x} : Set A)) := by
      obtain ⟨U, φ, hφ⟩ := hsec
      exact ⟨U, (QuotientGroup.mk' _).comp φ, (QuotientGroup.mk'_surjective _).comp hφ⟩
    have := isSimpleGroup_statedProj_three (K := K) hcard hq4
    have : Group.IsPerfect (StatedProj (StatedSU 3 (p0 ^ f) K)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have : Nontrivial (StatedProj (StatedSU 3 (p0 ^ f) K)) := IsSimpleGroup.toNontrivial
    have hns : ¬ Group.IsSolvable (StatedProj (StatedSU 3 (p0 ^ f) K)) :=
      Group.IsPerfect.not_isSolvable _
    exact not_kindFactorAll hp02 (involved_qdSL_statedProj_three hcard)
      (not_card_dvd_factorial_statedProj_three hf hcard hq4) (hall x hx2 _ hns hsec')
  · exact absurd rfl (hnot s)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
