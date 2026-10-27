module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Cross
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Simple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Cell

open Matrix

theorem excl55_fl5 : Excl55 FL5 := by
  classical
  intro k Y _ hF hinv
  obtain ⟨A, _, _, J, hJ, ⟨eJ⟩, hall⟩ := hinv
  obtain ⟨p0, f, hp0, hf, hq4, hL⟩ := hF
  obtain ⟨F, hFfield, hFfin, hcard, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have := Nat.even_iff.mp this
    omega
  have hfodd : Odd f := by
    by_contra hnot
    obtain ⟨m, rfl⟩ := Nat.not_odd_iff_even.mp hnot
    have hsq : p0 ^ (m + m) = (p0 ^ m) ^ 2 := by ring
    rw [hsq] at hq4
    have h4 : ∀ a : ℕ, a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      intro a
      have := Nat.mod_lt a (by norm_num : 4 > 0)
      interval_cases h : a % 4 <;> simp [Nat.pow_mod, h]
    rcases h4 (p0 ^ m) with h | h <;> omega
  have : Fact p0.Prime := ⟨hp0⟩
  have : CharP F p0 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hK2 : ringChar F ≠ 2 := by rwa [ringChar.eq F p0]
  have hFodd : Odd (Nat.card F) := by rw [hcard, Nat.odd_iff]; omega
  have h3 : 3 ≤ Nat.card F := by rw [hcard]; omega
  let ψ : ↥J →* projectiveSL 5 F :=
    (e.toMonoidHom.comp eJ.toMonoidHom).comp (QuotientGroup.mk' (center ↥J))
  have hψ : Function.Surjective ψ :=
    (e.surjective.comp eJ.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ center ↥J := by
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
    by_contra h
    exact hnsY (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)))
  let s : projectiveSL 5 F := e (eJ ub)
  have hs : orderOf s = 2 := by
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hub
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hα2 : (MulAut.conj s) ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
  rcases linear5_involution_cases hp0 hf hcard hfodd hK2 (MulAut.conj s) hα2 with
    ⟨ρ, hρ, hfix⟩ | ⟨hnot, -⟩
  · have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    have hcomm : ∀ g, s * ρ g = ρ g * s := by
      intro g
      have h1 := hfix g
      rw [MulAut.conj_apply] at h1
      calc s * ρ g = (s * ρ g * s⁻¹) * s := by group
        _ = ρ g * s := by rw [h1]
    obtain ⟨x, hx2, hsec⟩ := exists_involution_section ψ hψ hker hs ρ hρ hcomm
    have hsec' : IsSection (projectiveSL 3 F) ↥(centralizer ({x} : Set A)) := by
      obtain ⟨U, φ, hφ⟩ := hsec
      exact ⟨U, (QuotientGroup.mk' (scalars 3 F)).comp φ,
        (QuotientGroup.mk'_surjective _).comp hφ⟩
    have := isSimpleGroup_projectiveSL3 F
    have := isPerfect_projectiveSL3 F
    have : Nontrivial (projectiveSL 3 F) := IsSimpleGroup.toNontrivial
    have hns : ¬ Group.IsSolvable (projectiveSL 3 F) := Group.IsPerfect.not_isSolvable _
    exact not_kindFactorAll hp02 (involved_qdSL_projectiveSL3 (p := p0))
      (not_card_dvd_factorial_projectiveSL3 hFodd h3) (hall x hx2 _ hns hsec')
  · exact absurd rfl (hnot s)

end Cell

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
