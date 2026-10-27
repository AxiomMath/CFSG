module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Sec
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem p3_section_of_L5 {Y : Type} [Group Y] {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (hfodd : Odd f)
    (hK2 : ringChar F ≠ 2) (e : Y ≃* projectiveSL 5 F) (u : Y) (hu : orderOf u = 2) :
    IsSection (projectiveSL 3 F) ↥(centralizer ({u} : Set Y)) := by
  classical
  set v : projectiveSL 5 F := e u with hv
  have hv2 : v ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    rw [hv, ← map_pow, this, map_one]
  have hα2 : (MulAut.conj v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  rcases linear5_involution_cases hp hf hcard hfodd hK2 (MulAut.conj v) hα2 with
    ⟨ρ, hρ, hfix⟩ | ⟨hnot, -⟩
  · let c : ↥ρ.range →* projectiveSL 3 F :=
      (QuotientGroup.mk' (scalars 3 F)).comp (MonoidHom.ofInjective hρ).symm.toMonoidHom
    have hc : Function.Surjective c :=
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hρ).symm.surjective
    have hQ : ρ.range ≤ centralizer ({v} : Set (projectiveSL 5 F)) := by
      rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hfix g
      rw [MulAut.conj_apply] at h1
      calc ρ g * v = (v * ρ g * v⁻¹) * v := by rw [h1]
        _ = v * ρ g := by group
    exact IsSection.of_equiv (centEquiv e u)
      (IsSection.of_le_le hQ (isSection_of_surjective_hom c hc))
  · exact absurd rfl (hnot v)

theorem cellAbs_L5 : CellAbs FL5 := by
  intro A _ _ zb Sb Vb J hfr hJ _ hF
  exfalso
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
  have := isSimpleGroup_projectiveSL3 F
  have := isPerfect_projectiveSL3 F
  have : Nontrivial (projectiveSL 3 F) := IsSimpleGroup.toNontrivial
  have hns : ¬ Group.IsSolvable (projectiveSL 3 F) := Group.IsPerfect.not_isSolvable _
  have hQ : ¬ KindFactorAll Kind.ly (projectiveSL 3 F) := fun h =>
    not_card_dvd_factorial_projectiveSL3 hFodd h3 (KindFactorAll.card_dvd h (Or.inr rfl))
  exact false_of_section_all hfr hJ hns hQ fun u hu =>
    p3_section_of_L5 hp0 hf hcard hfodd hK2 e u hu

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
