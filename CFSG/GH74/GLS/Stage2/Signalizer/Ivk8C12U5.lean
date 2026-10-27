module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Sec
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem psu3_section_of_U5 {Y : Type} [Group Y] {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hp : p ≠ 2) (e : Y ≃* hypPSU h 2 1) (u : Y)
    (hu : orderOf u = 2) :
    IsSection (StatedProj (StatedSU 3 (p ^ f) K)) ↥(centralizer ({u} : Set Y)) := by
  classical
  set v : hypPSU h 2 1 := e u with hv
  have hv2 : v ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    rw [hv, ← map_pow, this, map_one]
  have hα2 : (MulAut.conj v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  rcases unitary5_involution_cases h hp (MulAut.conj v) hα2 with
    ⟨ψ, hψi, hfix⟩ | ⟨hnot, -⟩
  · let c : ↥((hypProj h 2 1).comp ψ).range →* StatedProj (StatedSU 3 (p ^ f) K) :=
      (QuotientGroup.mk' _).comp (MonoidHom.ofInjective hψi).symm.toMonoidHom
    have hc : Function.Surjective c :=
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hψi).symm.surjective
    have hQ : ((hypProj h 2 1).comp ψ).range ≤ centralizer ({v} : Set (hypPSU h 2 1)) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hfix s hs
      rw [MulAut.conj_apply] at h1
      calc s * v = (v * s * v⁻¹) * v := by rw [h1]
        _ = v * s := by group
    exact IsSection.of_equiv (centEquiv e u)
      (IsSection.of_le_le hQ (isSection_of_surjective_hom c hc))
  · exact absurd rfl (hnot v)

theorem cellAbs_U5 : CellAbs FU5 := by
  intro A _ _ zb Sb Vb J hfr hJ _ hF
  exfalso
  obtain ⟨p0, f, hp0, hf, hq4, hL⟩ := hF
  obtain ⟨K, _, _, h, hcard, ⟨e⟩⟩ := exists_unitaryData_equiv hp0 hf hL
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have := Nat.even_iff.mp this
    omega
  have : Fact p0.Prime := ⟨hp0⟩
  have : CharP K p0 := h.charP
  have hP3 := isPerfect_statedSU_three_odd (K := K) hcard hp02
  have := isSimpleGroup_statedProj_three (K := K) hcard hq4
  have : Group.IsPerfect (StatedProj (StatedSU 3 (p0 ^ f) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : Nontrivial (StatedProj (StatedSU 3 (p0 ^ f) K)) := IsSimpleGroup.toNontrivial
  have hns : ¬ Group.IsSolvable (StatedProj (StatedSU 3 (p0 ^ f) K)) :=
    Group.IsPerfect.not_isSolvable _
  have hQ : ¬ KindFactorAll Kind.ly (StatedProj (StatedSU 3 (p0 ^ f) K)) := fun hk =>
    not_card_dvd_factorial_statedProj_three hf hcard hq4 (KindFactorAll.card_dvd hk (Or.inr rfl))
  exact false_of_section_all hfr hJ hns hQ fun u hu => psu3_section_of_U5 h hp02 e u hu

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
