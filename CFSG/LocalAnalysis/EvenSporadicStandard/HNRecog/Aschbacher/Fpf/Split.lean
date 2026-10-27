module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Cyclic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem range_eq_ker_of_ker_ne_bot (γ δ ν : V →ₗ[ZMod 2] V) (hγ : γ ^ 5 = 1) (hδ : δ ^ 5 = 1)
    (hγδ : δ * γ = γ * δ) (hνγ : ν * γ = γ * ν) (hνδ : ν * δ = δ ^ 4 * ν)
    (hν : Function.Injective ν) (h8 : finrank (ZMod 2) V = 8) (hγ1 : γ ≠ 1) (hδ1 : δ ≠ 1)
    (hker : LinearMap.ker (γ - 1) ≠ ⊥) :
    LinearMap.range (γ - 1) = LinearMap.ker (δ - 1) ∧
      finrank (ZMod 2) (LinearMap.range (γ - 1)) = 4 := by
  haveI : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_finrank_pos (by rw [h8]; norm_num)
  set R : Submodule (ZMod 2) V := LinearMap.range (γ - 1) with hR
  set R' : Submodule (ZMod 2) V := LinearMap.range (δ - 1) with hR'
  have hcommγ : γ * (γ - 1) = (γ - 1) * γ := by
    rw [mul_sub, sub_mul, mul_one, one_mul]
  have hcommδ : δ * (γ - 1) = (γ - 1) * δ := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hγδ]
  have hcommν : ν * (γ - 1) = (γ - 1) * ν := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hνγ]
  have hRγ : ∀ u ∈ R, γ u ∈ R := by
    intro u hu
    rw [hR, LinearMap.mem_range] at hu
    obtain ⟨x, hx⟩ := hu
    rw [← hx, hR, LinearMap.mem_range]
    exact ⟨γ x, by rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcommγ]⟩
  have hRδ : ∀ u ∈ R, δ u ∈ R := by
    intro u hu
    rw [hR, LinearMap.mem_range] at hu
    obtain ⟨x, hx⟩ := hu
    rw [← hx, hR, LinearMap.mem_range]
    exact ⟨δ x, by rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcommδ]⟩
  have hRν : ∀ u ∈ R, ν u ∈ R := by
    intro u hu
    rw [hR, LinearMap.mem_range] at hu
    obtain ⟨x, hx⟩ := hu
    rw [← hx, hR, LinearMap.mem_range]
    exact ⟨ν x, by rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcommν]⟩
  have hfix : ∀ u ∈ R, γ u = u → u = 0 := by
    intro u hu hγu
    have hmem : u ∈ LinearMap.ker (γ - 1) ⊓ LinearMap.range (γ - 1) := by
      refine ⟨?_, ?_⟩
      · simp [LinearMap.mem_ker, hγu]
      · rw [hR] at hu; exact hu
    have hbot := (disjoint_ker_range γ hγ).eq_bot
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hRne : R ≠ ⊥ := by
    intro h
    rw [hR] at h
    rw [LinearMap.range_eq_bot] at h
    exact hγ1 (sub_eq_zero.mp h)
  have hRfin : finrank (ZMod 2) R = 4 := by
    have h4 : 4 ∣ finrank (ZMod 2) R := by rw [hR]; exact four_dvd_finrank_range γ hγ
    have hRpos : 0 < finrank (ZMod 2) R := by
      have : 1 ≤ finrank (ZMod 2) R := Submodule.one_le_finrank_iff.mpr hRne
      omega
    have hsum : finrank (ZMod 2) R + finrank (ZMod 2) (LinearMap.ker (γ - 1)) = 8 := by
      have := LinearMap.finrank_range_add_finrank_ker (γ - 1)
      rw [h8] at this
      rw [← hR] at this
      exact this
    have hkpos : 1 ≤ finrank (ZMod 2) (LinearMap.ker (γ - 1)) :=
      Submodule.one_le_finrank_iff.mpr hker
    rcases h4 with ⟨k, hk⟩
    omega
  have hδonR : ∀ u ∈ R, δ u = u :=
    eq_self_of_conj_inv γ δ ν hγ hδ hγδ hνγ hνδ hν R hRγ hRδ hRν hfix hRfin
  have hRle : R ≤ LinearMap.ker (δ - 1) := by
    intro u hu
    simp [LinearMap.mem_ker, LinearMap.sub_apply, hδonR u hu]
  have hR'ne : R' ≠ ⊥ := by
    intro h
    rw [hR'] at h
    rw [LinearMap.range_eq_bot] at h
    exact hδ1 (sub_eq_zero.mp h)
  have hker' : LinearMap.ker (δ - 1) ≠ ⊥ := by
    intro h
    exact hRne (le_bot_iff.mp (h ▸ hRle))
  have hR'fin : finrank (ZMod 2) R' = 4 := by
    have h4 : 4 ∣ finrank (ZMod 2) R' := by rw [hR']; exact four_dvd_finrank_range δ hδ
    have hR'pos : 0 < finrank (ZMod 2) R' := by
      have : 1 ≤ finrank (ZMod 2) R' := Submodule.one_le_finrank_iff.mpr hR'ne
      omega
    have hsum : finrank (ZMod 2) R' + finrank (ZMod 2) (LinearMap.ker (δ - 1)) = 8 := by
      have := LinearMap.finrank_range_add_finrank_ker (δ - 1)
      rw [h8] at this
      rw [← hR'] at this
      exact this
    have hkpos : 1 ≤ finrank (ZMod 2) (LinearMap.ker (δ - 1)) :=
      Submodule.one_le_finrank_iff.mpr hker'
    rcases h4 with ⟨k, hk⟩
    omega
  have hkerfin : finrank (ZMod 2) (LinearMap.ker (δ - 1)) = 4 := by
    have hsum : finrank (ZMod 2) R' + finrank (ZMod 2) (LinearMap.ker (δ - 1)) = 8 := by
      have := LinearMap.finrank_range_add_finrank_ker (δ - 1)
      rw [h8] at this
      rw [← hR'] at this
      exact this
    omega
  have hReq : R = LinearMap.ker (δ - 1) :=
    Submodule.eq_of_le_of_finrank_eq hRle (by rw [hRfin, hkerfin])
  exact ⟨hReq, hRfin⟩

end CFSG.EvenSporadicStandard.HNRecog.Fpf
