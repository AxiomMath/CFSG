module

public import CFSG.RepresentationTheory.CentralThreeCommutatorRank
import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleModule.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RepresentationTheory

theorem finrank_le_finrank_quotient_add_finrank_inf {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Y E : Submodule K V) :
    Module.finrank K Y ≤ Module.finrank K (V ⧸ E) + Module.finrank K ↥(Y ⊓ E) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq Y E
  have h2 := Submodule.finrank_quotient_add_finrank E
  have h3 := Submodule.finrank_le (Y ⊔ E)
  omega

theorem sub_one_mul_self_mul_sub_one_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Z : Module.End (ZMod 2) V} (hZ : Z ^ 3 = 1) : (Z - 1) * Z * (Z - 1) = Z - 1 := by
  have h2 : (2 : Module.End (ZMod 2) V) = 0 := by
    ext v
    simp only [Module.End.ofNat_apply, LinearMap.zero_apply, two_smul, zmod_two_add_self]
  have h : (Z - 1) * Z * (Z - 1) - (Z - 1) = (Z ^ 3 - 1) + 2 * (1 - Z ^ 2) := by
    noncomm_ring
  rw [hZ, sub_self, h2, zero_mul, add_zero] at h
  exact sub_eq_zero.1 h

theorem range_sub_one_inf_eq_inf_of_filtration {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {Z : Module.End (ZMod 2) V} (hZ : Z ^ 3 = 1)
    {E₁ E₂ : Submodule (ZMod 2) V} (h12 : E₁ ≤ E₂) (hE₂ : ∀ v ∈ E₂, Z v ∈ E₂)
    (hZ₂ : ∀ v ∈ E₂, Z v - v ∈ E₁) :
    LinearMap.range (Z - 1) ⊓ E₂ = LinearMap.range (Z - 1) ⊓ E₁ := by
  refine le_antisymm (le_inf inf_le_left ?_) (inf_le_inf_left _ h12)
  rintro y ⟨⟨v, hv⟩, hyE⟩
  have key : Z (Z y) - Z y = y := by
    calc Z (Z y) - Z y = (Z - 1) (Z y) := by rw [LinearMap.sub_apply, Module.End.one_apply]
      _ = ((Z - 1) * Z * (Z - 1)) v := by simp only [Module.End.mul_apply, hv]
      _ = (Z - 1) v := by rw [sub_one_mul_self_mul_sub_one_eq hZ]
      _ = y := hv
  rw [← key]
  exact hZ₂ _ (hE₂ y hyE)

theorem rank_filtration_core {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (a b z : LinearMap.GeneralLinearGroup (ZMod 2) V) (hz : z = a * b * a⁻¹ * b⁻¹)
    (hz3 : z ^ 3 = 1) (hza : z * a = a * z) (hzb : z * b = b * z) (hz1 : z ≠ 1)
    (E₁ E₂ : Submodule (ZMod 2) V) (h12 : E₁ ≤ E₂)
    (hE₂ : ∀ v ∈ E₂, (z : Module.End (ZMod 2) V) v ∈ E₂)
    (hz₂ : ∀ v ∈ E₂, (z : Module.End (ZMod 2) V) v - v ∈ E₁)
    (hd₂ : Module.finrank (ZMod 2) (V ⧸ E₂) ≤ 2) (hd₁ : Module.finrank (ZMod 2) E₁ ≤ 4) :
    Module.finrank (ZMod 2) (V ⧸ E₂) = 2 ∧ Module.finrank (ZMod 2) E₁ = 4 := by
  set Y : Submodule (ZMod 2) V := LinearMap.range ((z : Module.End (ZMod 2) V) - 1) with hY
  have h6 : 6 ≤ Module.finrank (ZMod 2) Y := by
    have hdvd := six_dvd_rank_central_three_commutator a b z hz hz3 hza hzb
    have hne : Module.finrank (ZMod 2) Y ≠ 0 := by
      intro h0
      rw [Submodule.finrank_eq_zero, hY, LinearMap.range_eq_bot, sub_eq_zero] at h0
      exact hz1 (Units.ext h0)
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have hZ3 : (z : Module.End (ZMod 2) V) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz3, Units.val_one]
  have hk : Module.finrank (ZMod 2) ↥(Y ⊓ E₂) ≤ Module.finrank (ZMod 2) E₁ := by
    rw [hY, range_sub_one_inf_eq_inf_of_filtration hZ3 h12 hE₂ hz₂]
    exact Submodule.finrank_mono inf_le_right
  have hup := finrank_le_finrank_quotient_add_finrank_inf Y E₂
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
