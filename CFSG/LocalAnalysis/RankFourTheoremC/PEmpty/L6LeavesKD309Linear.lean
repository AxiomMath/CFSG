module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup

variable {Y V : Type} [Group Y] [AddCommGroup V] [Module (ZMod 2) V]

theorem two_nsmul_eq_zero (v : V) : (2 : ℕ) • v = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem odd_nsmul_eq_self {n : ℕ} (hn : Odd n) (v : V) : n • v = v := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, mul_nsmul, two_nsmul_eq_zero, smul_zero, zero_add, one_nsmul]

@[expose] def fixSub (ρ : Representation (ZMod 2) Y V) (H : Subgroup Y) : Submodule (ZMod 2) V :=
  ⨅ h ∈ H, LinearMap.ker (ρ h - 1)

theorem mem_fixSub {ρ : Representation (ZMod 2) Y V} {H : Subgroup Y} {v : V} :
    v ∈ fixSub ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  simp only [fixSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

@[expose] def commSub (ρ : Representation (ZMod 2) Y V) (H : Subgroup Y) : Submodule (ZMod 2) V :=
  ⨆ h ∈ H, LinearMap.range (ρ h - 1)

theorem apply_sub_one_mem_commSub {ρ : Representation (ZMod 2) Y V} {H : Subgroup Y} {h : Y}
    (hh : h ∈ H) (w : V) : (ρ h - 1) w ∈ commSub ρ H :=
  (Submodule.mem_iSup_of_mem h (Submodule.mem_iSup_of_mem hh ⟨w, rfl⟩))

@[expose] noncomputable def eSum (ρ : Representation (ZMod 2) Y V) (H : Subgroup Y) [Fintype H] :
    V →ₗ[ZMod 2] V :=
  ∑ h : H, ρ h

theorem eSum_apply (ρ : Representation (ZMod 2) Y V) (H : Subgroup Y) [Fintype H] (v : V) :
    eSum ρ H v = ∑ h : H, ρ h v := by
  simp [eSum, LinearMap.sum_apply]

theorem eSum_apply_of_mem_fixSub {ρ : Representation (ZMod 2) Y V} {H : Subgroup Y} [Fintype H]
    (hodd : Odd (Fintype.card H)) {v : V} (hv : v ∈ fixSub ρ H) : eSum ρ H v = v := by
  rw [eSum_apply]
  have : ∀ h : H, ρ h v = v := fun h => mem_fixSub.mp hv h h.2
  simp only [this, Finset.sum_const, Finset.card_univ]
  exact odd_nsmul_eq_self hodd v

theorem eSum_apply_sub_one {ρ : Representation (ZMod 2) Y V} {H : Subgroup Y} [Fintype H]
    {h₀ : Y} (hh₀ : h₀ ∈ H) (w : V) : eSum ρ H ((ρ h₀ - 1) w) = 0 := by
  rw [eSum_apply]
  have h1 : ∀ h : H, ρ h ((ρ h₀ - 1) w) = ρ ((h * ⟨h₀, hh₀⟩ : H) : Y) w - ρ h w := by
    intro h
    simp [map_sub, ← Module.End.mul_apply, ← map_mul]
  simp only [h1, Finset.sum_sub_distrib]
  have h2 : ∑ h : H, ρ ((h * ⟨h₀, hh₀⟩ : H) : Y) w = ∑ h : H, ρ (h : Y) w :=
    Fintype.sum_equiv (Equiv.mulRight (⟨h₀, hh₀⟩ : H)) _ _ (fun h => rfl)
  rw [h2, sub_self]

theorem eSum_apply_of_mem_commSub {ρ : Representation (ZMod 2) Y V} {H : Subgroup Y} [Fintype H]
    {v : V} (hv : v ∈ commSub ρ H) : eSum ρ H v = 0 := by
  have : commSub ρ H ≤ LinearMap.ker (eSum ρ H) := by
    refine iSup₂_le fun h hh => ?_
    rintro _ ⟨w, rfl⟩
    exact eSum_apply_sub_one hh w
  exact this hv

theorem disjoint_fixSub_commSub (ρ : Representation (ZMod 2) Y V) (H : Subgroup Y) [Fintype H]
    (hodd : Odd (Fintype.card H)) : Disjoint (fixSub ρ H) (commSub ρ H) := by
  rw [Submodule.disjoint_def]
  intro v hv1 hv2
  rw [← eSum_apply_of_mem_fixSub hodd hv1]
  exact eSum_apply_of_mem_commSub hv2

@[expose] noncomputable def repEquiv (ρ : Representation (ZMod 2) Y V) : Y →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.toHomUnits

@[simp] theorem repEquiv_apply (ρ : Representation (ZMod 2) Y V) (g : Y) (v : V) :
    repEquiv ρ g v = ρ g v := rfl

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
