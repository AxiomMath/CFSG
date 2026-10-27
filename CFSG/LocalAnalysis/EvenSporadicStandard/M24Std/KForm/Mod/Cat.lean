module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Alt
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Even
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Setup
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG CFSG.Open CFSG.Blueprint

private theorem nonabelian_of_centralizer_eq_bot {K : Type} [Group K] (S : Subgroup K)
    [IsSimpleGroup ↥S] (hC : centralizer (S : Set K) = ⊥) : ∃ a b : ↥S, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hS : S = ⊥ := by
    rw [eq_bot_iff, ← hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥S)
  have : (a : K) ∈ (⊥ : Subgroup K) := hS ▸ a.2
  exact ha (Subtype.ext (by simpa using this))

private theorem conj_injective_of_nonabelian {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ center S := by
    rw [mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  have hbot : center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨x, y, hxy⟩ := hna
      exact hxy (mem_center_iff.mp (hc ▸ mem_top y) x)
  rw [hbot, mem_bot, inv_mul_eq_one] at hc
  exact hc

theorem catZ2S6_of_inputs (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    (hBT : EvenLieInvolutionTwoConstrained) (hEL : EvenOuterA6LeafMod)
    (hOB : OddLieA6TwoComponent) (hL : OddA6ModLeaf) (hSpor : SporadicZ2S6Leaf) : CatZ2S6 := by
  intro K _ _ S hSn hSs hcat hC z hz hζ
  obtain ⟨ζ⟩ := hζ
  haveI := hSn
  haveI := hSs
  have hna : ∃ a b : ↥S, a * b ≠ b * a := nonabelian_of_centralizer_eq_bot S hC
  have hinj : Function.Injective (MulAut.conj : ↥S →* MulAut ↥S) :=
    conj_injective_of_nonabelian hna
  have hsolv := hSch ↥S hna hcat
  have hMod := KForm.Mod.modData_of_quotient hz KForm.Reduction.rhyp_perm6 ζ
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition ↥S hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | hsp
  · obtain ⟨σ, J, hdata⟩ := KForm.Mod.z2s6_mod_setup S hC hsolv hz hMod
    exact Or.inl (KForm.Mod.z2s6_mod_alt_arm hdata hn θ)
  · obtain ⟨σ, J, hdata⟩ := KForm.Mod.z2s6_mod_setup S hC hsolv hz hMod
    exact KForm.Mod.z2s6_mod_odd_arm hOB hL hodd hdata
  · obtain ⟨σ, J, hdata⟩ := KForm.Mod.z2s6_mod_setup S hC hsolv hz hMod
    exact KForm.Mod.z2s6_mod_even_arm hBT hEL hinj heven hdata
  · exact (hSpor K S hSn hSs hC hsp z hz ⟨ζ⟩).elim

end CFSG.EvenSporadicStandard.M24Std
