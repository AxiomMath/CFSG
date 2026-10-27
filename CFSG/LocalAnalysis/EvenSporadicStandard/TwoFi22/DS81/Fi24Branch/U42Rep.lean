module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Main

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

theorem IsU42Two.of_mulEquiv {A A' : Type} [Group A] [Group A'] (e : A ≃* A')
    (h : IsU42Two A) : IsU42Two A' := by
  obtain ⟨U, hUgrp, hU, ⟨f⟩⟩ := h
  exact ⟨U, hUgrp, hU, ⟨e.symm.trans f⟩⟩

private theorem index_two_unique {B : Type} [Group B] (hF : U42Facts) (hB : IsU42Two B)
    {M1 M2 : Subgroup B} (h1 : M1.index = 2) (h2 : M2.index = 2) : M1 = M2 := by
  by_contra hne
  have hcardB : Nat.card B = 2 ^ 7 * 3 ^ 4 * 5 := hF.card B hB
  haveI : Finite B := Nat.finite_of_card_ne_zero (by rw [hcardB]; norm_num)
  haveI : M1.Normal := Subgroup.normal_of_index_eq_two h1
  haveI : M2.Normal := Subgroup.normal_of_index_eq_two h2
  rcases hF.normal B hB (M1 ⊓ M2) inferInstance with hbot | hidx | htop
  · have hle : (M1 ⊓ M2).index ≤ M1.index * M2.index :=
      Subgroup.index_inf_le (H := M1) (K := M2)
    rw [h1, h2] at hle
    rw [hbot, Subgroup.index_bot, hcardB] at hle
    norm_num at hle
  · have hrel : M1.relIndex M2 = 1 := by
      have := Subgroup.index_inf (H := M1) (K := M2)
      rw [hidx, h2] at this
      omega
    have hle : M2 ≤ M1 := Subgroup.relIndex_eq_one.mp hrel
    have hcard_eq : Nat.card M1 = Nat.card M2 := by
      have c1 := Subgroup.card_mul_index M1
      have c2 := Subgroup.card_mul_index M2
      rw [h1] at c1
      rw [h2] at c2
      omega
    exact hne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard_eq)).symm
  · have hM1top : M1 = ⊤ := top_le_iff.mp (htop ▸ (inf_le_left : M1 ⊓ M2 ≤ M1))
    rw [hM1top, Subgroup.index_top] at h1
    norm_num at h1

theorem statedClassicalModel_of_index_two (hF : U42Facts) {A : Type} [Group A]
    (hA : IsU42Two A) {N : Subgroup A} (hN : N.index = 2) :
    CFSG.Open.StatedClassicalModel ↥N .PSU 4 2 1 := by
  obtain ⟨U, hUgrp, hU, ⟨e⟩⟩ := hA
  have hA' : IsU42Two A := ⟨U, hUgrp, hU, ⟨e⟩⟩
  letI : Group U := hUgrp
  have hcardU : Nat.card U = 25920 :=
    CFSG.EvenSporadicStandard.M24Std.card_of_statedClassicalModel_psu_four_two hU
  obtain ⟨-, hUsimple⟩ := CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity U 4 2 1 hU
  have hcenter : Subgroup.center U = ⊥ := by
    rcases hUsimple.eq_bot_or_eq_top_of_normal (Subgroup.center U) with h | h
    · exact h
    · exfalso
      haveI : IsMulCommutative U := Subgroup.center_eq_top_iff.mp h
      have hprime : (Nat.card U).Prime := (Group.is_simple_iff_prime_card (α := U)).mp hUsimple
      rw [hcardU] at hprime
      norm_num at hprime
  have hker : (MulAut.conj : U →* MulAut U).ker = Subgroup.center U := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have hx : g * x * g⁻¹ = x := by
        have := congrArg (fun f : MulAut U => f x) h
        simpa [MulAut.conj_apply] using this
      calc x * g = (g * x * g⁻¹) * g := by rw [hx]
        _ = g * x := by group
    · intro h
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      have hx : x * g = g * x := h x
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hx.symm]
        _ = x := by group
  have hcinj : Function.Injective (MulAut.conj : U →* MulAut U) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [hker, hcenter]
  have hcard_range : Nat.card (MulAut.conj : U →* MulAut U).range = 25920 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hcinj).toEquiv]
    exact hcardU
  have hcard_aut : Nat.card (MulAut U) = 2 ^ 7 * 3 ^ 4 * 5 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hF.card A hA'
  have hIindex : (MulAut.conj : U →* MulAut U).range.index = 2 := by
    have hlag := Subgroup.card_mul_index (MulAut.conj : U →* MulAut U).range
    rw [hcard_range, hcard_aut] at hlag
    norm_num at hlag
    omega
  have hA_aut : IsU42Two (MulAut U) := IsU42Two.of_mulEquiv e hA'
  have hNmap_index : (N.map (e : A →* MulAut U)).index = 2 := by
    rw [Subgroup.index_map_equiv N e]
    exact hN
  have hN'I : N.map (e : A →* MulAut U) = (MulAut.conj : U →* MulAut U).range :=
    index_two_unique hF hA_aut hNmap_index hIindex
  have iso : U ≃* ↥N :=
    (MonoidHom.ofInjective hcinj).trans ((hN'I ▸ MulEquiv.subgroupMap e N).symm)
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv iso hU

theorem isU42Two_or_model_of_normal (hF : U42Facts) {A : Type} [Group A] (hA : IsU42Two A)
    {T : Subgroup A} (hT : T.Normal) (hne : T ≠ ⊥) :
    IsU42Two ↥T ∨ CFSG.Open.StatedClassicalModel ↥T .PSU 4 2 1 := by
  rcases hF.normal A hA T hT with hbot | hidx | htop
  · exact absurd hbot hne
  · exact Or.inr (statedClassicalModel_of_index_two hF hA hidx)
  · rw [htop]
    exact Or.inl (IsU42Two.of_mulEquiv (Subgroup.topEquiv).symm hA)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch