module


import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs3
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

open Subgroup

private theorem ne_bot_of_centralizer_eq_bot {X : Type} [Group X] [Finite X]
    {W N : Subgroup X} (eW : ↥W ≃* Equiv.Perm (Fin 5))
    (hC : Subgroup.centralizer (N : Set X) = ⊥) : N ≠ ⊥ := by
  intro hbot
  have hbotC : Subgroup.centralizer (N : Set X) = ⊤ := by
    rw [hbot]
    exact Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
  rw [hbotC] at hC
  have hXcard : Nat.card X = 1 := by
    rw [← Subgroup.card_top (G := X), hC, Subgroup.card_bot]
  have hWle : Nat.card W ≤ Nat.card X := by
    simpa using Subgroup.card_le_of_le (H := W) (K := ⊤) le_top
  have hWcard : Nat.card W = 120 := by
    rw [Nat.card_congr eW.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  omega

private theorem image_commutator_eq_alt_five {X : Type} [Group X] [Finite X]
    {W N : Subgroup X} (eW : ↥W ≃* Equiv.Perm (Fin 5)) (hN : N.Normal) (hNW : N ≤ W)
    (hNne : N ≠ ⊥) :
    ∃ Aw : Subgroup W, Aw.map W.subtype = ⁅N, N⁆ ∧
      Aw.map eW.toMonoidHom = alternatingGroup (Fin 5) := by
  classical
  let Nw : Subgroup W := N.subgroupOf W
  have hNw : Nw.Normal := hN.subgroupOf W
  let N' : Subgroup (Equiv.Perm (Fin 5)) := Nw.map eW.toMonoidHom
  have hN' : N'.Normal := hNw.map eW.toMonoidHom eW.surjective
  have hN'nt : Nontrivial N' := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    apply hNne
    have hNwbot : Nw = ⊥ :=
      Subgroup.map_injective (f := eW.toMonoidHom) eW.injective (by simpa [N'] using hbot)
    have hNwbot' : N.subgroupOf W = ⊥ := hNwbot
    have hmap := Subgroup.map_subgroupOf_eq_of_le (H := N) (K := W) hNW
    rw [hNwbot'] at hmap
    simpa using hmap.symm
  have hA5N' : alternatingGroup (Fin 5) ≤ N' :=
    @Equiv.Perm.alternatingGroup_le_of_normal (Fin 5) _ _ (by simp) N' hN' hN'nt
  let Aw : Subgroup W := ⁅Nw, Nw⁆
  have hcommN' : ⁅N', N'⁆ = alternatingGroup (Fin 5) := by
    apply le_antisymm
    · calc ⁅N', N'⁆ ≤ ⁅(⊤ : Subgroup (Equiv.Perm (Fin 5))), ⊤⁆ :=
            Subgroup.commutator_mono le_top le_top
        _ = alternatingGroup (Fin 5) := alternatingGroup.commutator_perm_eq (by simp)
    · calc alternatingGroup (Fin 5) =
            ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ :=
            (commutator_alternatingGroup_eq_self (by simp)).symm
        _ ≤ ⁅N', N'⁆ := Subgroup.commutator_mono hA5N' hA5N'
  refine ⟨Aw, ?_, ?_⟩
  · simp only [Aw, Nw, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hNW]
  · simp only [Aw, Subgroup.map_commutator]
    exact hcommN'

private theorem eq_one_of_mem_centralizer_commutator {X : Type} [Group X]
    {W N : Subgroup X} (eW : ↥W ≃* Equiv.Perm (Fin 5)) (hNW : N ≤ W)
    {Aw : Subgroup W}
    (hAwA : Aw.map W.subtype = ⁅N, N⁆)
    (hAwImage : Aw.map eW.toMonoidHom = alternatingGroup (Fin 5))
    {c : X} (hcN : c ∈ N)
    (hcC : c ∈ Subgroup.centralizer ((⁅N, N⁆ : Subgroup X) : Set X)) : c = 1 := by
  classical
  let cW : W := ⟨c, hNW hcN⟩
  have hσ : MulAut.conjNormal (H := alternatingGroup (Fin 5)) (eW cW) = 1 := by
    apply MulEquiv.ext
    intro a
    have ha : (a : Equiv.Perm (Fin 5)) ∈ Aw.map eW.toMonoidHom := by
      rw [hAwImage]
      exact a.2
    obtain ⟨k, hkAw, hk⟩ := Subgroup.mem_map.mp ha
    have hkA : (k : X) ∈ ⁅N, N⁆ := by
      have hmem : (k : X) ∈ Aw.map W.subtype := Subgroup.mem_map.mpr ⟨k, hkAw, rfl⟩
      rwa [hAwA] at hmem
    have hck : c * (k : X) = (k : X) * c :=
      (Subgroup.mem_centralizer_iff.mp hcC (k : X) hkA).symm
    have hckW : cW * k = k * cW := by
      apply Subtype.ext
      exact hck
    have hk' : eW k = (a : Equiv.Perm (Fin 5)) := hk
    have hcomm : eW cW * (a : Equiv.Perm (Fin 5)) =
        (a : Equiv.Perm (Fin 5)) * eW cW := by
      have h1 := congrArg eW hckW
      simpa [map_mul, hk'] using h1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    calc eW cW * (a : Equiv.Perm (Fin 5)) * (eW cW)⁻¹ =
          (a : Equiv.Perm (Fin 5)) * eW cW * (eW cW)⁻¹ := by rw [hcomm]
      _ = (a : Equiv.Perm (Fin 5)) := by group
  have hσ1 : eW cW = 1 :=
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 5
      (by norm_num) hσ
  have hcW : cW = 1 := eW.injective (by simpa using hσ1)
  simpa [cW] using congrArg Subtype.val hcW

private theorem centralizer_commutator_eq_bot_of_image {X : Type} [Group X] [Finite X]
    {W N : Subgroup X} (eW : ↥W ≃* Equiv.Perm (Fin 5)) (hN : N.Normal) (hNW : N ≤ W)
    (hC : Subgroup.centralizer (N : Set X) = ⊥)
    {Aw : Subgroup W}
    (hAwA : Aw.map W.subtype = ⁅N, N⁆)
    (hAwImage : Aw.map eW.toMonoidHom = alternatingGroup (Fin 5)) :
    Subgroup.centralizer ((⁅N, N⁆ : Subgroup X) : Set X) = ⊥ := by
  classical
  have hAcomm : (⁅N, N⁆ : Subgroup X).Normal :=
    Subgroup.commutator_normal (H₁ := N) (H₂ := N) (h₁ := hN) (h₂ := hN)
  let C : Subgroup X := Subgroup.centralizer ((⁅N, N⁆ : Subgroup X) : Set X)
  have hCn : C.Normal := by
    simpa [C] using (@Subgroup.normal_centralizer X _ (⁅N, N⁆ : Subgroup X) hAcomm)
  have hCNbot : C ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_centralizer_commutator eW hNW hAwA hAwImage hc.2 hc.1
  have hCle : C ≤ Subgroup.centralizer (N : Set X) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (Subgroup.commute_of_normal_of_disjoint C N hCn hN
      (disjoint_iff.mpr hCNbot) c n hc hn).symm.eq
  have hCbot : C = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hc' := hCle hc
    rw [hC, Subgroup.mem_bot] at hc'
    exact hc'
  simpa [C] using hCbot

theorem eq_top_of_mulEquiv_perm_five {X : Type} [Group X] [Finite X] {W N : Subgroup X}
    (eW : ↥W ≃* Equiv.Perm (Fin 5)) (hN : N.Normal) (hNW : N ≤ W)
    (hC : Subgroup.centralizer (N : Set X) = ⊥) : W = ⊤ := by
  classical
  have hWcard : Nat.card W = 120 := by
    rw [Nat.card_congr eW.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hNne : N ≠ ⊥ := ne_bot_of_centralizer_eq_bot eW hC
  obtain ⟨Aw, hAwA, hAwImage⟩ :=
    image_commutator_eq_alt_five eW hN hNW hNne
  let A : Subgroup X := ⁅N, N⁆
  have hAn : A.Normal :=
    Subgroup.commutator_normal (H₁ := N) (H₂ := N) (h₁ := hN) (h₂ := hN)
  let eAwA : Aw ≃* A :=
    (Subgroup.equivMapOfInjective Aw W.subtype W.subtype_injective).trans
      (MulEquiv.subgroupCongr hAwA)
  let eAwA5 : Aw ≃* alternatingGroup (Fin 5) :=
    (Subgroup.equivMapOfInjective Aw eW.toMonoidHom eW.injective).trans
      (MulEquiv.subgroupCongr hAwImage)
  let eA : A ≃* alternatingGroup (Fin 5) := eAwA.symm.trans eAwA5
  have hCbot : Subgroup.centralizer (A : Set X) = ⊥ :=
    centralizer_commutator_eq_bot_of_image eW hN hNW hC hAwA hAwImage
  have hXle : Nat.card X ≤ 120 := by
    have h := @CFSG.Quasithin.H13.S126P31.card_le_mul_centralizer_alt5 X _ _ A hAn eA
    rw [hCbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hXleW : Nat.card X ≤ Nat.card W := by
    rw [hWcard]
    exact hXle
  exact Subgroup.eq_top_of_le_card W hXleW

theorem nonempty_mulEquiv_perm_five {X : Type} [Group X] [Finite X] {W N : Subgroup X}
    (eW : ↥W ≃* Equiv.Perm (Fin 5)) (hN : N.Normal) (hNW : N ≤ W)
    (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    Nonempty (X ≃* Equiv.Perm (Fin 5)) := by
  have hW := eq_top_of_mulEquiv_perm_five eW hN hNW hC
  exact ⟨Subgroup.topEquiv.symm.trans (hW ▸ eW)⟩

end CFSG.GroupTheory
