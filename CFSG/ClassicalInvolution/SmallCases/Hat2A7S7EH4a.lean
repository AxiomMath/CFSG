module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM00
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerDich

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7E

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7S8.Asc77.T8
open CFSG.ClassicalInvolution.Asc77.T8 (XMem layerRes layerSet layerJoin cenZ cenZ_eq_centralizer
  mem_cenZ_iff layerRes_conj layerRes_le layerRes_le_cenZ layerSet_le_cenZ layerJoin_le_cenZ
  le_layerJoin)
open scoped commutatorElement


section Cls

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem HM.cls (hΩ : HM Ω) : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u := fun L hL => by
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  exact ⟨z, hz.to2A7⟩

end Cls

namespace Asc77

section Transfer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G}

theorem exists_of_mem_RSet_layerSet {R₀ : Subgroup G} (hR₀ : R₀ ∈ RSet (layerSet Ω w)) :
    ∃ J, XMem Ω w J ∧ IsSylow2In R₀ (layerRes w J) := by
  obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR₀
  obtain ⟨J, hJ, rfl⟩ := hM
  exact ⟨J, hJ, hRM⟩

theorem mem_RSet_of_mem_RSet_layerSet (hΩ : HM Ω) (hw2 : w * w = 1) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ RSet (layerSet Ω w)) : R₀ ∈ RSet Ω := by
  obtain ⟨J, hJ, hT⟩ := exists_of_mem_RSet_layerSet hR₀
  exact mem_RSet_of_isSylow2In hJ.1 (XMem.isSylow2In_of_layerRes hΩ.toGen hΩ.cls hw2 hJ hT)

theorem mem_USet_of_mem_USet_layerSet (hΩ : HM Ω) (hw2 : w * w = 1) {U : Subgroup G}
    (hU : U ∈ USet (layerSet Ω w)) : U ∈ USet Ω := by
  obtain ⟨R₀, hR₀, hUR, hcyc, hidx⟩ := hU
  exact ⟨R₀, mem_RSet_of_mem_RSet_layerSet hΩ hw2 hR₀, hUR, hcyc, hidx⟩

theorem isUniqueInvolution_of_layerRes (hΩ : HM Ω) (hw2 : w * w = 1) {J : Subgroup G}
    (hJ : XMem Ω w J) {z : G} (hz : IsUniqueInvolution (layerRes w J) z) :
    IsUniqueInvolution J z :=
  XMem.isUniqueInvolution_of_layerRes hΩ.toGen hΩ.cls hw2 hJ hz

theorem isUniqueInvolution_layerRes (hΩ : HM Ω) (hw2 : w * w = 1) {J : Subgroup G}
    (hJ : XMem Ω w J) {z : G} (hz : IsUniqueInvolution J z) :
    IsUniqueInvolution (layerRes w J) z :=
  XMem.isUniqueInvolution_layerRes hΩ.toGen hΩ.cls hw2 hJ hz

theorem mem_twinSet_of_layerRes (hΩ : HM Ω) (hw2 : w * w = 1) {K L : Subgroup G}
    (hK : XMem Ω w K) (hL : XMem Ω w L)
    (h : layerRes w L ∈ twinSet (layerSet Ω w) (layerRes w K)) : L ∈ twinSet Ω K := by
  obtain ⟨-, z, hzK, hzL⟩ := h
  exact ⟨hL.1, z, isUniqueInvolution_of_layerRes hΩ hw2 hK hzK,
    isUniqueInvolution_of_layerRes hΩ hw2 hL hzL⟩

theorem layerRes_mem_twinSet (hΩ : HM Ω) (hw2 : w * w = 1) {K L : Subgroup G}
    (hK : XMem Ω w K) (hL : XMem Ω w L) (h : L ∈ twinSet Ω K) :
    layerRes w L ∈ twinSet (layerSet Ω w) (layerRes w K) := by
  obtain ⟨-, z, hzK, hzL⟩ := h
  exact ⟨⟨L, hL, rfl⟩, z, isUniqueInvolution_layerRes hΩ hw2 hK hzK,
    isUniqueInvolution_layerRes hΩ hw2 hL hzL⟩

theorem mem_omegaNbr_of_layerSet (hΩ' : HM Ω) (hw2 : w * w = 1) {K J : Subgroup G}
    (hK : XMem Ω w K) (hJ : XMem Ω w J)
    (h : layerRes w J ∈ omegaNbr (layerSet Ω w) (layerRes w K)) : J ∈ omegaNbr Ω K := by
  have hΩ := hΩ'.toGen
  obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  obtain ⟨J', hJ', hTfix⟩ := exists_of_mem_RSet_layerSet hT
  have hTJ' : IsSylow2In T J' := XMem.isSylow2In_of_layerRes hΩ hΩ'.cls hw2 hJ' hTfix
  have h8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ'.1 hTJ')
  have hTJG : T ≤ J := hTJ.trans (layerRes_le w J)
  have hJJ' : J = J' := Sec6Gen.eq_of_le_of_le hΩ hJ.1 hJ'.1 hTJ'.2.1 (by omega) hTJG hTJ'.1
  subst hJJ'
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK.1
  have hzA := isUniqueInvolution_layerRes hΩ' hw2 hK hz
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have hTN' : T ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK.1 hJ.1 (Ne.symm hJK) hz hTJG hTJ'.2.1
      (by omega) hTc
  exact ⟨hJ.1, hJK, T, mem_RSet_of_isSylow2In hJ.1 hTJ', hTJG, hTN'⟩

theorem mem_omegaStarNbr_of_layerSet (hΩ' : HM Ω) (hw2 : w * w = 1) {K J : Subgroup G}
    (hK : XMem Ω w K) (hJ : XMem Ω w J)
    (h : layerRes w J ∈ omegaStarNbr (layerSet Ω w) (layerRes w K)) :
    J ∈ omegaStarNbr Ω K := by
  have hΩ := hΩ'.toGen
  obtain ⟨-, hne, U, hU, hUJ, hUN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  have hUΩ : U ∈ USet Ω := mem_USet_of_mem_USet_layerSet hΩ' hw2 hU
  obtain ⟨R₀, hR₀, J', hJ', hR₀J', hUR₀, hcyc, hcard, h4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hΩ hUΩ
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hUΩ
  have hUJG : U ≤ J := hUJ.trans (layerRes_le w J)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK.1
  have hzA := isUniqueInvolution_layerRes hΩ' hw2 hK hz
  have hUc : U ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hUN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have hUN' : U ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK.1 hJ.1 (Ne.symm hJK) hz hUJG hU2 (by omega) hUc
  exact ⟨hJ.1, hJK, U, hUΩ, hUJG, hUN'⟩

theorem dstarAdj_of_layerSet (hΩ : HM Ω) (hw2 : w * w = 1) {K J : Subgroup G}
    (hK : XMem Ω w K) (hJ : XMem Ω w J)
    (h : dstarAdj (layerSet Ω w) (layerRes w K) (layerRes w J)) : dstarAdj Ω K J := by
  rcases h.2 with h1 | h1
  · exact ⟨hJ.1, Or.inl (mem_omegaStarNbr_of_layerSet hΩ hw2 hK hJ h1)⟩
  · exact ⟨hJ.1, Or.inr (mem_omegaStarNbr_of_layerSet hΩ hw2 hJ hK h1)⟩

theorem eq_of_layerRes_eq (hΩ : HM Ω) (hw2 : w * w = 1) {J L : Subgroup G} (hJ : XMem Ω w J)
    (hL : XMem Ω w L) (h : layerRes w J = layerRes w L) : J = L :=
  XMem.eq_of_layerRes_eq hΩ.toGen hΩ.cls hw2 hJ hL h

theorem mem_dstarComp_of_dstarComp_layerSet (hΩ : HM Ω) (hw2 : w * w = 1) {K : Subgroup G}
    (hK : XMem Ω w K) {L : Subgroup G} (hL : L ∈ dstarComp (layerSet Ω w) (layerRes w K)) :
    ∀ M, XMem Ω w M → layerRes w M = L → M ∈ dstarComp Ω K := by
  induction hL with
  | refl =>
    intro M hM hMK
    rw [eq_of_layerRes_eq hΩ hw2 hM hK hMK]
    exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    rename_i b d
    intro M hM hMd
    have hbΛ : b ∈ layerSet Ω w := by
      rcases dstarComp_subset_insert _ hab with h | h
      · rw [h]
        exact ⟨K, hK, rfl⟩
      · exact h
    obtain ⟨M₀, hM₀, rfl⟩ := hbΛ
    have h1 := ih M₀ hM₀ rfl
    rw [← hMd] at hbc
    exact h1.tail (dstarAdj_of_layerSet hΩ hw2 hM₀ hM hbc)

theorem le_normalizer_layerJoin (hΩ : HM Ω) :
    Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (layerJoin Ω w : Set G) := by
  intro x hx
  exact mem_normalizer_iff_conjSub_eq.mpr
    (layerJoin_conjSub_eq hΩ.toGen (by rwa [cenZ_eq_centralizer]))

end Transfer

end Asc77

end CFSG.ClassicalInvolution.Hat2A7E
