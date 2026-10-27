module

public import CFSG.GH74.GLS.Stage2.Final.L26.Main
public import CFSG.GH74.GLS.Stage2.Final.L26.M12Core
public import CFSG.GH74.GLS.Stage2.Final.M12Odd

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section M12

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem lemma26_of_m12 (hctx : Stage2Ctx G z Kind.m12 S) (h : Stage1M12 G z S) {t : G} (htS : t ∈ S)
    (htW : t ∉ WC z) (ht2 : orderOf t = 2) (htc : IsConj z t) : Lemma26 z S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWn, hWp, hC, -⟩ := m12_barFacts h
  obtain ⟨A, hA₃, -, -, hFst, hcomm, -⟩ := h.L_shape
  obtain ⟨hWn', ⟨e⟩⟩ := h.quot
  have hA3 : Nat.card ↥A = 3 := by
    rw [Nat.card_congr hA₃.some.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have htC : t ∈ Cen z := hctx.S_le_Cen htS
  obtain ⟨y, hy⟩ : ∃ y : CentralizerBar z, y = toBar z ⟨t, htC⟩ := ⟨_, rfl⟩
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul]
    have h1 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at this
    have : (⟨t, htC⟩ : ↥(Cen z)) * ⟨t, htC⟩ = 1 := Subtype.ext h1
    rw [this, map_one]
  have hyW : y ∉ WBar z := by
    intro hyW
    apply htW
    have hOn : (O22Res ↥(Cen z)).Normal := O22Res_normal
    rw [hy, WBar_eq_map_O22Res] at hyW
    have h2 := mem_of_twoElt_of_map_mem (toBar z) (O22Res ↥(Cen z)) (x := ⟨t, htC⟩)
      ⟨1, by rw [Subgroup.orderOf_mk, ht2]; norm_num⟩ (odd_card_ker_toBar z) hyW
    exact ⟨⟨t, htC⟩, h2, rfl⟩
  have : Group.IsNilpotent ↥(WBar z) := hWp.isNilpotent
  have hW2 : Group.IsSolvable ↥(WBar z) := inferInstance
  have hE : layer (CentralizerBar z) ≤ ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆ := by
    refine sSup_le fun J hJ => ?_
    exfalso
    have hJW : J ≤ WBar z :=
      hFst ▸ (le_sSup hJ : J ≤ layer (CentralizerBar z)).trans le_sup_right
    have : Group.IsPerfect ↥J := hJ.1.1
    have : Nontrivial ↥J := isQuasisimple_nontrivial hJ.1
    have hsolJ : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJW)
    exact Group.IsPerfect.not_isSolvable ↥J hsolJ
  have hcore := le_O2Of_commutator_of_perm3 hC e hA3 hcomm hy2 hyW
  subst hy
  refine lemma26_of_bar hctx htS htc hE ?_
  intro x hx hxS hxW
  have hw : toBar z ⟨x, hx⟩ ∈ WBar z := ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxW, rfl⟩
  exact hcore hw

end M12

section Final

theorem m12_data {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.m12 S) : Stage1M12 G z S := by
  have hd := hctx.data
  cases hd with
  | m12 h => exact h

theorem lemma26K_m12 : Lemma26K Kind.m12 := by
  intro G _ _ z S hctx
  have h := m12_data hctx
  obtain ⟨t, htS, htW, ht2, htc⟩ := h.fuse_out
  exact lemma26_of_m12 hctx h htS htW ht2 htc

end Final

end CFSG.GH74.GLS.Stage2.Final.L26
