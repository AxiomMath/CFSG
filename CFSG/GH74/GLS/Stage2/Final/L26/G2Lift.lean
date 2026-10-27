module

public import CFSG.GH74.GLS.Stage2.Final.L26.GLevel
public import CFSG.GH74.GLS.Stage2.Local.Lemma23

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section O2

variable {A B : Type} [Group A] [Group B]

theorem O2Of_map [Finite A] (g : A →* B) (A' : Subgroup A) : O2Of (A'.map g) = (O2Of A').map g := by
  have hs : Function.Surjective (g.subgroupMap A') := MonoidHom.subgroupMap_surjective g A'
  have h := CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual (g.subgroupMap A') hs
    (p := 2) Nat.prime_two
  unfold O2Of
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem O2Of_normal [Finite A] (A' : Subgroup A) [hA' : A'.Normal] : (O2Of A').Normal := by
  have hc : (oResidual 2 ↥A').Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    exact CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual φ.toMonoidHom φ.surjective
      (p := 2) Nat.prime_two
  exact ConjAct.normal_of_characteristic_of_normal (K := oResidual 2 ↥A')

omit [Group B] in
theorem mem_O2Of_of_odd {A' : Subgroup A} {n : A} (hn : n ∈ A') (ho : Nat.Coprime (orderOf n) 2) :
    n ∈ O2Of A' :=
  ⟨⟨n, hn⟩, Subgroup.subset_closure (by
    change Nat.Coprime (orderOf (⟨n, hn⟩ : ↥A')) 2
    rwa [Subgroup.orderOf_mk]), rfl⟩

end O2

section WBar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem WBar_eq_map_O22Res (z : G) : WBar z = (O22Res ↥(Cen z)).map (toBar z) := by
  unfold WBar barOf
  have h : (WC z).subgroupOf (Cen z) = O22Res ↥(Cen z) :=
    Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _
  rw [h]

omit [Finite G] in
theorem WBar_normal (z : G) : (WBar z).Normal := by
  rw [WBar_eq_map_O22Res]
  have := O22Res_normal (X := ↥(Cen z))
  exact Subgroup.Normal.map this (toBar z) (toBar_surjective z)

theorem WBar_two_pow (z : G) : ∀ w ∈ WBar z, ∃ a : ℕ, w ^ (2 ^ a) = 1 := by
  rw [WBar_eq_map_O22Res]
  rintro _ ⟨w', hw', rfl⟩
  obtain ⟨a, ha⟩ := exists_pow_mem_pPrimeCore_of_mem_O22Res hw'
  refine ⟨a, ?_⟩
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ha

theorem WBar_le_generalizedFitting (z : G) : WBar z ≤ generalizedFitting (CentralizerBar z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWn : (WBar z).Normal := WBar_normal z
  have hWp : IsPGroup 2 ↥(WBar z) := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha⟩ := WBar_two_pow z w hw
    exact ⟨a, Subtype.ext ha⟩
  have hle : WBar z ≤ pCore 2 (CentralizerBar z) := le_sSup ⟨hWn, hWp⟩
  exact (pCore_le_fitting (CentralizerBar z) 2).trans le_sup_left |> fun h => hle.trans h

end WBar

section WrapUp

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem lemma26_of_bar (hctx : Stage2Ctx G z k S) {t : G} (htS : t ∈ S) (htc : IsConj z t)
    (hE : layer (CentralizerBar z) ≤
      ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers (toBar z ⟨t, hctx.S_le_Cen htS⟩)⁆)
    (hW : ∀ (x : G) (hx : x ∈ Cen z), x ∈ S → x ∈ WC z →
      toBar z ⟨x, hx⟩ ∈ O2Of ⁅(⊤ : Subgroup (CentralizerBar z)),
        Subgroup.zpowers (toBar z ⟨t, hctx.S_le_Cen htS⟩)⁆) :
    Lemma26 z S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC : t ∈ Cen z := hctx.S_le_Cen htS
  have hmapG : (⁅(⊤ : Subgroup ↥(Cen z)), Subgroup.zpowers (⟨t, htC⟩ : ↥(Cen z))⁆).map (Cen z).subtype =
      ⁅Cen z, Subgroup.zpowers t⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_zpowers]
    rfl
  have hLz := pLayer_le_commutator_of_bar (⟨t, htC⟩ : ↥(Cen z)) hE
  have hLG : pLayerOf 2 (Cen z) ≤ ⁅Cen z, Subgroup.zpowers t⁆ := by
    rw [pLayerOf_eq_map, ← hmapG]
    exact Subgroup.map_mono hLz
  have hperf : Group.IsPerfect ↥(pLayerOf 2 (Cen z)) := by
    rw [pLayerOf_eq_map]
    have : Group.IsPerfect ↥(pLayer ↥(Cen z) 2) :=
      Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect _)
    exact Group.IsPerfect.map _
  have hOle : pLayerOf 2 (Cen z) ≤ O2Of ⁅Cen z, Subgroup.zpowers t⁆ := le_O2Of_of_perfect hperf hLG
  have hB : S ⊓ WC z ≤ O2Of ⁅Cen z, Subgroup.zpowers t⁆ := by
    rintro x ⟨hxS, hxW⟩
    have hxC : x ∈ Cen z := hctx.S_le_Cen hxS
    obtain ⟨K', hK'⟩ : ∃ K' : Subgroup ↥(Cen z),
        K' = ⁅(⊤ : Subgroup ↥(Cen z)), Subgroup.zpowers (⟨t, htC⟩ : ↥(Cen z))⁆ := ⟨_, rfl⟩
    have hK'n : K'.Normal := by
      rw [hK']
      exact commutator_top_normal _
    have hmapB : K'.map (toBar z) =
        ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers (toBar z ⟨t, htC⟩)⁆ := by
      rw [hK', Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective _ (toBar_surjective z), MonoidHom.map_zpowers]
    have hmapG' : K'.map (Cen z).subtype = ⁅Cen z, Subgroup.zpowers t⁆ := by rw [hK']; exact hmapG
    have h1 : toBar z ⟨x, hxC⟩ ∈ (O2Of K').map (toBar z) := by
      rw [← O2Of_map, hmapB]
      exact hW x hxC hxS hxW
    have hN : (O2Of K').Normal := O2Of_normal K'
    have hx2 : ∃ a : ℕ, orderOf (⟨x, hxC⟩ : ↥(Cen z)) = 2 ^ a := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_mem_S hctx hxS
    have h2 : (⟨x, hxC⟩ : ↥(Cen z)) ∈ O2Of K' :=
      mem_of_twoElt_of_map_mem (toBar z) (O2Of K') hx2 (odd_card_ker_toBar z) h1
    have h3 : x ∈ (O2Of K').map (Cen z).subtype := ⟨_, h2, rfl⟩
    rw [← O2Of_map, hmapG'] at h3
    exact h3
  have hH : O2Of ⁅Cen z, Subgroup.zpowers t⁆ ≤
      ⨆ (t : G) (_ : t ∈ S) (_ : IsConj z t), O2Of ⁅Cen z, Subgroup.zpowers t⁆ :=
    le_iSup_of_le t (le_iSup_of_le htS (le_iSup_of_le htc le_rfl))
  exact sup_le (hOle.trans hH) (hB.trans hH)

end WrapUp

end CFSG.GH74.GLS.Stage2.Final.L26
