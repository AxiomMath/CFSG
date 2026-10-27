module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Desc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5_comp_kind03_false (hM : Asc82Tab6M) (hL : IsOm6Z2 L) {s : G} (hs2 : orderOf s = 2)
    (hs : s ∈ normalizer (L : Set G)) (hk : Kind5 L s 0 ∨ Kind5 L s 3) {J : Subgroup G}
    (hJ : IsComponentIn J (L ⊓ centralizer ({s} : Set G))) (h29 : IsL29 J) : False := by
  obtain ⟨t, ht, ht2⟩ := t5_exists_central_involution hL
  have hnc : s ∉ centralizer (L : Set G) := by
    rcases hk with hk | hk
    · exact t5_kind5_ne_central hL hs2 hs (by norm_num) hk
    · exact t5_kind5_ne_central hL hs2 hs (by norm_num) hk
  have hkM : InducesTypeSome (DescL L t) (descElt L t s hs) 6 (-1) 4 1 ∨
      ∃ α : ℤˣ, InducesTypeSome (DescL L t) (descElt L t s hs) 6 (-1) 3 α := by
    rcases hk with hk | hk
    · exact Or.inl ((t5_desc_kind_iff hM hL ht ht2 hs hs2 hnc (by norm_num)).mp hk)
    · exact Or.inr ((t5_desc_kind_iff hM hL ht ht2 hs hs2 hnc (by norm_num)).mp hk)
  have hbot' : layerCent (DescL L t) (descElt L t s hs) = ⊥ :=
    (hM.layer_trivial (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2) (descElt L t s hs)
      (t5_desc_orderOf hL ht ht2 hs hs2 hnc) (t5_desc_mem_normalizer L t hs)).mpr hkM
  have hbot : layerCent L s = ⊥ := (t5_desc_layerCent_bot_iff hL ht ht2 hs).mp hbot'
  have hJle : J ≤ layerCent L s := t5_component_le_layerCent hJ
  rw [hbot] at hJle
  exact ff_isL29_ne_bot h29 (le_bot_iff.mp hJle)

theorem t5_comp_kind2_false (hM : Asc82Tab6M) (hL : IsOm6Z2 L) {s : G} (hs2 : orderOf s = 2)
    (hs : s ∈ normalizer (L : Set G)) (hk : Kind5 L s 2) {J : Subgroup G}
    (hJ : IsComponentIn J (L ⊓ centralizer ({s} : Set G))) (h29 : IsL29 J) : False := by
  obtain ⟨t, ht, ht2⟩ := t5_exists_central_involution hL
  have hnc : s ∉ centralizer (L : Set G) := t5_kind5_ne_central hL hs2 hs (by norm_num) hk
  have hkM : ∃ α : ℤˣ, InducesTypeSome (DescL L t) (descElt L t s hs) 6 (-1) 1 α :=
    (t5_desc_kind_iff hM hL ht ht2 hs hs2 hnc (by norm_num)).mp hk
  have hOm5 : IsOmega5 (layerCent (DescL L t) (descElt L t s hs)) :=
    hM.layer_i1 (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2) (descElt L t s hs)
      (t5_desc_orderOf hL ht ht2 hs hs2 hnc) (t5_desc_mem_normalizer L t hs) hkM
  rw [t5_desc_layerCent hL ht ht2 hs] at hOm5
  obtain ⟨hX, h16⟩ := t5_isOmega5_simple hOm5
  obtain ⟨hJle, hJnorm, hcard⟩ := t5_component_subgroupOf_normalizer hs hJ
  obtain ⟨h8, h16'⟩ := t5_isL29_card_two_adic h29
  have hker : Nat.card (descMk L t).ker ∣ 2 := by
    have h1 : Nat.card (descMk L t).ker ∣ Nat.card (Subgroup.zpowers (descT L ht)) :=
      Subgroup.card_dvd_of_le (descMk_ker_le_zpowers hL ht ht2)
    have h2 : Nat.card (Subgroup.zpowers (descT L ht)) ∣ 2 := by
      rw [Nat.card_zpowers]
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      exact descT_mul_self ht ht2
    exact h1.trans h2
  exact t5_comp_false_of_simple_image (descMk L t) hker hJle hJnorm hX h16
    (by rw [hcard]; exact h8) (by rw [hcard]; exact h16')

end CFSG.OddStandard.SmallF3.Omega
