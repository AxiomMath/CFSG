module

public import CFSG.GH74.GLS.Prop27.Defs
public import CFSG.GH74.E2.ComponentsUnique

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG.GH74.E2

theorem Shapes7.card_center_le_two {K : Type} [Group K] (h : Shapes7 K) :
    Nat.card (center K) ≤ 2 := by
  rcases h with ⟨hZ, -⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩
  · rw [hZ, Subgroup.card_bot]
    norm_num
  · exact h2.le
  · exact h2.le

theorem exists_two_subgroup7 (hTab : Prop27TableFacts) {Y : Type} [Group Y] [Finite Y]
    {K : Subgroup Y} (hS : Shapes7 ↥K) :
    ∃ A : Subgroup Y, A ≤ K ∧ IsPGroup 2 ↥A ∧ (center ↥K = ⊥ → 2 ≤ Group.rank ↥A) ∧
      (center ↥K ≠ ⊥ → 3 ≤ Group.rank ↥A) := by
  have key : ∀ T : Subgroup ↥K, IsPGroup 2 ↥T →
      ∃ A : Subgroup Y, A ≤ K ∧ IsPGroup 2 ↥A ∧ Group.rank ↥A = Group.rank ↥T := fun T hT =>
    ⟨T.map K.subtype, Subgroup.map_subtype_le T, hT.map K.subtype,
      (Group.rank_congr (T.equivMapOfInjective K.subtype K.subtype_injective)).symm⟩
  by_cases hZ : center ↥K = ⊥
  · obtain ⟨T, hT, hr⟩ := hTab.sylow_rank_simple ↥K hS hZ
    obtain ⟨A, hAK, hA, hrA⟩ := key T hT
    exact ⟨A, hAK, hA, fun _ => hrA ▸ hr, fun h => absurd hZ h⟩
  · obtain ⟨T, hT, hr⟩ := hTab.sylow_rank_cover ↥K hS hZ
    obtain ⟨A, hAK, hA, hrA⟩ := key T hT
    exact ⟨A, hAK, hA, fun h => absurd h hZ, fun _ => hrA ▸ hr⟩

theorem commute_of_distinct_components {Y : Type} [Group Y] [Finite Y] {K K' : Subgroup Y}
    (hK : IsComponent K) (hK' : IsComponent K') (hne : K ≠ K') :
    ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
  intro k hk k' hk'
  rcases CFSG.LocalCores.distinct_components_commute hK hK' with h | h
  · exact absurd h hne
  · exact (Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hk) k' hk').symm

theorem false_of_two_components7 (hT : Prop27TableFacts) {Y : Type} [Group Y] [Finite Y]
    (hgen : Gen4 Y) {t : Y} (ht : orderOf t = 2) (htc : ∀ y : Y, y * t = t * y)
    {K K' : Subgroup Y} (hK : IsComponent K) (hK' : IsComponent K') (hne : K ≠ K')
    (hS : Shapes7 ↥K) (hS' : Shapes7 ↥K') : False := by
  have hcomm := commute_of_distinct_components hK hK' hne
  obtain ⟨A, hAK, hA, hrA2, hrA3⟩ := exists_two_subgroup7 hT hS
  obtain ⟨B, hBK', hB, hrB2, hrB3⟩ := exists_two_subgroup7 hT hS'
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    hcomm a (hAK ha) b (hBK' hb)
  have h1 := gen4_rank_add_le hgen A B hA hB hcommAB
  have hZK : A ⊓ B ≤ (center ↥K).map K.subtype := by
    rintro x ⟨hxA, hxB⟩
    have hxK := hAK hxA
    have hxK' := hBK' hxB
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g.1 g.2 x hxK')
  have hZK' : A ⊓ B ≤ (center ↥K').map K'.subtype := by
    rintro x ⟨hxA, hxB⟩
    have hxK := hAK hxA
    have hxK' := hBK' hxB
    refine ⟨⟨x, hxK'⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm x hxK g.1 g.2).symm
  by_cases hZ : center ↥K = ⊥
  · have hbot : A ⊓ B = ⊥ := by
      refine le_bot_iff.1 (hZK.trans ?_)
      rw [hZ, Subgroup.map_bot]
    have hr0 : Group.rank ↥(A ⊓ B) = 0 := by
      rw [Subgroup.rank_congr hbot]
      exact Group.rank_eq_zero _
    rw [hr0] at h1
    by_cases hZ' : center ↥K' = ⊥
    ·
      have h2 := rank_sup_add_inf_ge A B hA hB hcommAB
      rw [hr0] at h2
      have hQ : IsPGroup 2 ↥(A ⊔ B) := isPGroup_sup_of_commute A B hA hB hcommAB
      have hE : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_two ht
      have hcommQE : ∀ q ∈ A ⊔ B, ∀ e ∈ zpowers t, q * e = e * q := by
        intro q _ e he
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
        exact (Commute.zpow_right (htc q) k).eq
      have htQ : t ∉ A ⊔ B := by
        intro htm
        obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcommAB htm
        have haK := hAK ha
        have hbK' := hBK' hb
        have ha1 : a = 1 := by
          have hc : (⟨a, haK⟩ : ↥K) ∈ center ↥K := by
            rw [Subgroup.mem_center_iff]
            intro g
            apply Subtype.ext
            have h3 : t * g.1 = g.1 * t := (htc g.1).symm
            have h4 : g.1 * b = b * g.1 := hcomm g.1 g.2 b hbK'
            show g.1 * a = a * g.1
            rw [hab] at h3
            have h5 : a * g.1 * b = g.1 * a * b := by
              calc a * g.1 * b = a * (g.1 * b) := by group
                _ = a * (b * g.1) := by rw [h4]
                _ = a * b * g.1 := by group
                _ = g.1 * (a * b) := h3
                _ = g.1 * a * b := by group
            exact (mul_right_cancel h5).symm
          rw [hZ, Subgroup.mem_bot] at hc
          exact congrArg Subtype.val hc
        have hb1 : b = 1 := by
          have hc : (⟨b, hbK'⟩ : ↥K') ∈ center ↥K' := by
            rw [Subgroup.mem_center_iff]
            intro g
            apply Subtype.ext
            have h3 : t * g.1 = g.1 * t := (htc g.1).symm
            have h4 : a * g.1 = g.1 * a := hcomm a haK g.1 g.2
            show g.1 * b = b * g.1
            rw [hab] at h3
            have h5 : a * (b * g.1) = a * (g.1 * b) := by
              calc a * (b * g.1) = a * b * g.1 := by group
                _ = g.1 * (a * b) := h3
                _ = (g.1 * a) * b := by group
                _ = (a * g.1) * b := by rw [h4]
                _ = a * (g.1 * b) := by group
            exact (mul_left_cancel h5).symm
          rw [hZ', Subgroup.mem_bot] at hc
          exact congrArg Subtype.val hc
        rw [ha1, hb1, one_mul] at hab
        rw [hab, orderOf_one] at ht
        omega
      have hinf : (A ⊔ B) ⊓ zpowers t = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hxQ, hxE⟩
        rcases eq_one_or_eq_of_mem_zpowers ht hxE with h | h
        · exact h ▸ Subgroup.one_mem _
        · exact absurd (h ▸ hxQ) htQ
      have h3 := gen4_rank_add_le hgen (A ⊔ B) (zpowers t) hQ hE hcommQE
      have hr0' : Group.rank ↥((A ⊔ B) ⊓ zpowers t) = 0 := by
        rw [Subgroup.rank_congr hinf]
        exact Group.rank_eq_zero _
      rw [hr0'] at h3
      have hnt : Nontrivial ↥(zpowers t) := by
        rw [Subgroup.nontrivial_iff_ne_bot, Ne, Subgroup.zpowers_eq_bot]
        intro h
        rw [h, orderOf_one] at ht
        omega
      have hr1 : 0 < Group.rank ↥(zpowers t) := Group.rank_pos _
      have := hrA2 hZ
      have := hrB2 hZ'
      omega
    · have := hrB3 hZ'
      have := hrA2 hZ
      omega
  · by_cases hZ' : center ↥K' = ⊥
    · have hbot : A ⊓ B = ⊥ := by
        refine le_bot_iff.1 (hZK'.trans ?_)
        rw [hZ', Subgroup.map_bot]
      have hr0 : Group.rank ↥(A ⊓ B) = 0 := by
        rw [Subgroup.rank_congr hbot]
        exact Group.rank_eq_zero _
      rw [hr0] at h1
      have := hrA3 hZ
      have := hrB2 hZ'
      omega
    · have hcard : Nat.card ↥(A ⊓ B) ≤ 2 := by
        calc Nat.card ↥(A ⊓ B) ≤ Nat.card ↥((center ↥K).map K.subtype) :=
              Subgroup.card_le_of_le hZK
          _ = Nat.card ↥(center ↥K) :=
              Subgroup.card_map_of_injective K.subtype_injective
          _ ≤ 2 := hS.card_center_le_two
      have := rank_le_one_of_card_le_two hcard
      have := hrA3 hZ
      have := hrB3 hZ'
      omega

end CFSG.GH74.GLS.Prop27
