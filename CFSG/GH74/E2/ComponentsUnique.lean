module

public import CFSG.GH74.E2.ComponentsBridge
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.E2.Action
public import CFSG.GH74.E2.FrattiniRank

public section

namespace CFSG.GH74.E2

open Subgroup

section Aux

variable {G : Type*} [Group G]

theorem mem_sup_of_commute {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have h := hcomm a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [hcomm a ha b hb, mul_inv_rev] }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  exact sup_le hAS hBS hx

theorem isPGroup_zpowers_two {t : G} (ht : orderOf t = 2) : IsPGroup 2 ↥(zpowers t) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)

theorem eq_one_or_eq_of_mem_zpowers {t x : G} (ht : orderOf t = 2) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h1 : t ^ k = t ^ (k % 2) := by
    have := zpow_mod_orderOf t k
    rw [ht] at this
    simpa using this.symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h1, h, zpow_zero]
  · right
    rw [h1, h, zpow_one]

end Aux

section Unique

variable {G : Type} [Group G] [Finite G]

theorem exists_two_subgroup (hD : K0Data) {K : Subgroup G} (hS : K0Shape ↥K) :
    ∃ A : Subgroup G, A ≤ K ∧ IsPGroup 2 ↥A ∧ (center ↥K = ⊥ → 2 ≤ Group.rank ↥A) ∧
      (center ↥K ≠ ⊥ → 3 ≤ Group.rank ↥A) := by
  have key : ∀ T : Subgroup ↥K, IsPGroup 2 ↥T →
      ∃ A : Subgroup G, A ≤ K ∧ IsPGroup 2 ↥A ∧ Group.rank ↥A = Group.rank ↥T := fun T hT =>
    ⟨T.map K.subtype, Subgroup.map_subtype_le T, hT.map K.subtype,
      (Group.rank_congr (T.equivMapOfInjective K.subtype K.subtype_injective)).symm⟩
  by_cases hZ : center ↥K = ⊥
  · obtain ⟨T, hT, hr⟩ := hD.sylow_rank_simple ↥K hS hZ
    obtain ⟨A, hAK, hA, hrA⟩ := key T hT
    exact ⟨A, hAK, hA, fun _ => hrA ▸ hr, fun h => absurd hZ h⟩
  · obtain ⟨T, hT, hr⟩ := hD.sylow_rank_cover ↥K hS hZ
    obtain ⟨A, hAK, hA, hrA⟩ := key T hT
    exact ⟨A, hAK, hA, fun h => absurd h hZ, fun _ => hrA ▸ hr⟩

theorem false_of_two_components (hH : Hyp G) (hD : K0Data) {t : G} (ht : orderOf t = 2)
    {K K' : Subgroup G} (hK : IsCompCen t K) (hK' : IsCompCen t K') (hS : K0Shape ↥K)
    (hS' : K0Shape ↥K') (hne : K ≠ K') : False := by
  have hcomm := isCompCen_commute hK hK' hne
  obtain ⟨A, hAK, hA, hrA2, hrA3⟩ := exists_two_subgroup hD hS
  obtain ⟨B, hBK', hB, hrB2, hrB3⟩ := exists_two_subgroup hD hS'
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    hcomm a (hAK ha) b (hBK' hb)
  have hgen := hH.gen4
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
      have hQC : A ⊔ B ≤ Cen t := sup_le (hAK.trans hK.1) (hBK'.trans hK'.1)
      have hcommQE : ∀ q ∈ A ⊔ B, ∀ e ∈ zpowers t, q * e = e * q := by
        intro q hq e he
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
        have hc : Commute t q := mem_Cen.1 (hQC hq)
        exact (Commute.zpow_left hc k).eq.symm
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
            have h3 : t * g.1 = g.1 * t := mem_Cen.1 (hK.1 g.2)
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
            have h3 : t * g.1 = g.1 * t := mem_Cen.1 (hK'.1 g.2)
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
          _ ≤ 2 := hD.center_card ↥K hS
      have := rank_le_one_of_card_le_two hcard
      have := hrA3 hZ
      have := hrB3 hZ'
      omega

end Unique

end CFSG.GH74.E2
