module

public import CFSG.LargeExtraspecial.AS35COdd
public import CFSG.LargeExtraspecial.S10FourB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

theorem mem_Qa_of_commute {h e : G} (he : e ∈ S.QG) (hhe : h * e = e * h) : e ∈ S.Qa h := by
  rw [S.Qa_eq_map]
  refine ⟨e, he, ?_⟩
  change h * e * h⁻¹ = e
  rw [hhe, mul_inv_cancel_right]

theorem z_not_mem_Qa (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {h : G}
    (hne : h * S.z * h⁻¹ ≠ S.z) : S.z ∉ S.Qa h := by
  rw [S.Qa_eq_map]
  rintro ⟨u, hu, huz⟩
  change h * u * h⁻¹ = S.z at huz
  have hu' : u = h⁻¹ * S.z * h := by rw [← huz]; group
  have h1 : u = S.z := by
    have := hW h⁻¹ (by rw [inv_inv, ← hu']; exact hu)
    rwa [inv_inv, ← hu'] at this
  rw [h1] at huz
  exact hne huz

variable [Finite G]

theorem mul_self_eq_one_of_mem_Qa {h t : G} (hne : h * S.z * h⁻¹ ≠ S.z) (htQ : t ∈ S.QG)
    (hta : t ∈ S.Qa h) : t * t = 1 := by
  rw [S.Qa_eq_map] at hta
  obtain ⟨u, hu, hut⟩ := hta
  change h * u * h⁻¹ = t at hut
  rw [← pow_two]
  rcases S.sq_eq_one_or_z htQ with h2 | h2
  · exact h2
  · exfalso
    have ht2 : t ^ 2 = h * u ^ 2 * h⁻¹ := by rw [← hut, pow_two, pow_two]; group
    rcases S.sq_eq_one_or_z hu with hu2 | hu2
    · rw [hu2] at ht2
      apply S.z_ne_one
      rw [← h2, ht2]
      group
    · rw [hu2, h2] at ht2
      exact hne ht2.symm

theorem aschbacherHyp_of_smith
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (h63 : ∀ h t : G, h * S.z * h⁻¹ ∈ S.M → h * S.z * h⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa h →
      t ≠ 1 → S.ZInOTwo t)
    (h64 : ∃ h : G, h * S.z * h⁻¹ ∈ S.M ∧ h * S.z * h⁻¹ ≠ S.z ∧
      4 ≤ Nat.card ↥(S.QG ⊓ S.Qa h)) :
    S.AschbacherHyp := by
  intro e he he1
  have hzX : S.z ∈ centralizer ({e} : Set G) :=
    mem_centralizer_singleton_iff.mpr (S.z_comm_QG he).symm
  let zX : centralizer ({e} : Set G) := ⟨S.z, hzX⟩
  by_cases hiso : ∀ g : centralizer ({e} : Set G),
      g * zX * g⁻¹ * zX = zX * (g * zX * g⁻¹) → g * zX * g⁻¹ = zX
  ·
    have hz1 : zX ≠ 1 := fun h => S.z_ne_one (congrArg Subtype.val h)
    have hz2 : zX * zX = 1 := Subtype.ext S.z_mul_z
    obtain ⟨NX, hNXn, hNXodd, hNX⟩ := S10.exists_odd_normal_of_isolated zX hz1 hz2 hiso
    have hNC : NX.map (centralizer ({e} : Set G)).subtype ≤ centralizer ({e} : Set G) :=
      map_subtype_le NX
    have hNn : ∀ c ∈ centralizer ({e} : Set G), ∀ k ∈ NX.map (centralizer ({e} : Set G)).subtype,
        c * k * c⁻¹ ∈ NX.map (centralizer ({e} : Set G)).subtype := by
      rintro c hc _ ⟨k, hk, rfl⟩
      exact ⟨⟨c, hc⟩ * k * ⟨c, hc⟩⁻¹, hNXn.conj_mem k hk ⟨c, hc⟩, rfl⟩
    have hodd : Odd (Nat.card (NX.map (centralizer ({e} : Set G)).subtype)) := by
      rw [card_map_of_injective (centralizer ({e} : Set G)).subtype_injective]
      exact hNXodd
    obtain ⟨h, hhM, hhne, hcard⟩ := h64
    obtain ⟨t, htA, ht1, hte⟩ := S.exists_commute_of_four_le inf_le_left hcard he
    obtain ⟨htQ, hta⟩ := mem_inf.mp htA
    have htz : t ≠ S.z := fun h' => S.z_not_mem_Qa hW hhne (h' ▸ hta)
    have ht2 : t * t = 1 := S.mul_self_eq_one_of_mem_Qa hhne htQ hta
    have hZt : S.ZInOTwo t := h63 h t hhM hhne htQ hta ht1
    obtain ⟨q, hqQ, hqt⟩ := S.exists_conj_eq_mul_z htQ ht1 htz
    have hqM : q ∈ S.M := S.QG_le_M hqQ
    have hconj : q * h * S.z * (q * h)⁻¹ = q * (h * S.z * h⁻¹) * q⁻¹ := by group
    have hZtz : S.ZInOTwo (t * S.z) := by
      refine h63 (q * h) (t * S.z) ?_ ?_ (mul_mem htQ S.z_mem_QG) ?_ ?_
      · rw [hconj]
        exact mul_mem (mul_mem hqM hhM) (inv_mem hqM)
      · intro hcontra
        apply hhne
        rw [hconj] at hcontra
        calc h * S.z * h⁻¹ = q⁻¹ * (q * (h * S.z * h⁻¹) * q⁻¹) * q := by group
          _ = q⁻¹ * (S.z * q) := by rw [hcontra, mul_assoc]
          _ = S.z := by rw [← S.z_comm hqM, inv_mul_cancel_left]
      · rw [S.Qa_eq_map] at hta ⊢
        obtain ⟨u, hu, hut⟩ := hta
        change h * u * h⁻¹ = t at hut
        refine ⟨u, hu, ?_⟩
        change q * h * u * (q * h)⁻¹ = t * S.z
        rw [← hqt, ← hut]
        group
      · intro h1
        apply htz
        calc t = t * S.z * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
          _ = S.z := by rw [h1, one_mul]
    have hNbot := S.eq_bot_of_odd he hNC hNn hodd hte ht2 hZt hZtz
    have hcen : ∀ c ∈ centralizer ({e} : Set G), c * S.z = S.z * c := by
      intro c hc
      have hmem : c * S.z * c⁻¹ * S.z⁻¹ ∈ NX.map (centralizer ({e} : Set G)).subtype :=
        ⟨⟨c, hc⟩ * zX * ⟨c, hc⟩⁻¹ * zX⁻¹, hNX ⟨c, hc⟩, rfl⟩
      rw [hNbot, mem_bot] at hmem
      calc c * S.z = c * S.z * c⁻¹ * S.z⁻¹ * (S.z * c) := by group
        _ = S.z * c := by rw [hmem, one_mul]
    refine S.zInOTwo_of_le (P := zpowers S.z) (zpowers_le.mpr hzX) ?_
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.orderOf_z, pow_one]))
      (mem_zpowers _)
    intro c hc p hp
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hp
    have hcm : c * S.z ^ m = S.z ^ m * c := (Commute.zpow_right (hcen c hc) m).eq
    exact mem_zpowers_iff.mpr ⟨m, by rw [hcm, mul_inv_cancel_right]⟩
  ·
    push Not at hiso
    obtain ⟨g, hgc, hgne⟩ := hiso
    have hgc' : (g : G) * S.z * (g : G)⁻¹ * S.z = S.z * ((g : G) * S.z * (g : G)⁻¹) :=
      congrArg Subtype.val hgc
    have hgne' : (g : G) * S.z * (g : G)⁻¹ ≠ S.z := fun h' => hgne (Subtype.ext h')
    have hge : (g : G) * e = e * g := mem_centralizer_singleton_iff.mp g.2
    exact h63 g e (S.mem_M_iff.mpr hgc') hgne' he (S.mem_Qa_of_commute he hge) he1

end Setting

namespace S14

@[expose] def SmithSixThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 3 ≤ S.width →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
      ∀ h t : G, h * S.z * h⁻¹ ∈ S.M → h * S.z * h⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa h →
        t ≠ 1 → S.ZInOTwo t

@[expose] def SmithSixFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 3 ≤ S.width →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
      ∃ h : G, h * S.z * h⁻¹ ∈ S.M ∧ h * S.z * h⁻¹ ≠ S.z ∧ 4 ≤ Nat.card ↥(S.QG ⊓ S.Qa h)

@[expose] def SmithSixFiveStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 3 ≤ S.width →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) → S.AschbacherHyp

theorem smithSixFiveStmt_of (h63 : SmithSixThreeInput) (h64 : SmithSixFourInput) :
    SmithSixFiveStmt := by
  intro G _ _ _ S hn hW
  exact S.aschbacherHyp_of_smith hW (h63 G S hn hW) (h64 G S hn hW)

end S14

end CFSG.LargeExtraspecial
