module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXCaseOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXWreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputSecond
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LocalSettingOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardQuotient

public section

namespace CFSG.EvenSporadicStandard.M24Std.GenX

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def FirstHalfProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), LocalSetting G L z → CaseTwo L z →
    ∃ A B C D : Subgroup G, FirstHalfData L z A B C D

theorem hom_apply_eq_one_of_forall {X : Type} [Group X] {z : X}
    (hE : ¬ ∃ E : Subgroup X, E.Normal ∧ E.index = 2 ∧ z ∉ E) (ψ : X →* ℤˣ) : ψ z = 1 := by
  by_contra hψ
  apply hE
  refine ⟨ψ.ker, inferInstance, ?_, fun hzk => hψ (MonoidHom.mem_ker.1 hzk)⟩
  have hsurj : Function.Surjective ψ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one ψ⟩
    · exact ⟨z, (Int.units_eq_one_or (ψ z)).resolve_left hψ⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, card_units_int]

theorem fusionZStar_eq_bot_of {Y : Type} [Group Y] (hO : fusionOddCore Y = ⊥)
    (hZ : ∀ y : Y, (∀ g : Y, g * y = y * g) → y = 1) : fusionZStar Y = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  rw [mem_bot]
  refine hZ y fun g => ?_
  have h1 : QuotientGroup.mk' (fusionOddCore Y) y ∈ center (Y ⧸ fusionOddCore Y) := hy
  rw [mem_center_iff] at h1
  have h2 := h1 (QuotientGroup.mk' (fusionOddCore Y) g)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, hO, mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem isSimpleGroup_and_not_comm_of_M24
    {Y : Type} [Group Y] (hY : IsSporadic Y .M24) :
    IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* NativeSporadic.M24 := e
  have : IsSimpleGroup NativeSporadic.M24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
  refine ⟨e'.isSimpleGroup, ?_⟩
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  have hZ := center_eq_bot_of_isSporadic_M24 ⟨e⟩
  have htop : center Y = ⊤ := eq_top_iff.2 fun a _ => mem_center_iff.2 fun g => h g a
  rw [hZ] at htop
  have hc : Nat.card Y = 244823040 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  have : Nat.card (⊥ : Subgroup Y) = Nat.card (⊤ : Subgroup Y) := by rw [htop]
  rw [card_bot, card_top, hc] at this
  exact absurd this (by norm_num)

theorem section_of_secondHalf
    (hFH : FirstHalfProp) (hHS : HarrisSolomonZ2S6IsoK) (h2 : Ega81Lemmas214to217)
    (hA : Ega81HypAZ2A8K) (X : Type) [Group X] [Finite X] (hKX : CFSG.SectionRank.IsKGroupCat X)
    (z : X) (K : Subgroup X)
    (hzz : z * z = 1) (hz1 : z ≠ 1) (hK : IsSporadic K .M24) (hKz : ∀ k ∈ K, k * z = z * k)
    (hC : ∀ x : X, x * z = z * x → ∃ k ∈ K, x = k ∨ x = k * z)
    (hnc : ∃ x : X, x * z * x⁻¹ ≠ z ∧ (x * z * x⁻¹) * z = z * (x * z * x⁻¹)) :
    ∃ E : Subgroup X, E.Normal ∧ E.index = 2 ∧ z ∉ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hE
  have hGz := hom_apply_eq_one_of_forall hE
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hzK : z ∈ centralizer (K : Set X) := mem_centralizer_iff.2 hKz
  have hCX : centralizer ({z} : Set X) = K ⊔ zpowers z := by
    refine le_antisymm (fun x hx => ?_) (sup_le (fun k hk => ?_) ?_)
    · obtain ⟨k, hk, rfl | rfl⟩ := hC x (mem_centralizer_singleton_iff.1 hx)
      · exact mem_sup_left hk
      · exact mul_mem (mem_sup_left hk) (mem_sup_right (mem_zpowers z))
    · exact mem_centralizer_singleton_iff.2 (hKz k hk)
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
  obtain ⟨hKs, hKnab⟩ := isSimpleGroup_and_not_comm_of_M24 hK
  obtain ⟨hO1, hstd, -, -, ⟨eK⟩, hCY⟩ :=
    standardQuotient_of_centralizer_eq hz2 hKs hKnab hCX hzK
  set O := fusionOddCore X with hOdef
  set π := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := odd_natCard_fusionOddCore X
  have hinvO : ∀ w ∈ O, w * w = 1 → w = 1 := by
    intro w hw hww
    by_contra hw1
    have h1 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
    have h3 : orderOf (⟨w, hw⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mk, h1] at h3
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h3)
  have hπz1 : π z ≠ 1 := by
    rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    intro hzO
    exact hz1 (hinvO z hzO hzz)
  have hπzz : π z * π z = 1 := by rw [← map_mul, hzz, map_one]
  have hzb2 : orderOf (π z) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hπzz) hπz1
  have hspY : IsSporadic (K.map π) .M24 := by
    obtain ⟨e⟩ := hK
    exact ⟨eK.trans e⟩
  have hcenK : zpowers (π z) ≤ centralizer ((K.map π : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
    refine zpowers_le.2 (mem_centralizer_iff.2 ?_)
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hKz k hk]
  have hZK : center (K.map π) = ⊥ := center_eq_bot_of_isSporadic_M24 hspY
  have hcentral : ∀ y ∈ K.map π, (∀ g ∈ K.map π, g * y = y * g) → y = 1 := by
    intro y hy hc
    have hyZ : (⟨y, hy⟩ : K.map π) ∈ center (K.map π) := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2)
    rw [hZK, mem_bot] at hyZ
    exact congrArg Subtype.val hyZ
  have hdisjY : Disjoint (K.map π) (zpowers (π z)) := by
    rw [disjoint_def]
    intro x hxK hxz
    rcases eq_one_or_eq_of_mul_self hπzz hxz with h | h
    · exact h
    · exfalso
      apply hπz1
      rw [h] at hxK
      exact hcentral _ hxK fun g hg => mem_centralizer_iff.1 (hcenK (mem_zpowers _)) g hg
  have hsY : LocalSetting (X ⧸ O) (K.map π) (π z) :=
    localSetting_of_centralizer_eq hzb2 hcenK hCY hdisjY hspY
  have hGzY : ∀ ψ : (X ⧸ O) →* ℤˣ, ψ (π z) = 1 := fun ψ => hGz (ψ.comp π)
  have hZY : fusionZStar (X ⧸ O) = ⊥ := by
    refine fusionZStar_eq_bot_of hO1 fun y hy => ?_
    have hyc : y ∈ centralizer ({π z} : Set (X ⧸ O)) :=
      mem_centralizer_singleton_iff.2 (hy (π z)).symm
    rw [hCY] at hyc
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcenK hyc
    have hbc : ∀ g ∈ K.map π, g * b = b * g := fun g hg => mem_centralizer_iff.1 (hcenK hb) g hg
    have ha1 : a = 1 := by
      refine hcentral a ha fun g hg => ?_
      have h1 := hy g
      have h3 : g * a * b = a * g * b := by
        calc g * a * b = g * (a * b) := by group
          _ = a * b * g := h1
          _ = a * (b * g) := by group
          _ = a * (g * b) := by rw [hbc g hg]
          _ = a * g * b := by group
      exact mul_right_cancel h3
    rw [ha1, one_mul] at hy ⊢
    rcases eq_one_or_eq_of_mul_self hπzz hb with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx1, hx2⟩ := hnc
      have h1 := hy (π x)
      rw [h] at h1
      have h3 : π (x * z * x⁻¹) = π z := by
        rw [map_mul, map_mul, map_inv, h1]
        group
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h3
      have h4 : (x * z * x⁻¹)⁻¹ * z = 1 := by
        refine hinvO _ h3 ?_
        have hxi : (x * z * x⁻¹)⁻¹ = x * z * x⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_right hzz, mul_assoc]
        rw [hxi]
        calc x * z * x⁻¹ * z * (x * z * x⁻¹ * z) = x * z * x⁻¹ * (z * (x * z * x⁻¹)) * z := by
              group
          _ = x * z * x⁻¹ * ((x * z * x⁻¹) * z) * z := by rw [hx2]
          _ = x * (z * z) * x⁻¹ * (z * z) := by group
          _ = 1 := by rw [hzz]; group
      exact hx1 (inv_mul_eq_one.1 h4)
  have hcase : CaseTwo (K.map π) (π z) := (LS.of_localSetting hsY hGzY).caseTwo
  obtain ⟨A, B, C, D, hFD⟩ := hFH (X ⧸ O) (K.map π) (π z) hsY hcase
  obtain ⟨R, hR, hcomm, hinter⟩ := h2 hA hHS (X ⧸ O) (K.map π) (π z)
    (KLocalSections.of_isKGroupCat (hKX.quotient O)) hZY hstd hsY A B C D hFD
  exact false_of_wreath' hGzY hzb2 (k := 10) (m := 239085) ⟨119542, by norm_num⟩
    (card_centralizer_of_localSetting hsY) hR hcomm hinter

end CFSG.EvenSporadicStandard.M24Std.GenX
