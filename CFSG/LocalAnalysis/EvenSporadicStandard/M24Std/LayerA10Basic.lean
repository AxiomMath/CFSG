module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardQuotient
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open
open scoped Pointwise

instance egaLayer_characteristic (X : Type) [Group X] : (egaLayer X).Characteristic := by
  rw [characteristic_iff_map_le]
  intro φ
  rw [egaLayer, Subgroup.map_iSup]
  refine iSup_le fun K => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hK => ?_
  have h := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv φ hK
  rw [map_top_of_surjective _ φ.surjective] at h
  exact le_iSup₂_of_le (f := fun K (_ : IsComponentOf K ⊤) => K) (K.map φ.toMonoidHom) h le_rfl

theorem egaLayer_normal (X : Type) [Group X] : (egaLayer X).Normal :=
  inferInstance

theorem inf_centralizer_subgroupOf_normal {Y : Type*} [Group Y] {E : Subgroup Y} (hE : E.Normal)
    (t : Y) :
    ((E ⊓ centralizer ({t} : Set Y)).subgroupOf (centralizer ({t} : Set Y))).Normal := by
  rw [normal_subgroupOf_iff inf_le_right]
  intro x c hx hc
  exact mem_inf.2 ⟨hE.conj_mem x (mem_inf.1 hx).1 c,
    mul_mem (mul_mem hc (mem_inf.1 hx).2) (inv_mem hc)⟩

theorem le_or_card_le_of_le_sup_zpowers {Y : Type*} [Group Y] [Finite Y] {H K : Subgroup Y}
    [IsSimpleGroup H] {z : Y} (hz : z ∈ centralizer (H : Set Y)) (hK : K ≤ H ⊔ zpowers z)
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) : H ≤ K ∨ Nat.card K ≤ Nat.card (zpowers z) := by
  have hn : ((K ⊓ H).subgroupOf H).Normal := by
    rw [normal_subgroupOf_iff inf_le_right]
    intro x h hx hh
    exact mem_inf.2 ⟨hHK h hh x (mem_inf.1 hx).1,
      mul_mem (mul_mem hh (mem_inf.1 hx).2) (inv_mem hh)⟩
  rcases hn.eq_bot_or_eq_top with hb | ht
  · right
    have hle : zpowers z ≤ normalizer (H : Set Y) :=
      zpowers_le.2 (centralizer_le_normalizer _ hz)
    have hmem : ∀ k : K, ∃ w : zpowers z, (k : Y) * (w : Y)⁻¹ ∈ H := by
      intro k
      have hk : (k : Y) ∈ ((H ⊔ zpowers z : Subgroup Y) : Set Y) := hK k.2
      rw [coe_mul_of_right_le_normalizer_left H _ hle] at hk
      obtain ⟨h, hh, w, hw, hhw⟩ := Set.mem_mul.1 hk
      refine ⟨⟨w, hw⟩, ?_⟩
      rw [← hhw, mul_inv_cancel_right]
      exact hh
    choose f hf using hmem
    refine Nat.card_le_card_of_injective f fun k₁ k₂ h12 => ?_
    have h1 := hf k₁
    rw [h12] at h1
    have hH : (k₁ : Y) * (k₂ : Y)⁻¹ ∈ H := by
      have h3 := mul_mem h1 (inv_mem (hf k₂))
      have e : (k₁ : Y) * ((f k₂ : zpowers z) : Y)⁻¹ * ((k₂ : Y) * ((f k₂ : zpowers z) : Y)⁻¹)⁻¹ =
          (k₁ : Y) * (k₂ : Y)⁻¹ := by group
      rwa [e] at h3
    have hm : (⟨_, hH⟩ : H) ∈ (K ⊓ H).subgroupOf H :=
      mem_subgroupOf.2 (mem_inf.2 ⟨mul_mem k₁.2 (inv_mem k₂.2), hH⟩)
    rw [hb, mem_bot] at hm
    exact Subtype.ext (mul_inv_eq_one.1 (congrArg Subtype.val hm))
  · left
    exact (subgroupOf_eq_top.1 ht).trans inf_le_left

theorem card_sup_zpowers_le {Y : Type*} [Group Y] {H : Subgroup Y} {z : Y}
    (hz : z ∈ normalizer (H : Set Y)) :
    Nat.card (H ⊔ zpowers z : Subgroup Y) ≤ Nat.card H * Nat.card (zpowers z) := by
  have h := coe_mul_of_right_le_normalizer_left H (zpowers z) (zpowers_le.2 hz)
  calc Nat.card (H ⊔ zpowers z : Subgroup Y)
      = Nat.card ((H : Set Y) * (zpowers z : Set Y)) := by rw [← h]; rfl
    _ ≤ Nat.card H * Nat.card (zpowers z) := Set.natCard_mul_le

theorem card_le_two_or_of_le_sup_zpowers {Y : Type*} [Group Y] [Finite Y] {H K : Subgroup Y}
    [IsSimpleGroup H] {z : Y} (hz2 : z ^ 2 = 1) (hz : z ∈ centralizer (H : Set Y))
    (hK : K ≤ H ⊔ zpowers z) (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) :
    Nat.card K ≤ 2 ∨ Nat.card K = Nat.card H ∨ Nat.card K = 2 * Nat.card H := by
  have h2 : Nat.card (zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos hz2
  rcases le_or_card_le_of_le_sup_zpowers hz hK hHK with hHK' | hc
  · right
    have hle : Nat.card K ≤ Nat.card H * 2 :=
      (card_le_of_le hK).trans ((card_sup_zpowers_le (centralizer_le_normalizer _ hz)).trans
        (Nat.mul_le_mul_left _ h2))
    obtain ⟨m, hm⟩ := card_dvd_of_le hHK'
    have hpos : 0 < Nat.card H := Nat.card_pos
    have hK0 : 0 < Nat.card K := Nat.card_pos
    rw [hm] at hle hK0
    have hm2 : m ≤ 2 := Nat.le_of_mul_le_mul_left hle hpos
    interval_cases m
    · simp at hK0
    · exact Or.inl (by rw [hm, mul_one])
    · exact Or.inr (by rw [hm, mul_comm])
  · exact Or.inl (hc.trans h2)

theorem card_inf_centralizer_le_two_or {Y : Type*} [Group Y] [Finite Y] {t : Y}
    {H E : Subgroup Y} [IsSimpleGroup H] (ht : t ^ 2 = 1)
    (hC : centralizer ({t} : Set Y) = H ⊔ zpowers t) (ht' : t ∈ centralizer (H : Set Y))
    (hE : E.Normal) :
    Nat.card (E ⊓ centralizer ({t} : Set Y) : Subgroup Y) ≤ 2 ∨
      (H ≤ E ∧ Nat.card H ≤ Nat.card (E ⊓ centralizer ({t} : Set Y) : Subgroup Y) ∧
        Nat.card (E ⊓ centralizer ({t} : Set Y) : Subgroup Y) ≤ 2 * Nat.card H ∧
        (Nat.card (E ⊓ centralizer ({t} : Set Y) : Subgroup Y) = 2 * Nat.card H → t ∈ E)) := by
  have hHC : H ≤ centralizer ({t} : Set Y) := hC ▸ le_sup_left
  have h2 : Nat.card (zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos ht
  have hCcard : Nat.card (centralizer ({t} : Set Y)) ≤ 2 * Nat.card H := by
    rw [hC, mul_comm]
    exact (card_sup_zpowers_le (centralizer_le_normalizer _ ht')).trans
      (Nat.mul_le_mul_left _ h2)
  have hKle : E ⊓ centralizer ({t} : Set Y) ≤ H ⊔ zpowers t := hC ▸ inf_le_right
  rcases le_or_card_le_of_le_sup_zpowers ht' hKle (fun h hh k hk =>
      mem_inf.2 ⟨hE.conj_mem k (mem_inf.1 hk).1 h,
        mul_mem (mul_mem (hHC hh) (mem_inf.1 hk).2) (inv_mem (hHC hh))⟩) with hHK | hK
  · right
    have hKC : Nat.card (E ⊓ centralizer ({t} : Set Y) : Subgroup Y) ≤
        Nat.card (centralizer ({t} : Set Y)) := card_le_of_le inf_le_right
    refine ⟨hHK.trans inf_le_left, card_le_of_le hHK, hKC.trans hCcard, fun heq => ?_⟩
    have hKe : E ⊓ centralizer ({t} : Set Y) = centralizer ({t} : Set Y) :=
      eq_of_le_of_card_ge inf_le_right (by omega)
    have htK : t ∈ E ⊓ centralizer ({t} : Set Y) := by
      rw [hKe]
      exact mem_centralizer_singleton_iff.2 rfl
    exact (mem_inf.1 htK).1
  · exact Or.inl (hK.trans h2)

theorem card_inf_centralizer_mk_le_two_or {X : Type*} [Group X] [Finite X] {z : X}
    {H : Subgroup X} [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a) (hz : orderOf z = 2)
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    {E : Subgroup (X ⧸ fusionOddCore X)} (hE : E.Normal) :
    Nat.card (E ⊓ centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
        Set (X ⧸ fusionOddCore X)) : Subgroup (X ⧸ fusionOddCore X)) ≤ 2 ∨
      (Nat.card H ≤ Nat.card (E ⊓ centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
          Set (X ⧸ fusionOddCore X)) : Subgroup (X ⧸ fusionOddCore X)) ∧
        Nat.card (E ⊓ centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
          Set (X ⧸ fusionOddCore X)) : Subgroup (X ⧸ fusionOddCore X)) ≤ 2 * Nat.card H ∧
        (Nat.card (E ⊓ centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
            Set (X ⧸ fusionOddCore X)) : Subgroup (X ⧸ fusionOddCore X)) = 2 * Nat.card H →
          QuotientGroup.mk' (fusionOddCore X) z ∈ E)) := by
  obtain ⟨hHq, hZ⟩ := isQuasisimple_center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨eH⟩ := nonempty_map_fusionOddCore_mulEquiv (disjoint_fusionOddCore hHq hZ)
  have : IsSimpleGroup (H.map (QuotientGroup.mk' (fusionOddCore X))) := eH.isSimpleGroup
  have hcard : Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X))) = Nat.card H :=
    Nat.card_congr eH.toEquiv
  have ht : QuotientGroup.mk' (fusionOddCore X) z ^ 2 = 1 := by
    rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  have ht' : QuotientGroup.mk' (fusionOddCore X) z ∈
      centralizer ((H.map (QuotientGroup.mk' (fusionOddCore X)) : Subgroup _) :
        Set (X ⧸ fusionOddCore X)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hz' h hh]
  rcases card_inf_centralizer_le_two_or ht (centralizer_mk_fusionOddCore_eq hz hC hz') ht' hE with
    h | ⟨-, h1, h2, h3⟩
  · exact Or.inl h
  · rw [hcard] at h1 h2 h3
    exact Or.inr ⟨h1, h2, h3⟩

end CFSG.EvenSporadicStandard.M24Std
