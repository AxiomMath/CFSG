module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFPerm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace JankoF

variable {G : Type*} [Group G] {z : G}
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

theorem coe_mem_map_comap_iff {Y : Subgroup (alternatingGroup (Fin 9))}
    (u : centralizer ({z} : Set G)) :
    (u : G) ∈ (Y.comap (proj e)).map (centralizer ({z} : Set G)).subtype ↔ proj e u ∈ Y :=
  mem_map_iff_mem (centralizer ({z} : Set G)).subtype_injective

theorem self_mem_centralizer : z ∈ centralizer ({z} : Set G) :=
  mem_centralizer_singleton_iff.mpr rfl

theorem mk_mem_center :
    (⟨z, self_mem_centralizer⟩ : centralizer ({z} : Set G)) ∈ center (centralizer ({z} : Set G)) :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)

theorem proj_mk_eq_one : proj e (⟨z, self_mem_centralizer⟩ : centralizer ({z} : Set G)) = 1 :=
  (proj_eq_one_iff e).mpr mk_mem_center

theorem zbar_eq (hz : orderOf z = 2) (hH : IsTwoANine (centralizer ({z} : Set G))) :
    zbar (centralizer ({z} : Set G)) = ⟨z, self_mem_centralizer⟩ :=
  (hH.eq_zbar_of_mem_center mk_mem_center fun h => by
    have h1 : z = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)).symm

theorem card_map_subgroupOf_of_odd (hH : IsTwoANine (centralizer ({z} : Set G))) {B : Subgroup G}
    (hBH : B ≤ centralizer ({z} : Set G)) (hodd : Odd (Nat.card B)) :
    Nat.card ((B.subgroupOf (centralizer ({z} : Set G))).map (proj e)) = Nat.card B := by
  have hc : Nat.card (B.subgroupOf (centralizer ({z} : Set G))) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv
  exact (hH.card_map_proj_of_odd e (hc ▸ hodd)).trans hc

theorem map_subgroupOf_le_Fbar {B : Subgroup G} (hBF : B ≤ Janko.F e) :
    (B.subgroupOf (centralizer ({z} : Set G))).map (proj e) ≤ Janko.Fbar := by
  rintro _ ⟨b, hb, rfl⟩
  exact (coe_mem_map_comap_iff e b).mp (hBF hb)

end JankoF

namespace Janko

variable {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
  (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))
include hH

theorem card_F : Nat.card (F e) = 720 := by
  rw [F, card_map_of_injective (centralizer _).subtype_injective, hH.card_comap_proj e,
    JankoF.card_Fbar]

theorem finite_F : Finite (F e) :=
  Nat.finite_of_card_ne_zero (by rw [card_F hH e]; norm_num)

omit hH in
theorem z_mem_F : z ∈ F e :=
  (JankoF.coe_mem_map_comap_iff e ⟨z, JankoF.self_mem_centralizer⟩).mpr
    (by rw [JankoF.proj_mk_eq_one]; exact one_mem _)

theorem F_le_centralizer_s₁ : F e ≤ centralizer ({s₁ e} : Set G) := by
  have hodd : Odd (orderOf sbar₁) := by rw [orderOf_sbar₁]; exact ⟨1, rfl⟩
  rintro _ ⟨u, hu, rfl⟩
  have hc : Commute u (liftOdd e sbar₁) := hH.commute_of_odd_orderOf e
    (hH.odd_orderOf_liftOdd e hodd)
    (by rw [hH.proj_liftOdd e hodd]; exact JankoF.commute_sbar₁_of_mem_Fbar hu)
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc.eq)

omit hH in
theorem centralizer_zpowers_s₁ :
    centralizer ((zpowers (s₁ e) : Subgroup G) : Set G) = centralizer ({s₁ e} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem F_le_centralizer : F e ≤ centralizer ((zpowers (s₁ e) : Subgroup G) : Set G) := by
  rw [centralizer_zpowers_s₁]
  exact F_le_centralizer_s₁ hH e

theorem s₁_notMem_F : s₁ e ∉ F e := by
  have hodd : Odd (orderOf sbar₁) := by rw [orderOf_sbar₁]; exact ⟨1, rfl⟩
  intro h
  rw [s₁, F, JankoF.coe_mem_map_comap_iff, hH.proj_liftOdd e hodd] at h
  exact JankoF.sbar₁_notMem_Fbar h

theorem card_zpowers_s₁ : Nat.card (zpowers (s₁ e)) = 3 := by
  rw [Nat.card_zpowers, orderOf_s₁ hH e]

theorem P₁_inf_F : zpowers (s₁ e) ⊓ F e = ⊥ := by
  have h3 := card_zpowers_s₁ hH e
  have : Finite (zpowers (s₁ e)) := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
  have hdvd : Nat.card (zpowers (s₁ e) ⊓ F e : Subgroup G) ∣ 3 :=
    h3 ▸ card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exfalso
    have heq : zpowers (s₁ e) ⊓ F e = zpowers (s₁ e) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h3])
    exact s₁_notMem_F hH e ((inf_eq_left.mp heq) (mem_zpowers _))

theorem centralizer_P₁ :
    centralizer ((zpowers (s₁ e) : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
      zpowers (s₁ e) ⊔ F e := by
  have hC : Nat.card (centralizer ((zpowers (s₁ e) : Subgroup G) : Set G) ⊓
      centralizer ({z} : Set G) : Subgroup G) = 2160 := by
    rw [centralizer_zpowers_s₁]
    exact card_centralizer_s₁ hH e
  have : Finite (centralizer ((zpowers (s₁ e) : Subgroup G) : Set G) ⊓
      centralizer ({z} : Set G) : Subgroup G) :=
    Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hP : zpowers (s₁ e) ≤ centralizer ((zpowers (s₁ e) : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_s₁]
    exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hle : zpowers (s₁ e) ⊔ F e ≤ centralizer ((zpowers (s₁ e) : Subgroup G) : Set G) ⊓
      centralizer ({z} : Set G) :=
    sup_le (le_inf hP (zpowers_le.mpr (s₁_mem e))) (le_inf (F_le_centralizer hH e) (F_le e))
  have hcard : Nat.card (zpowers (s₁ e) ⊔ F e : Subgroup G) = 2160 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      ((F_le_centralizer hH e).trans (centralizer_le_normalizer _))
      (disjoint_iff.mpr (P₁_inf_F hH e)), card_zpowers_s₁ hH e, card_F hH e]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hC, hcard])).symm

include hz in
theorem eq_z_of_mem_F : ∀ x ∈ F e, orderOf x = 2 → x = z := by
  rintro _ ⟨u, hu, rfl⟩ hx
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hx
  by_contra hne
  have hu' : u ≠ zbar (centralizer ({z} : Set G)) := fun h =>
    hne (by rw [h, JankoF.zbar_eq hz hH]; rfl)
  have hct := hH.cycleType_eq_of_orderOf_eq_two e hx hu'
  obtain ⟨h0, h1, h2⟩ := mem_Fbar_iff.mp (mem_comap.mp hu)
  have hs := JankoPerm.card_support_le_six h0 h1 h2
  rw [← Perm.sum_cycleType, hct] at hs
  norm_num at hs

omit hH in
private theorem normal_map_subgroupOf {B : Subgroup G} (hFB : F e ≤ normalizer (B : Set G)) :
    (((B.subgroupOf (centralizer ({z} : Set G))).map (proj e)).subgroupOf Fbar).Normal := by
  constructor
  rintro n hn g
  obtain ⟨b, hb, hbn⟩ := mem_subgroupOf.mp hn
  obtain ⟨f, hf⟩ := proj_surjective e (g : alternatingGroup (Fin 9))
  have hfF : (f : G) ∈ F e := (JankoF.coe_mem_map_comap_iff e f).mpr (by rw [hf]; exact g.2)
  have hconj : f * b * f⁻¹ ∈ B.subgroupOf (centralizer ({z} : Set G)) := by
    have hb' : (b : G) ∈ B := hb
    exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp (hFB hfF) b).mp hb')
  refine mem_subgroupOf.mpr ⟨f * b * f⁻¹, hconj, ?_⟩
  rw [map_mul, map_mul, map_inv, hf, hbn]
  rfl

include hz in
theorem z_mem_of_normal :
    ∀ B : Subgroup G, B ≤ F e → F e ≤ normalizer (B : Set G) → B ≠ ⊥ → z ∈ B := by
  intro B hBF hFB hB
  have := finite_F hH e
  have : Finite B := Finite.of_injective (Subgroup.inclusion hBF) (Subgroup.inclusion_injective hBF)
  rcases Nat.even_or_odd (Nat.card B) with hev | hodd
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have hxz := eq_z_of_mem_F hz hH e x (hBF x.2) (by rw [Subgroup.orderOf_coe, hx])
    exact hxz ▸ x.2
  · exfalso
    have hBH : B ≤ centralizer ({z} : Set G) := hBF.trans (F_le e)
    have hcard := JankoF.card_map_subgroupOf_of_odd e hH hBH hodd
    have hle := JankoF.map_subgroupOf_le_Fbar e hBF
    have := normal_map_subgroupOf e hFB
    rcases JankoF.isSimpleGroup_Fbar.eq_bot_or_eq_top_of_normal
        (((B.subgroupOf (centralizer ({z} : Set G))).map (proj e)).subgroupOf Fbar) with h | h
    · rw [subgroupOf_eq_bot] at h
      have hbot := disjoint_iff.mp h
      rw [inf_of_le_left hle] at hbot
      rw [hbot, card_bot] at hcard
      exact hB (Subgroup.card_eq_one.mp hcard.symm)
    · rw [subgroupOf_eq_top] at h
      have h360 : 360 ∣ Nat.card B := by
        rw [← hcard, ← JankoF.card_Fbar]
        exact card_dvd_of_le h
      obtain ⟨k, hk⟩ := hodd
      omega

theorem card_dvd_nine_or_eq_five_of_odd {B : Subgroup G} (hBF : B ≤ F e)
    (hodd : Odd (Nat.card B)) : Nat.card B ∣ 9 ∨ Nat.card B = 5 := by
  have hcard := JankoF.card_map_subgroupOf_of_odd e hH (hBF.trans (F_le e)) hodd
  rw [← hcard] at hodd ⊢
  exact JankoPerm.card_dvd_nine_or_eq_five_of_odd_alt (JankoF.map_subgroupOf_le_Fbar e hBF) hodd

theorem card_le_of_odd :
    ∀ B : Subgroup G, B ≤ F e → Odd (Nat.card B) → Nat.card B ≤ 9 := by
  intro B hBF hodd
  rcases card_dvd_nine_or_eq_five_of_odd hH e hBF hodd with h | h
  · exact Nat.le_of_dvd (by norm_num) h
  · omega

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
