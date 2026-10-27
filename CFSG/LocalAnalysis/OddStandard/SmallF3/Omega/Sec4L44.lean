module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4AData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L44Slc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem zpowers_eq_one_or_of_orderOf_two {H : Type} [Group H] {t : H}
    (ht : orderOf t = 2) {p : H} (hp : p ∈ Subgroup.zpowers t) : p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private theorem zpowers_sq_eq_one {H : Type} [Group H] {t : H} (ht : orderOf t = 2)
    {p : H} (hp : p ∈ Subgroup.zpowers t) : p ^ 2 = 1 := by
  rcases zpowers_eq_one_or_of_orderOf_two ht hp with h1 | h1
  · rw [h1]
    exact one_pow 2
  · rw [h1, ← ht]
    exact pow_orderOf_eq_one t

private lemma mem_normalizer_zpowers_of_commute {x t : G} (hxt : Commute x t) :
    x ∈ normalizer (Subgroup.zpowers t : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have h : x * t ^ k * x⁻¹ = t ^ k := by
      rw [(hxt.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [h]
    exact Subgroup.zpow_mem_zpowers t k
  · intro hp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hp_eq : p = x⁻¹ * t ^ k * x := by
      calc p = x⁻¹ * (x * p * x⁻¹) * x := by group
        _ = x⁻¹ * t ^ k * x := by rw [← hk]
    rw [hp_eq]
    have h : x⁻¹ * t ^ k * x = t ^ k := by
      rw [(hxt.inv_left.zpow_right k).eq, mul_assoc, inv_mul_cancel, mul_one]
    rw [h]
    exact Subgroup.zpow_mem_zpowers t k

private lemma mem_centerIn_iff' {K : Subgroup G} (a : G) :
    a ∈ centerIn K ↔ a ∈ K ∧ ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm⟩
  · rintro ⟨haK, hcent⟩
    exact ⟨⟨a, haK⟩,
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcent (y : G) y.2).symm, rfl⟩

theorem sec4_card_sup_zpowers [Finite G] {t : G} {L B : Subgroup G} (hBL : B ≤ L)
    (htC : t ∈ centralizer (L : Set G)) (htL : t ∉ L) (ht : orderOf t = 2) :
    Nat.card ↥(B ⊔ zpowers t) = 2 * Nat.card B := by
  have hcomm : ∀ b ∈ B, ∀ p ∈ zpowers t, b * p = p * b := by
    intro b hb p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hbt : Commute b t := (Subgroup.mem_centralizer_iff.mp htC) b (hBL hb)
    exact (hbt.zpow_right k).eq
  have hinf : B ⊓ zpowers t = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rcases zpowers_eq_one_or_of_orderOf_two ht hx.2 with h1 | h1
    · exact h1
    · exact absurd (hBL (h1 ▸ hx.1)) htL
  have h := CFSG.OddStandard.SmallF3.HarrisU33.card_sup_of_commute hcomm hinf
  rw [h, Nat.card_zpowers, ht]
  exact Nat.mul_comm _ _

theorem sec4_isElemAbelian_sup_zpowers {t : G} {L B : Subgroup G} (hBL : B ≤ L)
    (hB : CFSG.Open.IsElemAbelian 2 B) (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    CFSG.Open.IsElemAbelian 2 (B ⊔ zpowers t) := by
  have hcomm : ∀ b ∈ B, ∀ p ∈ zpowers t, b * p = p * b := by
    intro b hb p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hbt : Commute b t := (Subgroup.mem_centralizer_iff.mp htC) b (hBL hb)
    exact (hbt.zpow_right k).eq
  refine ⟨?_, ?_⟩
  · exact CFSG.OddStandard.SmallF3.HarrisU33.isMulCommutative_sup_of_commute hcomm hB.1
      (Subgroup.zpowers_isMulCommutative t)
  · intro x hx
    obtain ⟨b, hb, p, hp, rfl⟩ :=
      (CFSG.OddStandard.SmallF3.HarrisU33.mem_sup_iff_of_commute hcomm).mp hx
    have hbp : Commute b p := hcomm b hb p hp
    rw [hbp.mul_pow 2, hB.2 b hb, zpowers_sq_eq_one ht hp, mul_one]

theorem sec4_sup_zpowers_inf {t : G} {L B : Subgroup G} (hBL : B ≤ L)
    (htC : t ∈ centralizer (L : Set G)) (htL : t ∉ L) (ht : orderOf t = 2) :
    (B ⊔ zpowers t) ⊓ L = B := by
  have hcomm : ∀ b ∈ B, ∀ p ∈ zpowers t, b * p = p * b := by
    intro b hb p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hbt : Commute b t := (Subgroup.mem_centralizer_iff.mp htC) b (hBL hb)
    exact (hbt.zpow_right k).eq
  refine le_antisymm ?_ (le_inf le_sup_left hBL)
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxBt, hxL⟩ := hx
  obtain ⟨b, hb, p, hp, rfl⟩ :=
    (CFSG.OddStandard.SmallF3.HarrisU33.mem_sup_iff_of_commute hcomm).mp hxBt
  have hbL : b ∈ L := hBL hb
  rcases zpowers_eq_one_or_of_orderOf_two ht hp with h1 | h1
  · rw [h1, mul_one]
    exact hb
  · exfalso
    have hpL : p ∈ L := by
      rw [show p = b⁻¹ * (b * p) by group]
      exact L.mul_mem (L.inv_mem hbL) hxL
    exact htL (h1 ▸ hpL)

theorem sec4_z_eq_phi [Finite G] {t : G} {L S B : Subgroup G} {z : G}
    {φ : (Fin 7 → ZMod 2) → G} (hctx : Sec4Ctx G t L S z) (hB : Sec4BData L (S ⊓ L) B φ) :
    ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ φ v = z := by
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hzL : z ∈ L := hctx.pocket.mem
  have hz2 : z ^ 2 = 1 := by
    rw [← hctx.pocket.1]
    exact pow_orderOf_eq_one z
  have hzB : z ∈ centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hctx.central b (Subgroup.mem_inf.mp (hB.isMax.1 hb)).1
  have hzmem : z ∈ centralizer (B : Set G) ⊓ L := ⟨hzB, hzL⟩
  rw [hB.cent] at hzmem
  have hcomm : ∀ b ∈ B, ∀ c ∈ centerIn L, b * c = c * b := by
    intro b hb c hc
    have hbL : b ∈ L := (Subgroup.mem_inf.mp (hB.isMax.1 hb)).2
    exact ((mem_centerIn_iff' c).mp hc).2 b hbL |>.symm
  obtain ⟨b, hb, c, hc, hbc⟩ :=
    (CFSG.OddStandard.SmallF3.HarrisU33.mem_sup_iff_of_commute hcomm).mp hzmem
  have hb2 : b ^ 2 = 1 := hB.isMax.2.1.2 b hb
  have hc2 : c ^ 2 = 1 := by
    have hbc_comm : Commute b c := hcomm b hb c hc
    have h := hbc_comm.mul_pow 2
    rw [← hbc, hz2, hb2, one_mul] at h
    exact h.symm
  have hcL : c ∈ L := ((mem_centerIn_iff' c).mp hc).1
  have hcCent : c ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((mem_centerIn_iff' c).mp hc).2 l hl |>.symm
  have hcodd : Odd (orderOf c) := sec4_odd_orderOf_of_mem_centralizer hL hcL hcCent
  have hc1 : c = 1 := by
    have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hcodd
      exact absurd hcodd (by decide)
  have hzBmem : z ∈ B := by
    rw [hbc, hc1, mul_one]
    exact hb
  obtain ⟨v, hv, hφv⟩ := (hB.perm.2.2.1 z).mp hzBmem
  have hz1 : z ≠ 1 := by
    intro h
    have h2 := hctx.pocket.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hv0 : v ≠ 0 := by
    intro hv0
    apply hz1
    rw [← hφv, hv0]
    exact IsPermModuleVia.map_zero hB.perm
  exact ⟨v, hv, (hB.type4 v hv hv0).mpr (hφv.symm ▸ hctx.pocket), hφv⟩

theorem sec4_inf_normalizer_eq {t : G} {L A B : Subgroup G} (hLt : L ≤ centralizer ({t} : Set G))
    (hA : A = B ⊔ zpowers t) (hAL : A ⊓ L = B) :
    L ⊓ normalizer (A : Set G) = L ⊓ normalizer (B : Set G) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxL, hxN⟩ := hx
    refine ⟨hxL, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro b
    rw [show b ∈ B ↔ b ∈ A ∧ b ∈ L by rw [← hAL, Subgroup.mem_inf],
      show x * b * x⁻¹ ∈ B ↔ x * b * x⁻¹ ∈ A ∧ x * b * x⁻¹ ∈ L by
        rw [← hAL, Subgroup.mem_inf]]
    exact and_congr (hxN b) (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxL) b)
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxL, hxN⟩ := hx
    refine ⟨hxL, ?_⟩
    have hxt : Commute x t := ((Subgroup.mem_centralizer_iff.mp (hLt hxL)) t
      (Set.mem_singleton t)).symm
    have hxNT : x ∈ normalizer (Subgroup.zpowers t : Set G) :=
      mem_normalizer_zpowers_of_commute hxt
    rw [hA]
    exact Subgroup.inf_normalizer_le_normalizer_sup (H := B) (K := zpowers t) ⟨hxN, hxNT⟩

theorem Sec4AData.card_A [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G} (hctx : Sec4Ctx G t L S z) (h : Sec4AData t L S z A B φ) :
    Nat.card A = 2 ^ 7 := by
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (h.bdata.isMax.1 hb)).2
  have htC : t ∈ centralizer (L : Set G) :=
    sec4_t_mem_centralizer hctx.toSec4Setting.toSec3SettingLB.toSec3Setting
  have htL : t ∉ L := sec4_t_not_mem hctx.toSec4Setting
  have hcard := sec4_card_sup_zpowers hBL htC htL hctx.involution
  rw [h.A_eq, hcard, h.bdata.card]
  norm_num

theorem sec4_exists_AData (h36 : Asc82Lemma36) (h42 : Asc82Lemma42) (hE : Asc82FactE64)
    (hC : Asc82FactCentB) : Asc82ADataExists := by
  intro G _ _ t L S z hctx
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have htC : t ∈ centralizer (L : Set G) :=
    sec4_t_mem_centralizer hctx.toSec4Setting.toSec3SettingLB.toSec3Setting
  have htL : t ∉ L := sec4_t_not_mem hctx.toSec4Setting
  have hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec4Setting.toSec3SettingLB
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hLt hN hS
  obtain ⟨B, φ, hB⟩ := hE G L hL (S ⊓ L) hP
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (hB.isMax.1 hb)).2
  have hAcard : Nat.card ↥(B ⊔ zpowers t) = 2 ^ 7 := by
    rw [sec4_card_sup_zpowers hBL htC htL hctx.involution, hB.card]
    norm_num
  have hAe : CFSG.Open.IsElemAbelian 2 (B ⊔ zpowers t) :=
    sec4_isElemAbelian_sup_zpowers hBL hB.isMax.2.1 htC hctx.involution
  have hA_le : (B ⊔ zpowers t) ≤ SLC S L := by
    refine sup_le ?_ ?_
    · intro b hb
      have hbSL := hB.isMax.1 hb
      exact ⟨(Subgroup.mem_inf.mp hbSL).1, Subgroup.mem_sup_left (Subgroup.mem_inf.mp hbSL).2⟩
    · exact Subgroup.zpowers_le.mpr
        ⟨sec4_t_mem_S hS hctx.involution, Subgroup.mem_sup_right htC⟩
  have hslc : ∀ E : Subgroup G, E ≤ SLC S L → CFSG.Open.IsElemAbelian 2 E →
      Nat.card E ≤ 2 ^ 7 ∧ (Nat.card E = 2 ^ 7 → E = B ⊔ zpowers t) := fun E hE' hEa =>
    sec4_elemAbelian_slc hL hLt hN hS (h42 G t L hctx.toSec4Setting) hB.isMax hB.unique
      hB.card hctx.involution htC htL hE' hEa
  refine ⟨B ⊔ zpowers t, B, φ, ?_⟩
  exact
  { bdata := hB
    isMax := ⟨hA_le, hAe, fun E hE' hEa => hAcard ▸ (hslc E hE' hEa).1⟩
    unique := fun A' hA' => by
      have hle : Nat.card ↥(B ⊔ zpowers t) ≤ Nat.card A' := hA'.2.2 (B ⊔ zpowers t) hA_le hAe
      have hcard' : Nat.card A' = 2 ^ 7 :=
        le_antisymm (hslc A' hA'.1 hA'.2.1).1 (hAcard ▸ hle)
      exact (hslc A' hA'.1 hA'.2.1).2 hcard'
    A_eq := rfl
    B_eq := sec4_sup_zpowers_inf hBL htC htL hctx.involution
    centB := fun x hxS hxcomm => by
      have hxC : x ∈ centralizer ({t} : Set G) := hS.1 hxS
      have hxN : x ∈ normalizer (L : Set G) := hN x hxC
      have hxBC : x ∈ B ⊔ centralizer (L : Set G) :=
        hC G L hL (S ⊓ L) B hP hB.isMax hB.card x hxN hxcomm
      refine ⟨hxS, ?_⟩
      exact sup_le (hBL.trans le_sup_left) le_sup_right hxBC
    z_eq := sec4_z_eq_phi hctx hB }

theorem asc82Lemma44d_of (hAD : Asc82ADataExists) : Asc82Lemma44d := by
  intro G _ _ t L S z hctx A hA
  obtain ⟨A₀, B, φ, hD⟩ := hAD G t L S z hctx
  rw [hD.unique A hA]
  obtain ⟨v, hv, hw, hφv⟩ := hD.z_eq
  have hnorm := sec4_inf_normalizer_eq (t := t) hctx.component.le hD.A_eq hD.B_eq
  rw [hD.B_eq, hnorm, ← hφv]
  exact (IsPermModuleVia.closure_conjClassIn hD.bdata.perm hv (Or.inr (Or.inl hw))).symm

theorem asc82Lemma44e_of (hAD : Asc82ADataExists) : Asc82Lemma44e := by
  intro G _ _ t L S z hctx A hA
  obtain ⟨A₀, B, φ, hD⟩ := hAD G t L S z hctx
  rw [hD.unique A hA]
  obtain ⟨v, hv, hw, hφv⟩ := hD.z_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD.A_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  · rw [hD.A_eq, ← hφv]
    exact Subgroup.mem_sup_left (IsPermModuleVia.mem hD.bdata.perm hv)
  · rw [hD.B_eq, hD.A_eq]
  · rw [hD.B_eq, hD.bdata.card]

end CFSG.OddStandard.SmallF3.Omega