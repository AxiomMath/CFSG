module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeSetup

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

structure WtSpec {G : Type} [Group G] (W : Subgroup G) (t : G) (X O Wt : Subgroup G) : Prop where
  O_le : O ≤ Wt
  le_X : Wt ≤ X
  norm : ∀ n ∈ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G), ∀ x ∈ Wt, n * x * n⁻¹ ∈ Wt
  W_le : W ≤ Wt
  t_not_mem : t ∉ Wt
  card : Nat.card Wt = Nat.card O * 2 ^ 8
  comm : ∀ x ∈ Wt, ∀ y ∈ Wt, x * y * x⁻¹ * y⁻¹ ∈ O
  sq : ∀ x ∈ Wt, x * x ∈ O
  cent_t : ∀ w ∈ Wt, w * t = t * w → w ∈ W ⊔ O
  comm_onto : ∀ v ∈ W, ∃ w ∈ Wt, v⁻¹ * (t * w * t⁻¹ * w⁻¹) ∈ O

namespace IsSetting25

variable {G : Type} [Group G] [Finite G] {A W X O : Subgroup G} {t : G}
  (S : IsSetting25 A W t X O)

section Sylow

variable {Sy : Subgroup G}
  (hSy : IsSylowOf 2 Sy (normalizer ((W ⊔ zpowers t : Subgroup G) : Set G)))

include S hSy

theorem E_le_sylow : W ⊔ zpowers t ≤ Sy := by
  obtain ⟨Q, hQ⟩ := hSy.exists_sylow_eq_subgroupOf
  have hP : IsPGroup 2 ((W ⊔ zpowers t).subgroupOf
      (normalizer ((W ⊔ zpowers t : Subgroup G) : Set G))) := S.isPGroup_E.comap_subtype
  have hle := hP.le_sylow_of_normal Q
  rw [hQ] at hle
  intro x hx
  exact hle (show (⟨x, Subgroup.le_normalizer hx⟩ :
    ↥(normalizer ((W ⊔ zpowers t : Subgroup G) : Set G))) ∈ _ from hx)

theorem isSylowOf_inf_X : IsSylowOf 2 (Sy ⊓ X) X :=
  hSy.inf_of_le_normalizer S.X_le S.normalizer_le

theorem card_inf_X : Nat.card ↥(Sy ⊓ X) = 2 ^ 9 := by
  rw [(S.isSylowOf_inf_X hSy).card_eq, S.card_X]
  have hO : 0 < Nat.card O := Nat.card_pos
  have hodd : ¬ 2 ∣ Nat.card O := S.O_odd.not_two_dvd_nat
  rw [Nat.factorization_mul hO.ne' (pow_ne_zero 9 two_ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, zero_add]

theorem inf_centralizer_W_eq : Sy ⊓ centralizer (W : Set G) = Sy ⊓ X := by
  ext s
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hsS, hsC⟩
    exact ⟨hsS, S.normalizer_inf_centralizer_le (Subgroup.mem_inf.mpr ⟨hSy.le hsS, hsC⟩)⟩
  · rintro ⟨hsS, hsX⟩
    refine ⟨hsS, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact (mul_inv_eq_iff_eq_mul.mp (S.X_cent s hsX w hw)).symm

theorem exists_cent_t : ∀ s ∈ Sy, ∃ y ∈ Sy ⊓ X, y⁻¹ * s ∈ centralizer ({t} : Set G) := by
  intro s hs
  obtain ⟨w, hw, hst⟩ := S.conj_t s (hSy.le hs)
  obtain ⟨p, hp, hpt⟩ := S.trans w hw
  have hYO : Sy ⊓ X ≤ normalizer (O : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun o ho =>
      S.O_norm y (hSy.le (Subgroup.mem_inf.mp hy).1) o ho
  obtain ⟨o, ho, y, hy, rfl⟩ := S.eq_mul_of_card (Z := X) (P := Sy ⊓ X) S.O_le_X inf_le_right
    (S.card_inf_X hSy) S.card_X hYO p hp
  have hyN : y ∈ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G) :=
    S.X_le (Subgroup.mem_inf.mp hy).2
  have he : y * t * y⁻¹ ∈ W ⊔ zpowers t :=
    (Subgroup.mem_normalizer_iff.mp hyN t).mp (mem_sup_right (mem_zpowers t))
  have h1 : y * t * y⁻¹ = t * w := by
    rw [← hpt]
    calc y * t * y⁻¹ = (o * (y * t * y⁻¹)) * o⁻¹ := by
          rw [S.O_comm ho he, mul_inv_cancel_right]
      _ = o * y * t * (o * y)⁻¹ := by group
  refine ⟨y, hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc y⁻¹ * s * t = y⁻¹ * (s * t * s⁻¹) * s := by group
    _ = y⁻¹ * (y * t * y⁻¹) * s := by rw [h1, hst]
    _ = t * (y⁻¹ * s) := by group

end Sylow

section Wt

variable {Sy : Subgroup G}
  (hSy : IsSylowOf 2 Sy (normalizer ((W ⊔ zpowers t : Subgroup G) : Set G)))
  {Wt : Subgroup G} (hWt : WtSpec W t X O Wt)

include S hSy hWt

theorem isSylowOf_inf_Wt : IsSylowOf 2 (Sy ⊓ Wt) Wt := by
  refine hSy.inf_of_le_normalizer (hWt.le_X.trans S.X_le) fun n hn => ?_
  exact Subgroup.mem_normalizer_fintype fun x hx => hWt.norm n hn x hx

theorem card_inf_Wt : Nat.card ↥(Sy ⊓ Wt) = 2 ^ 8 := by
  rw [(S.isSylowOf_inf_Wt hSy hWt).card_eq, hWt.card,
    Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero 8 two_ne_zero),
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd S.O_odd.not_two_dvd_nat, zero_add]

omit hWt in
theorem disjoint_O_inf_Wt : Disjoint O (Sy ⊓ Wt) :=
  S.disjoint_O_of_isPGroup hSy.isPGroup.to_inf_left

theorem elem_inf_Wt : IsElemAbelian 2 (Sy ⊓ Wt) := by
  have hd : ∀ {x : G}, x ∈ O → x ∈ Sy ⊓ Wt → x = 1 :=
    Subgroup.disjoint_def.mp (S.disjoint_O_inf_Wt hSy)
  refine L34.isElemAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · have h1 : x * y * x⁻¹ * y⁻¹ = 1 :=
      hd (hWt.comm x (Subgroup.mem_inf.mp hx).2 y (Subgroup.mem_inf.mp hy).2)
        (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy))
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  · rw [sq]
    exact hd (hWt.sq x (Subgroup.mem_inf.mp hx).2) (mul_mem hx hx)

omit S [Finite G] in
theorem normal_inf_Wt : ((Sy ⊓ Wt).subgroupOf Sy).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnSy, hnWt⟩ := Subgroup.mem_inf.mp hn
  exact Subgroup.mem_inf.mpr
    ⟨mul_mem (mul_mem g.2 hnSy) (inv_mem g.2), hWt.norm (g : G) (hSy.le g.2) (n : G) hnWt⟩

theorem W_le_inf_Wt : W ≤ Sy ⊓ Wt :=
  le_inf (le_sup_left.trans (S.E_le_sylow hSy)) hWt.W_le

omit S hSy [Finite G] in
theorem t_not_mem_inf_Wt : t ∉ Sy ⊓ Wt :=
  fun h => hWt.t_not_mem (Subgroup.mem_inf.mp h).2

theorem inf_Wt_inf_centralizer_t : (Sy ⊓ Wt) ⊓ centralizer ({t} : Set G) = W := by
  refine le_antisymm (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨hwSy, hwWt⟩ := Subgroup.mem_inf.mp hw1
    have hcomm : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp hw2
    obtain ⟨v, hv, o, ho, rfl⟩ := S.mem_sup_W_O (hWt.cent_t w hwWt hcomm)
    have hvo : v * o = o * v := (S.O_comm ho (Subgroup.mem_sup_left hv)).symm
    have hv2 : ∃ n, orderOf v = 2 ^ n := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp S.isPGroup_W ⟨v, hv⟩
      exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
    have hvo2 : ∃ m, orderOf (v * o) = 2 ^ m := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hSy.isPGroup ⟨v * o, hwSy⟩
      exact ⟨m, by rwa [Subgroup.orderOf_mk] at hm⟩
    rw [S.eq_one_of_two_power ho hvo hv2 hvo2, mul_one]
    exact hv
  · exact Subgroup.mem_inf.mpr ⟨S.W_le_inf_Wt hSy hWt hw,
      Subgroup.mem_centralizer_singleton_iff.mpr (S.t_comm_W hw).symm⟩

theorem commutator_inf_Wt : ⁅Sy ⊓ Wt, zpowers t⁆ = W := by
  have hdisj : Disjoint O W := S.disjoint_O_of_isPGroup S.isPGroup_W
  have hPO : Sy ⊓ Wt ≤ normalizer (O : Set G) := fun x hx =>
    Subgroup.mem_normalizer_fintype fun o ho =>
      S.O_norm x (hSy.le (Subgroup.mem_inf.mp hx).1) o ho
  have hpow : ∀ k : ℤ, t ^ k = 1 ∨ t ^ k = t := by
    intro k
    have h2 : t ^ (2 : ℤ) = 1 := (zpow_two t).trans S.t_sq
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  refine le_antisymm (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_) (fun v hv => ?_)
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
    rcases hpow k with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact W.one_mem
    · rw [hk, ← commutatorElement_inv]
      exact W.inv_mem (S.commutator_t_mem_W (hSy.le (Subgroup.mem_inf.mp hg₁).1))
  · obtain ⟨w, hwWt, hwO⟩ := hWt.comm_onto v hv
    obtain ⟨o, ho, w₂, hw₂, rfl⟩ :=
      S.eq_mul_of_card (Z := Wt) (P := Sy ⊓ Wt) (k := 8) hWt.O_le inf_le_right
        (S.card_inf_Wt hSy hWt) hWt.card hPO w hwWt
    have hc := S.commutator_t_mem_W (hSy.le (Subgroup.mem_inf.mp hw₂).1)
    have hcE : t * w₂ * t⁻¹ * w₂⁻¹ ∈ W ⊔ zpowers t := Subgroup.mem_sup_left hc
    have ht : o * t = t * o := S.O_comm ho (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hcomm : t * (o * w₂) * t⁻¹ * (o * w₂)⁻¹ = t * w₂ * t⁻¹ * w₂⁻¹ :=
      calc t * (o * w₂) * t⁻¹ * (o * w₂)⁻¹
          = (t * o) * w₂ * t⁻¹ * w₂⁻¹ * o⁻¹ := by group
        _ = (o * t) * w₂ * t⁻¹ * w₂⁻¹ * o⁻¹ := by rw [ht]
        _ = o * (t * w₂ * t⁻¹ * w₂⁻¹) * o⁻¹ := by group
        _ = t * w₂ * t⁻¹ * w₂⁻¹ := by rw [S.O_comm ho hcE, mul_inv_cancel_right]
    rw [hcomm] at hwO
    have h1 : v⁻¹ * (t * w₂ * t⁻¹ * w₂⁻¹) = 1 :=
      Subgroup.disjoint_def.mp hdisj hwO (W.mul_mem (W.inv_mem hv) hc)
    have h2 : v = t * w₂ * t⁻¹ * w₂⁻¹ := inv_mul_eq_one.mp h1
    have h3 : ⁅w₂, t⁆⁻¹ ∈ ⁅Sy ⊓ Wt, zpowers t⁆ :=
      Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hw₂ (Subgroup.mem_zpowers t))
    rw [commutatorElement_inv] at h3
    rw [h2]
    exact h3

theorem Sy_inf_centralizer_W : Sy ⊓ centralizer (W : Set G) = (Sy ⊓ Wt) ⊔ zpowers t := by
  have ht1 : t ≠ 1 := fun h => S.t_not_mem (h ▸ W.one_mem)
  have htSy : t ∈ Sy := S.E_le_sylow hSy (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hpow : ∀ k : ℤ, t ^ k = 1 ∨ t ^ k = t := by
    intro k
    have h2 : t ^ (2 : ℤ) = 1 := (zpow_two t).trans S.t_sq
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  have hle : (Sy ⊓ Wt) ⊔ zpowers t ≤ Sy ⊓ X :=
    sup_le (inf_le_inf_left Sy hWt.le_X)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨htSy, S.t_mem_X⟩))
  have hnormal : zpowers t ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h := (normal_inf_Wt hSy hWt).conj_mem ⟨x, (Subgroup.mem_inf.mp hx).1⟩
      (Subgroup.mem_subgroupOf.mpr hx) ⟨t, htSy⟩
    exact Subgroup.mem_subgroupOf.mp h
  have hdisj : Disjoint (Sy ⊓ Wt) (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hx hxt
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
    rcases hpow k with hk | hk
    · exact hk
    · rw [hk] at hx
      exact absurd hx (t_not_mem_inf_Wt hWt)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact S.t_sq) ht1
  have hcard : Nat.card ↥((Sy ⊓ Wt) ⊔ zpowers t) = 2 ^ 9 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormal hdisj,
      S.card_inf_Wt hSy hWt, Nat.card_zpowers, hord]
    norm_num
  rw [S.inf_centralizer_W_eq hSy]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, S.card_inf_X hSy])).symm

theorem card_fix_inf_Wt (F : ActionFacts A W) :
    ∀ s ∈ Sy, s ∉ (Sy ⊓ Wt) ⊔ zpowers t →
      Nat.card ↥((Sy ⊓ Wt) ⊓ centralizer ({s} : Set G)) ≤ 16 := by
  intro s hs hsW₂
  have hSyN : Sy ≤ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G) := hSy.le
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    L34.comm_of_isElemAbelian S.W_elem ha hb
  have hW₂ab : ∀ a ∈ Sy ⊓ Wt, ∀ b ∈ Sy ⊓ Wt, a * b = b * a := fun a ha b hb =>
    L34.comm_of_isElemAbelian (S.elem_inf_Wt hSy hWt) ha hb
  have hWW₂ : W ≤ Sy ⊓ Wt := S.W_le_inf_Wt hSy hWt
  obtain ⟨y, hy, hx⟩ := S.exists_cent_t hSy s hs
  obtain ⟨x, hxdef⟩ : ∃ x, x = y⁻¹ * s := ⟨_, rfl⟩
  rw [← hxdef] at hx
  have hsx : s = y * x := by rw [hxdef, mul_inv_cancel_left]
  have hyW : ∀ w ∈ W, y * w = w * y := fun w hw =>
    mul_inv_eq_iff_eq_mul.mp (S.X_cent y (Subgroup.mem_inf.mp hy).2 w hw)
  have hxSy : x ∈ Sy := by
    rw [hxdef]
    exact Sy.mul_mem (Sy.inv_mem (Subgroup.mem_inf.mp hy).1) hs
  have hxA : x ∈ normalizer (A : Set G) := S.cent_t hx
  have hxW : x ∈ normalizer (W : Set G) := S.norm_le (hSyN hxSy)
  have hxWA : x ∉ W ⊔ centralizer (A : Set G) := by
    intro hxWA
    apply hsW₂
    rw [← S.Sy_inf_centralizer_W hSy hWt]
    refine Subgroup.mem_inf.mpr ⟨hs, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hxw : x * w = w * x := mem_centralizer_of_mem_sup S.W_le_A hWab hxWA w hw
    rw [hsx, ← mul_assoc, ← hyW w hw, mul_assoc, ← hxw, ← mul_assoc]
  have hfix := F.fix x (Subgroup.mem_inf.mpr ⟨hxA, hxW⟩) hxWA
  have hVeq : W ⊓ centralizer ({s} : Set G) = W ⊓ centralizer ({x} : Set G) := by
    ext w
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun hw => ?_
    have hyc : Commute y w := hyW w hw
    constructor
    · intro h
      rw [hxdef]
      exact (hyc.symm.inv_right.mul_right (show Commute w s from h)).eq
    · intro h
      rw [hsx]
      exact (hyc.symm.mul_right (show Commute w x from h)).eq
  have hV : ∀ z ∈ (Sy ⊓ Wt) ⊓ centralizer ({s} : Set G),
      t * z * t⁻¹ * z⁻¹ ∈ W ⊓ centralizer ({s} : Set G) := by
    intro z hz
    obtain ⟨hzW₂, hzs⟩ := Subgroup.mem_inf.mp hz
    have hzW : t * z * t⁻¹ * z⁻¹ ∈ W :=
      S.commutator_t_mem_W (hSyN (Subgroup.mem_inf.mp hzW₂).1)
    refine Subgroup.mem_inf.mpr ⟨hzW, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨w₀, hw₀, hsw₀⟩ := S.conj_t s (hSyN hs)
    have hszs : s * z * s⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hzs
      rw [← hzs, mul_inv_cancel_right]
    have hw₀z : w₀ * z * w₀⁻¹ = z := by
      rw [hW₂ab w₀ (hWW₂ hw₀) z hzW₂, mul_inv_cancel_right]
    have hc : s * (t * z * t⁻¹ * z⁻¹) * s⁻¹ = t * z * t⁻¹ * z⁻¹ :=
      calc s * (t * z * t⁻¹ * z⁻¹) * s⁻¹
          = (s * t * s⁻¹) * (s * z * s⁻¹) * (s * t * s⁻¹)⁻¹ * (s * z * s⁻¹)⁻¹ := by group
        _ = (t * w₀) * z * (t * w₀)⁻¹ * z⁻¹ := by rw [hsw₀, hszs]
        _ = t * (w₀ * z * w₀⁻¹) * t⁻¹ * z⁻¹ := by group
        _ = t * z * t⁻¹ * z⁻¹ := by rw [hw₀z]
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  have hmul : ∀ z ∈ (Sy ⊓ Wt) ⊓ centralizer ({s} : Set G),
      ∀ z' ∈ (Sy ⊓ Wt) ⊓ centralizer ({s} : Set G),
        t * (z * z') * t⁻¹ * (z * z')⁻¹ = (t * z * t⁻¹ * z⁻¹) * (t * z' * t⁻¹ * z'⁻¹) := by
    intro z hz z' hz'
    have hzW₂ := (Subgroup.mem_inf.mp hz).1
    have hdz' : t * z' * t⁻¹ * z'⁻¹ ∈ Sy ⊓ Wt :=
      hWW₂ (S.commutator_t_mem_W (hSyN (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hz').1).1))
    have hcomm := hW₂ab z hzW₂ _ hdz'
    calc t * (z * z') * t⁻¹ * (z * z')⁻¹
        = (t * z * t⁻¹ * z⁻¹) * (z * (t * z' * t⁻¹ * z'⁻¹) * z⁻¹) := by group
      _ = (t * z * t⁻¹ * z⁻¹) * (t * z' * t⁻¹ * z'⁻¹) := by rw [hcomm, mul_inv_cancel_right]
  have hker : ∀ z ∈ (Sy ⊓ Wt) ⊓ centralizer ({s} : Set G), t * z * t⁻¹ * z⁻¹ = 1 →
      z ∈ W ⊓ centralizer ({s} : Set G) := by
    intro z hz hd
    obtain ⟨hzW₂, hzs⟩ := Subgroup.mem_inf.mp hz
    have htz : t * z = z * t := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hd)
    have hzW : z ∈ W := by
      rw [← S.inf_Wt_inf_centralizer_t hSy hWt]
      exact Subgroup.mem_inf.mpr ⟨hzW₂, Subgroup.mem_centralizer_singleton_iff.mpr htz.symm⟩
    exact Subgroup.mem_inf.mpr ⟨hzW, hzs⟩
  have hcard := card_le_mul_self_of_mul_map ((Sy ⊓ Wt) ⊓ centralizer ({s} : Set G))
    (W ⊓ centralizer ({s} : Set G)) (fun z => t * z * t⁻¹ * z⁻¹) hV hmul hker
  rw [hVeq] at hcard
  exact hcard.trans (Nat.mul_le_mul hfix hfix)

omit hWt in
theorem relIndex_centralizer_le_four (F : ActionFacts A W) :
    ∀ B : Subgroup G, B ≤ Sy → IsElemAbelian 2 B →
      (centralizer (W : Set G)).relIndex B ≤ 4 := by
  intro B hB hBe
  have hSyN : Sy ≤ normalizer (W : Set G) := hSy.le.trans S.norm_le
  have hBN : B ≤ normalizer (W : Set G) := hB.trans hSyN
  set E' : Subgroup G :=
    (Sy ⊓ centralizer ({t} : Set G)) ⊓ (B ⊔ centralizer (W : Set G)) with hE'
  have hE'W : E' ≤ normalizer (W : Set G) := fun x hx => hSyN hx.1.1
  have hE'A : E' ≤ normalizer (A : Set G) := fun x hx => S.cent_t hx.1.2
  have hrel : (centralizer (W : Set G)).relIndex E' ≤ 4 :=
    F.rel E' (le_inf hE'A hE'W) fun x hx y hy =>
      comm_sq_mem_centralizer_of_mem_sup hBN hBe hx.2 hy.2
  have hBE : B ≤ E' ⊔ centralizer (W : Set G) := by
    intro b hb
    obtain ⟨y, hy, hyb⟩ := S.exists_cent_t hSy b (hB hb)
    have hyK : y ∈ centralizer (W : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      exact (mul_inv_eq_iff_eq_mul.mp (S.X_cent y hy.2 w hw)).symm
    have hs : y⁻¹ * b ∈ E' :=
      ⟨⟨Sy.mul_mem (Sy.inv_mem hy.1) (hB hb), hyb⟩,
        mul_mem (mem_sup_right (inv_mem hyK)) (mem_sup_left hb)⟩
    have hb' : b = y * (y⁻¹ * b) := by group
    rw [hb']
    exact mul_mem (mem_sup_right hyK) (mem_sup_left hs)
  exact (relIndex_le_of_le_sup (hE'W.trans (normalizer_le_normalizer_centralizer_W W)) hBE).trans
    hrel

theorem relIndex_inf_Wt (F : ActionFacts A W) :
    ∀ B : Subgroup G, B ≤ Sy → IsElemAbelian 2 B → (Sy ⊓ Wt).relIndex B ≤ 8 := by
  intro B hB hBe
  have hY := S.Sy_inf_centralizer_W hSy hWt
  have hYcard : Nat.card ↥(Sy ⊓ centralizer (W : Set G)) = 2 ^ 9 := by
    rw [S.inf_centralizer_W_eq hSy]
    exact S.card_inf_X hSy
  have hW₂card := S.card_inf_Wt hSy hWt
  have hW₂Y : Sy ⊓ Wt ≤ Sy ⊓ centralizer (W : Set G) := hY ▸ le_sup_left
  have h2 : (Sy ⊓ Wt).relIndex (Sy ⊓ centralizer (W : Set G)) = 2 := by
    have h := Subgroup.relIndex_mul_card (Sy ⊓ Wt) (Sy ⊓ centralizer (W : Set G))
    rw [inf_eq_left.mpr hW₂Y, hYcard, hW₂card] at h
    omega
  have h3 : (Sy ⊓ centralizer (W : Set G)).relIndex B = (centralizer (W : Set G)).relIndex B := by
    unfold Subgroup.relIndex
    congr 1
    ext b
    simp only [mem_subgroupOf, mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hB b.2, h⟩⟩
  calc (Sy ⊓ Wt).relIndex B
      ≤ (Sy ⊓ centralizer (W : Set G)).relIndex B *
          (Sy ⊓ Wt).relIndex (Sy ⊓ centralizer (W : Set G)) := relIndex_le_mul hW₂Y
    _ = (centralizer (W : Set G)).relIndex B * 2 := by rw [h3, h2]
    _ ≤ 4 * 2 := Nat.mul_le_mul_right 2 (S.relIndex_centralizer_le_four hSy F B hB hBe)
    _ = 8 := by norm_num

end Wt

end IsSetting25

end CFSG.OddStandard.Seitz77
