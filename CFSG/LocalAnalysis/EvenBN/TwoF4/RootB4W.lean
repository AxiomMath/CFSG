module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem sylowP_inf_centralizer_torusH (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedPosUnipotent K a ⊓ centralizer (torusH K a : Set (ModGL F4.tag K)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgP, hgc⟩ := mem_inf.1 hg
  have h5 : g ∈ rootV K a .i5 := by
    rw [← sylowP_inf_centralizer_torusHi ha hK (i := .i5) rfl]
    exact mem_inf.2 ⟨hgP, centralizer_le (SetLike.coe_subset_coe.2 (torusHi_le_torusH .i5)) hgc⟩
  have h1 : g ∈ rootV K a .i1 := by
    rw [← sylowP_inf_centralizer_torusHi ha hK (i := .i1) rfl]
    exact mem_inf.2 ⟨hgP, centralizer_le (SetLike.coe_subset_coe.2 (torusHi_le_torusH .i1)) hgc⟩
  have h5' : g ∈ (rootV K a .i5 : Set (ModGL F4.tag K)) := h5
  have h1' : g ∈ (rootV K a .i1 : Set (ModGL F4.tag K)) := h1
  rw [coe_rootV hK] at h5' h1'
  obtain ⟨x, hx, rfl⟩ := h5'
  obtain ⟨y, hy, hyx⟩ := h1'
  have hxy := (bijOn_sylowVec (m := a) (K := K) hK).injOn (Set.mem_univ _) (Set.mem_univ _) hyx
  have hx0 : x = 0 := by
    funext n
    by_cases hn : n ∈ Idx.i5.coords
    · have hn1 : n ∉ Idx.i1.coords := by revert hn; revert n; decide
      rw [← hxy]
      exact hy n hn1
    · exact hx n hn
  rw [mem_bot, hx0]
  have := (rootElt_eq_sylowVec (a := a) (K := K) .i7 0).symm
  rw [rootElt_zero] at this
  rw [← this]
  simp

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem eq_one_of_mem_P_of_mem_centralizer_H {x : G} (hxP : x ∈ h.P)
    (hxH : x ∈ centralizer (h.H : Set G)) : x = 1 := by
  have hxc : x ∈ h.pull (centralizer (torusH h.K h.a : Set (ModGL F4.tag h.K))) := by
    rw [h.pull_centralizer_subgroup (torusH_le_reeGamma h.card_K)]
    exact mem_inf.2 ⟨h.P_le_L hxP, hxH⟩
  have hmem : x ∈ h.pull (F4.reeFixedPosUnipotent h.K h.a ⊓
      centralizer (torusH h.K h.a : Set (ModGL F4.tag h.K))) := by
    rw [h.pull_inf]
    exact ⟨hxP, hxc⟩
  rw [sylowP_inf_centralizer_torusH h.one_le_a h.card_K, h.pull_bot] at hmem
  exact (mem_bot).1 hmem

theorem odd_card_H : Odd (Nat.card h.H) := by
  rw [h.card_H]
  exact (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩)
    odd_one).pow

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem comm_W_mem_W12 {x y : G} (hx : x ∈ d.W) (hy : y ∈ d.W) : ⁅x, y⁆ ∈ d.W12 := by
  have hxx := d.bender.mul_self_mem x hx
  have hyy := d.bender.mul_self_mem y hy
  have hxy := d.bender.mul_self_mem (x * y) (mul_mem hx hy)
  have hc : y⁻¹ * (x * x)⁻¹ * y = (x * x)⁻¹ := by
    have := (mem_zIn.1 hxx).1 y hy
    have e1 : y⁻¹ * (x * x) * y = x * x := by
      rw [mul_assoc, ← this]
      group
    calc y⁻¹ * (x * x)⁻¹ * y = (y⁻¹ * (x * x) * y)⁻¹ := by group
      _ = (x * x)⁻¹ := by rw [e1]
  have e : ⁅x, y⁆ = x * y * (x * y) * (y⁻¹ * (x * x)⁻¹ * y) * (y * y)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, hc]
  exact mul_mem (mul_mem hxy (inv_mem hxx)) (inv_mem hyy)

theorem comm_t_mem_V5_sup_W12 {w : G} (hw : w ∈ d.W) : ⁅w, h.t⁆ ∈ h.V .i5 ⊔ d.W12 := by
  have h1 := d.bender.comm_mem w⁻¹ (inv_mem hw)
  have e : ⁅w, h.t⁆ = w⁻¹⁻¹ * (h.t⁻¹ * w⁻¹ * h.t) := by
    rw [h.t_inv, commutatorElement_def, h.t_inv, inv_inv]
    group
  rw [e]
  have hle : ⁅d.W, d.W⁆ ⊔ h.V .i5 ≤ h.V .i5 ⊔ d.W12 :=
    sup_le ((commutator_le).2 fun x hx y hy => mem_sup_right (d.comm_W_mem_W12 hx hy))
      le_sup_left
  exact hle h1

theorem eq_one_of_mem_V5_sup_W12_of_mem_centralizer_H {u : G} (hu : u ∈ h.V .i5 ⊔ d.W12)
    (huH : u ∈ centralizer (h.H : Set G)) : u = 1 := by
  obtain ⟨v, hv, z, hz, rfl⟩ := exists_mul_of_mem_sup_zIn d.bender.le hu
  have htH : h.t ∈ centralizer (h.H : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 h.H_le_L) h.htL
  have hvt : v * h.t = h.t * v := h.mul_t_comm (h.pull_le_L _ hv)
  have hzt : ⁅z, h.t⁆ ∈ h.V .i12 := d.comm_t_W12_mem hz
  have hvz : ⁅v * z, h.t⁆ = v * ⁅z, h.t⁆ * v⁻¹ := by
    simp only [commutatorElement_def]
    calc v * z * h.t * (v * z)⁻¹ * h.t⁻¹ = v * z * h.t * z⁻¹ * (v⁻¹ * h.t⁻¹) := by group
      _ = v * z * h.t * z⁻¹ * (h.t⁻¹ * v⁻¹) := by
        rw [show v⁻¹ * h.t⁻¹ = (h.t * v)⁻¹ by group, ← hvt]
        group
      _ = v * (z * h.t * z⁻¹ * h.t⁻¹) * v⁻¹ := by group
  have hcomm : v * ⁅z, h.t⁆ * v⁻¹ = ⁅z, h.t⁆ := by
    rw [← d.W12_comm_V5 (d.V12_le_W12 hzt) hv, mul_inv_cancel_right]
  have hc1 : ⁅v * z, h.t⁆ = 1 := by
    refine h.eq_one_of_mem_P_of_mem_centralizer_H (h.V_le_P .i12 ?_) ?_
    · rw [hvz, hcomm]
      exact hzt
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem huH htH) (inv_mem huH)) (inv_mem htH)
  rw [hvz, hcomm] at hc1
  have hz12 : z ∈ h.V .i12 := d.mem_V12_of_commute hz (commutatorElement_eq_one_iff_mul_comm.1 hc1)
  exact h.eq_one_of_mem_P_of_mem_centralizer_H
    (mul_mem (h.V_le_P .i5 hv) (h.V_le_P .i12 hz12)) huH

theorem eq_one_of_mem_W_of_mem_centralizer_H {w : G} (hw : w ∈ d.W)
    (hwH : w ∈ centralizer (h.H : Set G)) : w = 1 := by
  have htH : h.t ∈ centralizer (h.H : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 h.H_le_L) h.htL
  have h1 := d.eq_one_of_mem_V5_sup_W12_of_mem_centralizer_H (d.comm_t_mem_V5_sup_W12 hw) (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hwH htH) (inv_mem hwH)) (inv_mem htH))
  have hw5 := d.mem_V5_of_commute hw (commutatorElement_eq_one_iff_mul_comm.1 h1)
  exact h.eq_one_of_mem_P_of_mem_centralizer_H (h.V_le_P .i5 hw5) hwH

theorem H_le_normalizer_W : h.H ≤ normalizer (d.W : Set G) := by
  have key : ∀ {b : G}, b ∈ h.H → ∀ w ∈ d.W, b * w * b⁻¹ ∈ d.W := fun {b} hb w hw =>
    d.conj_mem_W b (mem_centralizer_iff.2 fun c hc => h.H_comm (h.Ht_le_H .i5 hc) hb)
      (h.mul_t_comm (h.H_le_L hb)) (h.H_le_normalizer_V .i5 hb) w hw
  intro b hb
  refine mem_normalizer_of_conj_mem (key hb) fun w hw => ?_
  have := key (inv_mem hb) w hw
  rwa [inv_inv] at this

theorem V5_le_B4 : h.V .i5 ≤ d.B4 :=
  (h.V_le_S₄ (k := .i5) (by decide)).trans (d.S₄_le_Q4.trans d.Q4_le_B4)

theorem B4_inf_CH5_le_W : d.B4 ⊓ h.CH .i5 ≤ d.W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := d.B4 ⊓ h.CH .i5 with hYdef
  have htK : h.t ∈ h.Kp := h.P_sup_Tsyl_le_J_Kp.2 (mem_sup_right h.t_mem_Tsyl)
  have hY2 : IsPGroup 2 Y := d.isPGroup_B4.to_le inf_le_left
  have htY : h.t ∈ normalizer (Y : Set G) :=
    mem_normalizer_inf (d.Kp_le_normalizer_B4 htK) (le_normalizer (h.t_mem_CH .i5))
  have hYt2 : IsPGroup 2 (Y ⊔ zpowers h.t : Subgroup G) :=
    hY2.to_sup_of_normal_left' h.isPGroup_zpowers_t (zpowers_le.2 htY)
  have hV5Y : h.V .i5 ≤ Y := le_inf d.V5_le_B4 (h.V_le_centralizer_Ht rfl)
  have hle := d.le_W_sup (Y ⊔ zpowers h.t) (sup_le inf_le_right (zpowers_le.2 (h.t_mem_CH .i5)))
    hYt2 (sup_le_sup_right hV5Y _)
  have hWN : d.W ⊔ zpowers h.t ≤ normalizer (d.W : Set G) :=
    sup_le le_normalizer (zpowers_le.2 d.bender.mem_normalizer)
  intro y hy
  obtain ⟨w, hw, hyw | hyw⟩ := exists_eq_or_eq_mul_of_mem_sup d.bender.mul_self
    d.bender.mem_normalizer (hle (mem_sup_left hy))
  · rw [hyw]
    exact hw
  exfalso
  have hHCH : h.H ≤ normalizer (h.CH .i5 : Set G) := fun b hb =>
    le_normalizer (mem_centralizer_iff.2 fun c hc => h.H_comm (h.Ht_le_H .i5 hc) hb)
  have hHY : h.H ≤ normalizer (Y : Set G) := fun b hb =>
    mem_normalizer_inf (d.Kp_le_normalizer_B4 (h.H_le_Kp hb)) (hHCH hb)
  let : MulDistribMulAction h.H Y := Subgroup.conjMulDistribMulActionOfLeNormalizer h.H Y hHY
  set N : Subgroup Y := (Y ⊓ d.W).subgroupOf Y with hNdef
  have hYN : Y ≤ normalizer ((Y ⊓ d.W : Subgroup G) : Set G) := fun z hz =>
    mem_normalizer_inf (le_normalizer hz) (hWN (hle (mem_sup_left hz)))
  have : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYN
  have hNinv : CFSG.IsInvariant h.H Y N :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun b z hz => by
      rw [mem_subgroupOf] at hz ⊢
      exact (mem_normalizer_iff.1 (mem_normalizer_inf (hHY b.2) (d.H_le_normalizer_W b.2)) z).1 hz
  have hN2 : IsPGroup 2 N :=
    (hY2.to_le (inf_le_left : Y ⊓ d.W ≤ Y)).of_equiv (subgroupOfEquivOfLe inf_le_left).symm
  have hNsolv : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card h.H) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN2
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 h.odd_card_H)
  have hbt : ∀ b ∈ h.H, b * h.t = h.t * b := fun b hb => h.mul_t_comm (h.H_le_L hb)
  have hcoset : ∀ b : h.H, (⟨y, hy⟩ : Y)⁻¹ * (b • (⟨y, hy⟩ : Y)) ∈ N := by
    intro b
    have hsmul : ((b • (⟨y, hy⟩ : Y) : Y) : G) = (b : G) * y * (b : G)⁻¹ := rfl
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hsmul]
    refine mem_inf.2 ⟨mul_mem (inv_mem hy) ((mem_normalizer_iff.1 (hHY b.2) y).1 hy), ?_⟩
    have hbw : (b : G) * w * (b : G)⁻¹ ∈ d.W :=
      (mem_normalizer_iff.1 (d.H_le_normalizer_W b.2) w).1 hw
    have e : y⁻¹ * ((b : G) * y * (b : G)⁻¹) =
        h.t⁻¹ * (w⁻¹ * ((b : G) * w * (b : G)⁻¹)) * h.t := by
      rw [hyw]
      have hbt' := hbt b b.2
      calc (w * h.t)⁻¹ * ((b : G) * (w * h.t) * (b : G)⁻¹) =
          h.t⁻¹ * w⁻¹ * ((b : G) * w * (b : G)⁻¹) * ((b : G) * h.t * (b : G)⁻¹) := by group
        _ = h.t⁻¹ * (w⁻¹ * ((b : G) * w * (b : G)⁻¹)) * h.t := by
          rw [hbt', mul_inv_cancel_right]
          group
    rw [e]
    exact d.bender.conj_mem _ (mul_mem (inv_mem hw) hbw)
  obtain ⟨c, hc, hcN⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed N hNinv hNsolv hcop
    ⟨y, hy⟩ hcoset
  have hcfix : ∀ b ∈ h.H, b * (c : G) * b⁻¹ = c := fun b hb => congrArg Subtype.val (hc ⟨b, hb⟩)
  have hcn : (c : G)⁻¹ * y ∈ d.W := by
    have := (mem_subgroupOf.1 hcN).2
    simpa using this
  have hct : (c : G) * h.t⁻¹ ∈ d.W := by
    have e : (c : G) * h.t⁻¹ = w * (h.t * ((c : G)⁻¹ * y)⁻¹ * h.t⁻¹) := by
      rw [hyw]
      group
    rw [e]
    refine mul_mem hw ?_
    have := (mem_normalizer_iff.1 d.bender.mem_normalizer _).1 (inv_mem hcn)
    exact this
  have hctH : (c : G) * h.t⁻¹ ∈ centralizer (h.H : Set G) := mem_centralizer_iff.2 fun b hb => by
    have h1 := hcfix b hb
    have h2 : b * h.t⁻¹ = h.t⁻¹ * b := by
      calc b * h.t⁻¹ = h.t⁻¹ * (h.t * b) * h.t⁻¹ := by group
        _ = h.t⁻¹ * (b * h.t) * h.t⁻¹ := by rw [hbt b hb]
        _ = h.t⁻¹ * b := by group
    calc b * ((c : G) * h.t⁻¹) = b * (c : G) * b⁻¹ * (b * h.t⁻¹) := by group
      _ = (c : G) * (h.t⁻¹ * b) := by rw [h1, h2]
      _ = (c : G) * h.t⁻¹ * b := by group
  have h1 := d.eq_one_of_mem_W_of_mem_centralizer_H hct hctH
  have hct' : (c : G) = h.t := by
    calc (c : G) = (c : G) * h.t⁻¹ * h.t := by group
      _ = h.t := by rw [h1, one_mul]
  exact d.t_not_mem_B4 (hct' ▸ (c.2 : (c : G) ∈ Y).1)

theorem mem_W12_of_mem_B2_of_mem_V5_sup_W12 {z : G} (hzB : z ∈ d.B2)
    (hz : z ∈ h.V .i5 ⊔ d.W12) : z ∈ d.W12 := by
  obtain ⟨v, hv, z', hz', rfl⟩ := exists_mul_of_mem_sup_zIn d.bender.le hz
  have hz'B : z' ∈ d.B2 := mem_sup_right (d.W12_le_B1 hz')
  have hvB : v ∈ d.B2 := by
    have e : v = v * z' * z'⁻¹ := by group
    rw [e]
    exact mul_mem hzB (inv_mem hz'B)
  have hvS := d.mem_S₂_of_mem_B2 hvB
    (commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ hv)))
  have hv12 : v ∈ h.V .i12 := h.mem_V_of_mem_R₁_of_mem_CH (i := .i5) rfl (by decide)
    (h.S₂_le_R₁ hvS) (h.V_le_centralizer_Ht rfl hv)
  exact mul_mem (d.V12_le_W12 hv12) hz'

theorem exists_W_B4_comm_t {u : G} (hu : u ∈ h.V .i5) :
    ∃ c ∈ d.W, c ∈ d.B4 ∧ u⁻¹ * ⁅c, h.t⁆ ∈ d.W12 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, β, hβ, hux⟩ := d.exists_B4_comm_t (h.V_le_S₄ (k := .i5) (by decide) hu)
  have hHK : ∀ b ∈ h.Ht .i5, b ∈ h.Kp := fun b hb => h.H_le_Kp (h.Ht_le_H .i5 hb)
  have hHB : h.Ht .i5 ≤ normalizer (d.B4 : Set G) := fun b hb => d.Kp_le_normalizer_B4 (hHK b hb)
  let : MulDistribMulAction (h.Ht .i5) d.B4 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (h.Ht .i5) d.B4 hHB
  set N : Subgroup d.B4 := d.Q4.subgroupOf d.B4 with hNdef
  have hBQ : d.B4 ≤ normalizer (d.Q4 : Set G) := fun z hz =>
    mem_normalizer_of_conj_mem (fun q hq => d.conj_B4_mem_Q4 hz hq) fun q hq => by
      have := d.conj_B4_mem_Q4 (inv_mem hz) hq
      rwa [inv_inv] at this
  have : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBQ
  have hKQ : h.Kp ≤ normalizer (d.Q4 : Set G) := fun k hk => by
    have h4 := h.Kp_le_normalizer_S₂_S₃_S₄.2.2 hk
    have hB := d.Kp_le_normalizer_B2 hk
    have key : ∀ {k : G}, k ∈ normalizer (h.S₄ : Set G) → k ∈ normalizer (d.B2 : Set G) →
        ∀ q ∈ d.Q4, k * q * k⁻¹ ∈ d.Q4 := fun {k} h4 hB q hq => by
      have hle : d.Q4 ≤ d.Q4.comap (MulAut.conj k).toMonoidHom :=
        sup_le (fun v hv => d.S₄_le_Q4 ((mem_normalizer_iff.1 h4 v).1 hv))
          (fun b hb => d.B2_le_Q4 ((mem_normalizer_iff.1 hB b).1 hb))
      exact hle hq
    refine mem_normalizer_of_conj_mem (key h4 hB) fun q hq => ?_
    have := key (inv_mem h4) (inv_mem hB) q hq
    rwa [inv_inv] at this
  have hNinv : CFSG.IsInvariant (h.Ht .i5) d.B4 N :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun b z hz => by
      rw [mem_subgroupOf] at hz ⊢
      exact (mem_normalizer_iff.1 (hKQ (hHK b b.2)) z).1 hz
  have hN2 : IsPGroup 2 N := d.isPGroup_Q4.of_equiv (subgroupOfEquivOfLe d.Q4_le_B4).symm
  have hNsolv : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (h.Ht .i5)) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN2
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 (h.odd_card_Ht .i5))
  have hxt : ⁅x, h.t⁆ = u * β⁻¹ := by rw [hux]; group
  have hcoset : ∀ b : h.Ht .i5, (⟨x, hx⟩ : d.B4)⁻¹ * (b • (⟨x, hx⟩ : d.B4)) ∈ N := by
    intro b
    have hsmul : ((b • (⟨x, hx⟩ : d.B4) : d.B4) : G) = (b : G) * x * (b : G)⁻¹ := rfl
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hsmul]
    have hbK := hHK b b.2
    have hbxB : (b : G) * x * (b : G)⁻¹ ∈ d.B4 := d.conj_Kp_mem_B4 hbK hx
    refine d.inv_mul_mem_Q4_of_comm hx hbxB ?_
    have hbt : (b : G) * h.t = h.t * b := mem_centralizer_singleton_iff.1 hbK.1
    have hbu : (b : G) * u * (b : G)⁻¹ = u := h.conj_V5_eq b.2 hu
    have e1 : ⁅(b : G) * x * (b : G)⁻¹, h.t⁆ = (b : G) * ⁅x, h.t⁆ * (b : G)⁻¹ := by
      have hbt' : (b : G) * h.t * (b : G)⁻¹ = h.t := by rw [hbt, mul_inv_cancel_right]
      simp only [commutatorElement_def]
      conv_lhs => rw [← hbt']
      group
    have e2 : ⁅x, h.t⁆⁻¹ * ((b : G) * ⁅x, h.t⁆ * (b : G)⁻¹) =
        β * ((b : G) * β⁻¹ * (b : G)⁻¹) := by
      rw [hxt]
      calc (u * β⁻¹)⁻¹ * ((b : G) * (u * β⁻¹) * (b : G)⁻¹) =
          β * u⁻¹ * ((b : G) * u * (b : G)⁻¹) * ((b : G) * β⁻¹ * (b : G)⁻¹) := by group
        _ = β * ((b : G) * β⁻¹ * (b : G)⁻¹) := by rw [hbu]; group
    rw [e1, e2]
    exact mul_mem hβ ((mem_normalizer_iff.1 (d.Kp_le_normalizer_B2 hbK) _).1 (inv_mem hβ))
  obtain ⟨c, hc, hcN⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed N hNinv hNsolv hcop
    ⟨x, hx⟩ hcoset
  have hcH : (c : G) ∈ h.CH .i5 := mem_centralizer_iff.2 fun b hb => by
    have := congrArg Subtype.val (hc ⟨b, hb⟩)
    have hsmul : (((⟨b, hb⟩ : h.Ht .i5) • c : d.B4) : G) = b * (c : G) * b⁻¹ := rfl
    rw [hsmul] at this
    calc b * (c : G) = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [this]
  have hcW : (c : G) ∈ d.W := d.B4_inf_CH5_le_W (mem_inf.2 ⟨c.2, hcH⟩)
  refine ⟨c, hcW, c.2, d.mem_W12_of_mem_B2_of_mem_V5_sup_W12 ?_
    (mul_mem (mem_sup_left (inv_mem hu)) (d.comm_t_mem_V5_sup_W12 hcW))⟩
  have hq : (c : G)⁻¹ * x ∈ d.Q4 := by
    have := mem_subgroupOf.1 hcN
    simpa using this
  set q := (c : G)⁻¹ * x with hqdef
  have hcN2 : (c : G) ∈ normalizer (d.B2 : Set G) := (c.2 : (c : G) ∈ d.B4).1
  have hqt : (c : G) * ⁅q, h.t⁆ * (c : G)⁻¹ ∈ d.B2 :=
    (mem_normalizer_iff.1 hcN2 _).1 (d.comm_t_mem_B2_of_mem_Q4 hq)
  have e : u⁻¹ * ⁅(c : G), h.t⁆ =
      u⁻¹ * ((c : G) * ⁅q, h.t⁆ * (c : G)⁻¹)⁻¹ * u * β⁻¹ := by
    have hx' : x = (c : G) * q := by rw [hqdef]; group
    have e0 : ⁅x, h.t⁆ = (c : G) * ⁅q, h.t⁆ * (c : G)⁻¹ * ⁅(c : G), h.t⁆ := by
      rw [hx', commutatorElement_mul_left_eq]
    have e3 : ⁅(c : G), h.t⁆ = ((c : G) * ⁅q, h.t⁆ * (c : G)⁻¹)⁻¹ * ⁅x, h.t⁆ := by
      rw [e0]
      group
    rw [e3, hxt]
    group
  rw [e]
  have huK : u ∈ h.Kp := h.S₄_le_Kp (h.V_le_S₄ (k := .i5) (by decide) hu)
  refine mul_mem ?_ (inv_mem hβ)
  have := (mem_normalizer_iff.1 (inv_mem (d.Kp_le_normalizer_B2 huK)) _).1 (inv_mem hqt)
  simpa [mul_assoc] using this

theorem W_le_B4 : d.W ≤ d.B4 := by
  intro w hw
  obtain ⟨u, hu, z, hz, hwt⟩ := exists_mul_of_mem_sup_zIn d.bender.le (d.comm_t_mem_V5_sup_W12 hw)
  obtain ⟨c, hcW, hcB, hc⟩ := d.exists_W_B4_comm_t hu
  set z' := u⁻¹ * ⁅c, h.t⁆ with hz'
  have hct : ⁅c, h.t⁆ = u * z' := by rw [hz']; group
  have hW12 : ⁅c⁻¹ * w, h.t⁆ ∈ d.W12 := by
    have e : ⁅c⁻¹ * w, h.t⁆ = c⁻¹ * (u * (z * z'⁻¹) * u⁻¹) * c⁻¹⁻¹ := by
      have e1 : ⁅c⁻¹ * w, h.t⁆ = c⁻¹ * (⁅w, h.t⁆ * ⁅c, h.t⁆⁻¹) * c⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1, hwt, hct]
      group
    rw [e]
    have hu12 : u * (z * z'⁻¹) * u⁻¹ ∈ d.W12 :=
      (mem_normalizer_iff.1 (le_normalizer_zIn d.W (d.bender.le hu)) _).1
        (mul_mem hz (inv_mem hc))
    exact (mem_normalizer_iff.1 (le_normalizer_zIn d.W (inv_mem hcW)) _).1 hu12
  have hw' : c⁻¹ * w ∈ h.V .i5 ⊔ d.W12 := by
    have h1 := d.bender.mem_of_comm (c⁻¹ * w)⁻¹ (inv_mem (mul_mem (inv_mem hcW) hw)) (by
      have e : (c⁻¹ * w)⁻¹⁻¹ * (h.t⁻¹ * (c⁻¹ * w)⁻¹ * h.t) = ⁅c⁻¹ * w, h.t⁆ := by
        rw [inv_inv, commutatorElement_def, h.t_inv]
        group
      rw [e]
      exact hW12)
    have := inv_mem h1
    rwa [inv_inv] at this
  have hle : h.V .i5 ⊔ d.W12 ≤ d.B4 := sup_le d.V5_le_B4 (d.W12_le_A1.trans d.A1_le_B4)
  have e : w = c * (c⁻¹ * w) := by group
  rw [e]
  exact mul_mem hcB (hle hw')

@[expose] def W6 : Subgroup G := d.W.map (MulAut.conj h.s).toMonoidHom

@[expose] def W2 : Subgroup G := (d.WA .i4).map (MulAut.conj h.s).toMonoidHom

theorem conj_s_mem_W6 {z : G} (hz : z ∈ d.W) : h.s * z * h.s⁻¹ ∈ d.W6 := ⟨z, hz, rfl⟩

theorem conj_s_mem_W2 {z : G} (hz : z ∈ d.WA .i4) : h.s * z * h.s⁻¹ ∈ d.W2 := ⟨z, hz, rfl⟩

theorem W6_le_B4 : d.W6 ≤ d.B4 := by
  rintro _ ⟨z, hz, rfl⟩
  exact d.conj_Kp_mem_B4 h.s_mem_Kp (d.W_le_B4 hz)

theorem W2_le_B4 : d.W2 ≤ d.B4 := by
  rintro _ ⟨z, hz, rfl⟩
  exact d.conj_Kp_mem_B4 h.s_mem_Kp (d.A1_le_B4 hz.1)

@[expose] def imIn (M : Subgroup G) (hM : M ≤ d.B4) : Subgroup G where
  carrier := {v | ∃ x ∈ M, ∃ b ∈ d.B2, v = ⁅x, h.t⁆ * b}
  mul_mem' := fun {v v'} hv hv' => by
    obtain ⟨x, hx, b, hb, rfl⟩ := hv
    obtain ⟨x', hx', b', hb', rfl⟩ := hv'
    set a := ⁅x, h.t⁆ with ha
    set a' := ⁅x', h.t⁆ with ha'
    have haQ : a ∈ d.Q4 := (hM hx).2.2.2.2
    have haQ' : a' ∈ d.Q4 := (hM hx').2.2.2.2
    set β := ⁅x, a'⁆ with hβ
    have hβB : β ∈ d.B2 := d.comm_B4_Q4_mem (hM hx) haQ'
    refine ⟨x * x', mul_mem hx hx', ⁅a⁻¹, a'⁻¹⁆ * ((a * a')⁻¹ * β⁻¹ * (a * a')⁻¹⁻¹) *
      (a'⁻¹ * b * a'⁻¹⁻¹) * b', ?_, ?_⟩
    · have hN := d.Q4_le_normalizer_B2
      exact mul_mem (mul_mem (mul_mem (d.comm_Q4_Q4_mem (inv_mem haQ) (inv_mem haQ'))
        ((mem_normalizer_iff.1 (hN (inv_mem (mul_mem haQ haQ'))) _).1 (inv_mem hβB)))
        ((mem_normalizer_iff.1 (hN (inv_mem haQ')) _).1 hb)) hb'
    · rw [commutatorElement_mul_left_eq]
      simp only [hβ, ha, ha', commutatorElement_def]
      group
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [commutatorElement_one_left, one_mul]⟩
  inv_mem' := fun {v} hv => by
    obtain ⟨x, hx, b, hb, rfl⟩ := hv
    set a := ⁅x, h.t⁆ with ha
    have haQ : a ∈ d.Q4 := (hM hx).2.2.2.2
    set γ := ⁅x⁻¹, a⁻¹⁆ with hγ
    have hγB : γ ∈ d.B2 := d.comm_B4_Q4_mem (inv_mem (hM hx)) (inv_mem haQ)
    refine ⟨x⁻¹, inv_mem hx, a * (γ⁻¹ * b⁻¹) * a⁻¹, ?_, ?_⟩
    · exact (mem_normalizer_iff.1 (d.Q4_le_normalizer_B2 haQ) _).1
        (mul_mem (inv_mem hγB) (inv_mem hb))
    · simp only [hγ, ha, commutatorElement_def]
      group

theorem B4_eq : d.B4 = d.W2 ⊔ d.W ⊔ d.W6 ⊔ d.WA .i4 ⊔ d.B3 := by
  set M := d.W2 ⊔ d.W ⊔ d.W6 ⊔ d.WA .i4 ⊔ d.B3 with hMdef
  have h2 : d.W2 ≤ M := le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have h5 : d.W ≤ M := le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have h6 : d.W6 ≤ M := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have h8 : d.WA .i4 ≤ M := le_sup_right.trans le_sup_left
  have h3 : d.B3 ≤ M := le_sup_right
  have hMB : M ≤ d.B4 := sup_le (sup_le (sup_le (sup_le d.W2_le_B4 d.W_le_B4) d.W6_le_B4)
    (fun _ hx => d.A1_le_B4 hx.1)) d.B3_le_B4
  have hs2 : h.s * h.s = 1 := h.r_mul_self_s_mul_self.2
  have hsK := h.s_mem_Kp
  have hst : h.s * h.t * h.s⁻¹ = h.t := h.s_conj_t'
  have hcs : ∀ y : G, ⁅h.s * y * h.s⁻¹, h.t⁆ = h.s * ⁅y, h.t⁆ * h.s⁻¹ := fun y => by
    simp only [commutatorElement_def]
    conv_lhs => rw [← hst]
    group
  have hS3 : h.S₃ ≤ d.imIn M hMB := fun v hv => by
    obtain ⟨w, hw, hwt⟩ := d.exists_B3_comm_t hv
    exact ⟨w, h3 (d.B3_eq ▸ hw), 1, one_mem _, by rw [mul_one, hwt]⟩
  have hV8 : h.V .i8 ≤ d.imIn M hMB := fun v hv => by
    obtain ⟨w, hw, hwt⟩ := d.exists_WA_comm_t (i := .i4) (h.V_le_R₁ (by decide))
      (h.V_le_CH rfl (Or.inr rfl)) hv
    exact ⟨w, h8 hw, 1, one_mem _, by rw [mul_one, hwt]⟩
  have hV2 : h.V .i2 ≤ d.imIn M hMB := fun v hv => by
    have hv8 : h.s * v * h.s⁻¹ ∈ h.V .i8 := h.conj_s_mem_V (i := .i2) (by decide) hv
    obtain ⟨w, hw, hwt⟩ := d.exists_WA_comm_t (i := .i4) (h.V_le_R₁ (by decide))
      (h.V_le_CH rfl (Or.inr rfl)) hv8
    refine ⟨h.s * w * h.s⁻¹, h2 (d.conj_s_mem_W2 hw), 1, one_mem _, ?_⟩
    rw [mul_one, hcs, hwt, h.s_inv]
    calc v = (h.s * h.s) * v * (h.s * h.s) := by rw [hs2]; group
      _ = h.s * (h.s * v * h.s) * h.s := by group
  have hV5 : h.V .i5 ≤ d.imIn M hMB := fun u hu => by
    obtain ⟨c, hcW, -, hc⟩ := d.exists_W_B4_comm_t hu
    refine ⟨c, h5 hcW, (u⁻¹ * ⁅c, h.t⁆)⁻¹, inv_mem (mem_sup_right (d.W12_le_B1 hc)), ?_⟩
    group
  have hV6 : h.V .i6 ≤ d.imIn M hMB := fun v hv => by
    have hv5 : h.s * v * h.s⁻¹ ∈ h.V .i5 := h.conj_s_mem_V (i := .i6) (by decide) hv
    obtain ⟨c, hcW, -, hc⟩ := d.exists_W_B4_comm_t hv5
    have hz : h.s * ((h.s * v * h.s⁻¹)⁻¹ * ⁅c, h.t⁆) * h.s⁻¹ ∈ d.B2 :=
      mem_sup_right (d.W11_le_B1 (d.conj_s_mem_W11 hc))
    refine ⟨h.s * c * h.s⁻¹, h6 (d.conj_s_mem_W6 hcW),
      (h.s * ((h.s * v * h.s⁻¹)⁻¹ * ⁅c, h.t⁆) * h.s⁻¹)⁻¹, inv_mem hz, ?_⟩
    rw [hcs, h.s_inv]
    calc v = h.s * h.s * v := by rw [hs2, one_mul]
      _ = _ := by group
  have hS4 : h.S₄ ≤ d.imIn M hMB := h.pull_rootJoin_le fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hV2
    · exact hV5
    · exact hV6
    · exact hV8
    · exact (h.V_le_S₃ (k := .i7) (by decide)).trans hS3
    · exact (h.V_le_S₃ (k := .i9) (by decide)).trans hS3
    · exact (h.V_le_S₃ (k := .i10) (by decide)).trans hS3
    · exact (h.V_le_S₃ (k := .i11) (by decide)).trans hS3
    · exact (h.V_le_S₃ (k := .i12) (by decide)).trans hS3
  have hQM : d.Q4 ≤ M := by
    have hV : ∀ k ∈ ({.i2, .i5, .i6, .i8, .i7, .i9, .i10, .i11, .i12} : Finset Idx),
        h.V k ≤ M := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · intro v hv
        have hv8 : h.s * v * h.s⁻¹ ∈ h.V .i8 := h.conj_s_mem_V (i := .i2) (by decide) hv
        have hw : h.s * v * h.s⁻¹ ∈ d.WA .i4 :=
          d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inr rfl)) hv8
        have := h2 (d.conj_s_mem_W2 hw)
        rwa [h.s_inv, show h.s * (h.s * v * h.s) * h.s = (h.s * h.s) * v * (h.s * h.s) by group,
          hs2, one_mul, mul_one] at this
      · exact d.bender.le.trans h5
      · intro v hv
        have hv5 : h.s * v * h.s⁻¹ ∈ h.V .i5 := h.conj_s_mem_V (i := .i6) (by decide) hv
        have := h6 (d.conj_s_mem_W6 (d.bender.le hv5))
        rwa [h.s_inv, show h.s * (h.s * v * h.s) * h.s = (h.s * h.s) * v * (h.s * h.s) by group,
          hs2, one_mul, mul_one] at this
      · exact (d.V_le_WA (i := .i4) (k := .i8) (h.V_le_R₁ (by decide))
          (h.V_le_CH (i := .i4) rfl (Or.inr rfl))).trans h8
      · exact (h.V_le_S₃ (k := .i7) (by decide)).trans (d.S₃_le_B3.trans h3)
      · exact (h.V_le_S₃ (k := .i9) (by decide)).trans (d.S₃_le_B3.trans h3)
      · exact (h.V_le_S₃ (k := .i10) (by decide)).trans (d.S₃_le_B3.trans h3)
      · exact (h.V_le_S₃ (k := .i11) (by decide)).trans (d.S₃_le_B3.trans h3)
      · exact (h.V_le_S₃ (k := .i12) (by decide)).trans (d.S₃_le_B3.trans h3)
    exact sup_le (h.pull_rootJoin_le hV) (d.B2_le_B3.trans h3)
  refine le_antisymm (fun x hx => ?_) hMB
  obtain ⟨v, hv, b, hb, hvb⟩ : ∃ v ∈ h.S₄, ∃ b ∈ d.B2, ⁅x, h.t⁆ = v * b := by
    have hxQ : ⁅x, h.t⁆ ∈ ((h.S₄ ⊔ d.B2 : Subgroup G) : Set G) := hx.2.2.2.2
    rw [coe_mul_of_left_le_normalizer_right _ _ (h.S₄_le_Kp.trans d.Kp_le_normalizer_B2),
      Set.mem_mul] at hxQ
    obtain ⟨v, hv, b, hb, e⟩ := hxQ
    exact ⟨v, hv, b, hb, e.symm⟩
  obtain ⟨m, hm, b', hb', hmv⟩ := hS4 hv
  have hq : m⁻¹ * x ∈ d.Q4 := d.inv_mul_mem_Q4_of_comm (hMB hm) hx (by
    have e : ⁅m, h.t⁆⁻¹ * ⁅x, h.t⁆ = b' * b := by
      rw [hvb, hmv]
      group
    rw [e]
    exact mul_mem hb' hb)
  have e : x = m * (m⁻¹ * x) := by group
  rw [e]
  exact mul_mem hm (hQM hq)

theorem sec3_8_one :
    d.B4 = d.W2 ⊔ d.W ⊔ d.W6 ⊔ d.WA .i4 ⊔ d.B3 ∧ h.Kp ≤ normalizer (d.B4 : Set G) ∧
      d.Q4 ≤ d.B4 ∧ (∀ x ∈ d.B4, ⁅x, h.t⁆ ∈ d.Q4) ∧
      (∀ x ∈ d.B4, ∀ y ∈ d.B4, ⁅x * y, h.t⁆ * (⁅x, h.t⁆ * ⁅y, h.t⁆)⁻¹ ∈ d.B2) ∧
      (∀ k ∈ h.Kp, ∀ x : G, ⁅k * x * k⁻¹, h.t⁆ = k * ⁅x, h.t⁆ * k⁻¹) ∧
      (∀ v ∈ h.S₄, ∃ x ∈ d.B4, ∃ b ∈ d.B2, v = ⁅x, h.t⁆ * b) ∧
      (∀ x ∈ d.B4, ⁅x, h.t⁆ ∈ d.B2 ↔ x ∈ d.Q4) := by
  refine ⟨d.B4_eq, d.Kp_le_normalizer_B4, d.Q4_le_B4, fun x hx => hx.2.2.2.2,
    fun x hx y hy => ?_, fun k hk x => ?_, fun v hv => d.exists_B4_comm_t hv,
    fun x hx => ⟨d.mem_Q4_of_comm_mem_B2 hx, d.comm_t_mem_B2_of_mem_Q4⟩⟩
  · have e : ⁅x * y, h.t⁆ * (⁅x, h.t⁆ * ⁅y, h.t⁆)⁻¹ = ⁅x, ⁅y, h.t⁆⁆ * ⁅⁅y, h.t⁆, ⁅x, h.t⁆⁆ := by
      rw [commutatorElement_mul_left_eq]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (d.comm_B4_Q4_mem hx hy.2.2.2.2) (d.comm_Q4_Q4_mem hy.2.2.2.2 hx.2.2.2.2)
  · have hkt : k * h.t * k⁻¹ = h.t := by
      rw [mem_centralizer_singleton_iff.1 hk.1, mul_inv_cancel_right]
    simp only [commutatorElement_def]
    conv_lhs => rw [← hkt]
    group

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
