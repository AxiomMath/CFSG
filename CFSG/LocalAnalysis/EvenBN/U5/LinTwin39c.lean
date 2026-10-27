module

public import CFSG.LocalAnalysis.EvenBN.U5.LinLayer
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineC

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_Y₂_mem_odd (hl : d.LinCtx) (k8 : d.Know8) : d.Sec39cY₂ := by
  intro m hm hmc
  have hd := hl.hyp
  have hGMS := hl.gms
  obtain ⟨hΛs, -, hlay⟩ := lin_layer_facts hl
  have hME : ∀ x ∈ d.M₂, x ∈ normalizer (d.E : Set G) := fun x hx =>
    d.L₂_le_normalizer_E (sec39c_M₂_le_L₂ k8 hx)
  have hMV : ∀ x ∈ d.M₂, x ∈ normalizer (d.V : Set G) := fun x hx =>
    sec39c_L₂_le_normalizer_V k8 (sec39c_M₂_le_L₂ k8 hx)
  let Y₂ : Subgroup G := sec39cCentMod d.E d.V ⊓ d.M₂
  let Kb : Subgroup (sec39cQ d) := (Y₂.subgroupOf (sec39cH d)).map (sec39cθ d)
  have hKD : Kb ≤ layer (sec39cQ d) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hlay]
    exact ⟨y, (Subgroup.mem_subgroupOf.1 hy).2, rfl⟩
  have hKn : ∀ x ∈ layer (sec39cQ d), ∀ k ∈ Kb, x * k * x⁻¹ ∈ Kb := by
    intro x hx k hk
    rw [← hlay] at hx
    obtain ⟨m₀, hm₀, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hk
    refine ⟨m₀ * y * m₀⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hm₀' : (m₀ : G) ∈ d.M₂ := Subgroup.mem_subgroupOf.1 hm₀
    obtain ⟨hyc, hyM⟩ := Subgroup.mem_subgroupOf.1 hy
    exact ⟨sec39c_centMod_conj (hME _ hm₀') (hMV _ hm₀') hyc,
      d.M₂.mul_mem (d.M₂.mul_mem hm₀' hyM) (d.M₂.inv_mem hm₀')⟩
  have hfinal : ¬ layer (sec39cQ d) ≤ Kb := by
    intro hlayK
    have hsH : d.s ∈ sec39cH d := d.N₂_le_centralizer_I₂ d.s_mem_N₂
    have hsl : sec39cθ d ⟨d.s, hsH⟩ ∈ layer (sec39cQ d) := by
      rw [← hlay]
      exact ⟨⟨d.s, hsH⟩, Subgroup.mem_subgroupOf.2 (sec39c_N₂_le_M₂ d d.s_mem_N₂), rfl⟩
    obtain ⟨y, hy, hys⟩ := hlayK hsl
    have ho : y⁻¹ * ⟨d.s, hsH⟩ ∈ standardComponentOddCore ↥(sec39cH d) :=
      QuotientGroup.eq.1 hys
    obtain ⟨hyc, hyM⟩ := Subgroup.mem_subgroupOf.1 hy
    have hodd : Odd (Nat.card (standardComponentOddCore ↥(sec39cH d))) :=
      GMSK.odd_card_standardComponentOddCore _
    have ho1 : (y⁻¹ * ⟨d.s, hsH⟩ : ↥(sec39cH d)) ^
        (Nat.card (standardComponentOddCore ↥(sec39cH d))) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ ho)
    have ho2 : ((y : G)⁻¹ * d.s) ^ Nat.card (standardComponentOddCore ↥(sec39cH d)) = 1 := by
      have := congrArg Subtype.val ho1
      simpa using this
    have hyL : (y : G) ∈ d.L₂ := sec39c_M₂_le_L₂ k8 hyM
    have hsL : d.s ∈ d.L₂ := d.N₂_le_L₂ d.s_mem_N₂
    have hs2 : d.s ^ 2 ^ 1 = 1 := by
      have := pow_orderOf_eq_one d.s
      rwa [d.orderOf_s] at this
    have hsmem : d.s ∈ sec39cCentMod d.E d.V ⊓ d.L₂ :=
      sec39c_mem_of_odd_mul (L := d.L₂) (Y := sec39cCentMod d.E d.V ⊓ d.L₂) inf_le_right
        (fun g hg y' hy' => ⟨sec39c_centMod_conj (d.L₂_le_normalizer_E hg)
          (sec39c_L₂_le_normalizer_V k8 hg) hy'.1,
            d.L₂.mul_mem (d.L₂.mul_mem hg hy'.2) (d.L₂.inv_mem hg)⟩)
        hsL ⟨hyc, hyL⟩ (d.L₂.mul_mem (d.L₂.inv_mem hyL) hsL) (by group) hs2 ho2 hodd
    obtain ⟨a₀, ha₀, hA, hnZ⟩ := sec39c_s_not_comm d
    have ha₀E : a₀ ∈ d.E := hd.A₂_le_E hGMS ha₀
    have hV : d.s * a₀ * d.s⁻¹ * a₀⁻¹ ∈ d.V := (sec39c_mem_centMod.1 hsmem.1).2 a₀ ha₀E
    exact hnZ (by rw [← hd.V_inf_A₂]; exact ⟨hV, hA⟩)
  haveI := hΛs
  have hnorm : (Kb.subgroupOf (layer (sec39cQ d))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hKn (g : sec39cQ d) g.2 n hn
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Kb.subgroupOf (layer (sec39cQ d))) with h0 | h1
  · have hmH := sec39c_M₂_le_H d hm
    refine ⟨hmH, ?_⟩
    have hmY : (⟨m, hmH⟩ : ↥(sec39cH d)) ∈ Y₂.subgroupOf (sec39cH d) :=
      Subgroup.mem_subgroupOf.2 ⟨hmc, hm⟩
    have hmK : sec39cθ d ⟨m, hmH⟩ ∈ Kb := ⟨_, hmY, rfl⟩
    have hmΛ : sec39cθ d ⟨m, hmH⟩ ∈ layer (sec39cQ d) := hKD hmK
    have : (⟨sec39cθ d ⟨m, hmH⟩, hmΛ⟩ : ↥(layer (sec39cQ d))) ∈ Kb.subgroupOf (layer (sec39cQ d)) :=
      Subgroup.mem_subgroupOf.2 hmK
    rw [h0, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val this)
  · exfalso
    refine hfinal fun x hx => ?_
    have : (⟨x, hx⟩ : ↥(layer (sec39cQ d))) ∈ Kb.subgroupOf (layer (sec39cQ d)) := by
      rw [h1]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

theorem lin_sec39c (hl : d.LinCtx) (k8 : d.Know8) (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) (ha : d.Sec39a S) (hb : d.Sec39b) : d.Sec39c S :=
  sec39c_of_hyp hl.toCaseHyp k8 S hS hP ha hb (lin_Y₂_mem_odd hl k8)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
