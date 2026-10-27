module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WFour
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.sec38c1_eq_of_act_eq (hd : d.Hyp) {a b : G} (ha : a ∈ d.L) (hb : b ∈ d.L)
    (e : d.act ⟨a, le_normalizer ha⟩ = d.act ⟨b, le_normalizer hb⟩) : a = b := by
  have hN : ∀ x ∈ d.L, x ∈ normalizer (d.L : Set G) := fun x hx => le_normalizer hx
  have hc : a⁻¹ * b ∈ centralizer (d.L : Set G) := by
    refine (d.act_eq_one_iff ⟨a⁻¹ * b, mul_mem (inv_mem (hN a ha)) (hN b hb)⟩).1 ?_
    have e' : (⟨a⁻¹ * b, mul_mem (inv_mem (hN a ha)) (hN b hb)⟩ : normalizer (d.L : Set G)) =
        (⟨a, hN a ha⟩ : normalizer (d.L : Set G))⁻¹ * ⟨b, hN b hb⟩ := rfl
    rw [e', map_mul, map_inv, e, inv_mul_cancel]
  have hL : a⁻¹ * b ∈ d.L := mul_mem (inv_mem ha) hb
  have h1 : a⁻¹ * b ∈ d.L ⊓ centralizer (d.L : Set G) := ⟨hL, hc⟩
  rw [hd.inf_centralizer_eq_bot, mem_bot] at h1
  exact inv_mul_eq_one.1 h1

theorem Hyp.sec38c1_card_le_out (hd : d.Hyp) {x : G} (hx : x ∈ d.T) (hxt : x ∉ d.tP)
    {Y : Subgroup G} (hY : Y ≤ d.A₂) (hc : ∀ a ∈ Y, ⁅a, x⁆ ∈ d.Zp) :
    Nat.card Y ≤ (2 ^ f) ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxN : x ∈ normalizer (d.L : Set G) := hd.T_le_normalizer hx
  have hout : d.act ⟨x, hxN⟩ ∉ Pi h := fun e => hxt (hd.mem_tP_of_act_mem_Pi hx hxN e)
  have hT2 : IsPGroup 2 (d.actImage d.T) :=
    (hd.isPGroup_T.comap_subtype (K := normalizer (d.L : Set G))).map _
  have hρT : d.act ⟨x, hxN⟩ ∈ d.actImage d.T := d.mem_actImage.2 ⟨x, hx, hxN, rfl⟩
  have hYN : ∀ a ∈ Y, a ∈ normalizer (d.L : Set G) := fun a ha =>
    le_normalizer (d.A₂_le_L (hY ha))
  have hXA : d.actImage Y ≤ (A₂sub h).map (innM h) := by
    rw [← d.actImage_pull (A₂sub h)]
    intro ρ hρ
    obtain ⟨y, hy, hyN, rfl⟩ := d.mem_actImage.1 hρ
    exact d.mem_actImage.2 ⟨y, hY hy, hyN, rfl⟩
  have hX : ∀ ξ ∈ d.actImage Y, ⁅d.act ⟨x, hxN⟩, ξ⁆ ∈ (ZPsub h).map (innM h) := by
    intro ξ hξ
    obtain ⟨a, ha, haN, rfl⟩ := d.mem_actImage.1 hξ
    rw [← d.actImage_pull (ZPsub h)]
    have hz : ⁅x, a⁆ ∈ d.Zp := by
      have := inv_mem (hc a ha)
      rwa [commutatorElement_inv] at this
    have hzN : ⁅x, a⁆ ∈ normalizer (d.L : Set G) := le_normalizer (d.Zp_le_L hz)
    refine d.mem_actImage.2 ⟨⁅x, a⁆, hz, hzN, ?_⟩
    rw [← map_commutatorElement]
    rfl
  have h1 := card_le_of_outer_Ah hd.center_hypPSU hT2 hd.inf_Pi_actImage_T hρT hout hXA hX
  let φ : Y → d.actImage Y := fun a =>
    ⟨d.act ⟨a, hYN a a.2⟩, d.mem_actImage.2 ⟨a, a.2, hYN a a.2, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have e : d.act ⟨a, hYN a a.2⟩ = d.act ⟨b, hYN b b.2⟩ := congrArg Subtype.val hab
    exact Subtype.ext (hd.sec38c1_eq_of_act_eq (d.A₂_le_L (hY a.2)) (d.A₂_le_L (hY b.2)) e)
  exact (Nat.card_le_card_of_injective φ hφ).trans h1

theorem Hyp.sec38c1_card_le_in (hd : d.Hyp) {x : G} (hx : x ∈ d.tP) (hxB : x ∉ d.B₂)
    {Y : Subgroup G} (hY : Y ≤ d.A₂) (hc : ∀ a ∈ Y, ⁅a, x⁆ ∈ d.Zp) :
    Nat.card Y ≤ (2 ^ f) ^ 5 := by
  obtain ⟨p, hp, hxp⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hx
  have hpA : p ∉ d.A₂ := by
    intro hpA
    refine hxB ?_
    rcases hxp with rfl | rfl
    · exact mem_sup_right hpA
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right hpA)
  have hYle : Y ≤ d.A₂ ⊓ d.A₃ := by
    intro a ha
    refine d.sec2_2_five.2 p hp hpA a (hY ha) ?_
    have h1 := hc a ha
    rcases hxp with rfl | rfl
    · exact h1
    · have haL : a ∈ d.L := d.A₂_le_L (hY ha)
      have hpL : p ∈ d.L := d.P_le_L hp
      have hat : d.t * a = a * d.t := (hd.comm_t haL).symm
      have hcL : ⁅a, p⁆ ∈ d.L := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem haL hpL) (inv_mem haL)) (inv_mem hpL)
      have hct : ⁅a, p⁆ * d.t = d.t * ⁅a, p⁆ := hd.comm_t hcL
      have e : ⁅a, d.t * p⁆ = d.t * ⁅a, p⁆ * d.t⁻¹ := by
        simp only [commutatorElement_def]
        calc a * (d.t * p) * a⁻¹ * (d.t * p)⁻¹ = (a * d.t) * p * a⁻¹ * p⁻¹ * d.t⁻¹ := by group
          _ = (d.t * a) * p * a⁻¹ * p⁻¹ * d.t⁻¹ := by rw [← hat]
          _ = d.t * (a * p * a⁻¹ * p⁻¹) * d.t⁻¹ := by group
      rw [e, mul_inv_eq_iff_eq_mul.2 hct.symm] at h1
      exact h1
  have hcard : Nat.card (d.A₂ ⊓ d.A₃ : Subgroup G) = (2 ^ f) ^ 5 := by
    have e : d.A₂ ⊓ d.A₃ = d.pull (A₂sub h ⊓ Ssub h) :=
      (d.pull_inf A₂sub_le_U Ssub_le_Usub).symm
    rw [e, d.card_pull (inf_le_left.trans A₂sub_le_U), card_A₂sub_inf_Ssub]
  exact (Subgroup.card_le_of_le hYle).trans hcard.le

end Data

end CFSG.LocalAnalysis.EvenBN.U5
