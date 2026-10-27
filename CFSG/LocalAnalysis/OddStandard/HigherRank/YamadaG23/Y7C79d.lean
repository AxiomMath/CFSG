module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79s
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79e
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79g

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem y7c_step1 {M L1 L2 P V : Subgroup G} (h : Gl3Pair M L1 L2)
    (hP : IsSylowIn 2 (L1 ⊔ L2) P) (hV : V ≤ M) (hVc : Nat.card V = 4)
    (hVP : ∀ v ∈ V, ∀ x ∈ P, v * x = x * v)
    (h1 : centIn M L1 = ⊥) (h2 : centIn M L2 = ⊥) : False := by
  obtain ⟨hMP, hDcard⟩ := Gl3Pair.card_inf_sylow h hP
  have hP' : IsSylowIn 2 (L2 ⊔ L1) P := by
    unfold IsSylowIn
    rw [sup_comm]
    exact hP
  obtain ⟨hMP2, hD2card⟩ := Gl3Pair.card_inf_sylow h.symm hP'
  let D : Subgroup G := L1 ⊓ P
  let D2 : Subgroup G := L2 ⊓ P
  let W : Subgroup G := centIn M D
  haveI : IsMulCommutative M := h.elem.1
  have hMcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : M) (⟨b, hb⟩ : M))
  have hMD : M ≤ D := le_inf h.ext1.1 hMP
  have hMD2 : M ≤ D2 := le_inf h.ext2.1 hMP2
  have hDL1 : D ≤ L1 := inf_le_left
  have hD2L2 : D2 ≤ L2 := inf_le_left
  have hWleM : W ≤ M := inf_le_left
  have hM2 : IsPGroup 2 M := IsPGroup.of_card h.card
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hcardM : Nat.card M = 2 ^ 6 := h.card
    rw [hbot, Subgroup.card_bot] at hcardM
    norm_num at hcardM
  have hDpg : IsPGroup 2 D := IsPGroup.to_le hP.2.1 inf_le_right
  have hDMnorm : D ≤ normalizer (M : Set G) := le_trans inf_le_left h.le_normalizer_M
  have Wne : W ≠ ⊥ := y7c_centIn_ne_bot hM2 hMne hDpg hDMnorm
  have Wnorm : L2 ≤ normalizer (W : Set G) :=
    Gl3Pair.L2_le_normalizer_centIn h inf_le_left
  have WMcent : M ≤ centralizer (W : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hMcomm w (hWleM hw) m hm
  have Welem : IsElemAbelian 2 W := y7c_isElemAbelian_of_le h.elem inf_le_left
  have Wfix : centIn W L2 = ⊥ := by
    apply le_bot_iff.mp
    exact h2 ▸ le_inf (le_trans inf_le_left hWleM) inf_le_right
  have Wh8 : 8 ≤ Nat.card W :=
    y7c_gl3_card_ge_eight h.ext2 Wnorm WMcent Welem Wne Wfix
  obtain ⟨x, hxL1, hDsup⟩ := y7c_gl3_gen_sylow h.ext1 hMD hDL1 hDcard
  have hxM : conjSub x M = M :=
    y7c_conjSub_eq_of_mem_normalizer (h.le_normalizer_M hxL1)
  have hconj_cent : centIn M (conjSub x D) = conjSub x W := y7c_centIn_conjSub hxM
  have hWconj : W ⊓ conjSub x W = ⊥ := by
    have hmain : W ⊓ conjSub x W = centIn M L1 := by
      rw [← hDsup, y7c_centIn_sup, hconj_cent]
    rw [hmain]
    exact h1
  have hconjW_le_M : conjSub x W ≤ M := by
    rw [← hconj_cent]
    exact inf_le_left
  have hcommW : ∀ a ∈ W, ∀ b ∈ conjSub x W, a * b = b * a := by
    intro a ha b hb
    exact hMcomm a (hWleM ha) b (hconjW_le_M hb)
  have hsupcard : Nat.card ↥(W ⊔ conjSub x W) = Nat.card W * Nat.card (conjSub x W) :=
    y7c_card_sup_of_commute hcommW hWconj
  have hconjcard : Nat.card (conjSub x W) = Nat.card W := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hle : W ⊔ conjSub x W ≤ M := sup_le hWleM hconjW_le_M
  have hcardW_sq : Nat.card W * Nat.card W ≤ 64 := by
    have hcard := Subgroup.card_le_of_le hle
    rw [hsupcard, hconjcard, h.card] at hcard
    norm_num at hcard
    exact hcard
  have hWcard : Nat.card W = 8 := by
    refine le_antisymm ?_ Wh8
    have h8n : 8 * Nat.card W ≤ Nat.card W * Nat.card W := Nat.mul_le_mul_right _ Wh8
    have : 8 * Nat.card W ≤ 64 := le_trans h8n hcardW_sq
    omega
  have hfixcard : Nat.card ↥(centIn W D2) ≤ 2 :=
    y7c_gl3_fix_sylow h.ext2 Wnorm WMcent Welem hWcard Wfix hMD2 hD2L2 hD2card
  have hVW : V ≤ W := by
    refine le_inf hV ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hVP v hv d (Subgroup.mem_inf.mp hd).2).symm
  have hVsub : V ≤ centIn W D2 := by
    refine le_inf hVW ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hVP v hv d (Subgroup.mem_inf.mp hd).2).symm
  have hcardV_le : Nat.card V ≤ Nat.card ↥(centIn W D2) := Subgroup.card_le_of_le hVsub
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
