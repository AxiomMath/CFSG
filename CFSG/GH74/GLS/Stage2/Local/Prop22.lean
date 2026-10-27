module

public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GH74.GLS.Bg.Local.Lemma1621
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

section P22

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem Stage2Ctx.prop22a (h : Stage2Ctx G z k S) : Prop22a z S := by
  intro hone _ U hUS hU hUn
  have : IsElementaryAbelian 2 ↥U := hU.1
  have hUcard : Nat.card ↥U = 4 := hU.2
  have hUel : ∀ a ∈ U, a * a = 1 := fun a ha => by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a ha
    simpa [pow_two] using this
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [h.orderOf_z, pow_two] at this
    exact this
  have hz1 : z ≠ 1 := by
    intro h1
    have := h.orderOf_z
    rw [h1, orderOf_one] at this
    omega
  have hUne : U ≠ ⊥ := by
    intro hb
    rw [hb] at hUcard
    simp at hUcard
  obtain ⟨u₀, hu₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hUne)
  have hzU : z ∈ U := by
    have hS2 : IsPGroup 2 ↥S := h.sylow.isPGroup
    have : Group.IsNilpotent ↥S := hS2.isNilpotent
    let N : Subgroup ↥S := U.subgroupOf S
    have hNnorm : N.Normal := ⟨fun n hn g => by
      show ((g * n * g⁻¹ : ↥S) : G) ∈ U
      simpa using hUn g.1 g.2 n.1 hn⟩
    have hNbot : N ≠ ⊥ := by
      apply Subgroup.ne_bot_iff_exists_ne_one.mpr
      refine ⟨⟨⟨(u₀ : G), hUS u₀.2⟩, u₀.2⟩, ?_⟩
      intro h1
      apply hu₀1
      have := congrArg (fun x : ↥N => ((x : ↥S) : G)) h1
      exact Subtype.ext this
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hNbot)
    have hwU : ((w : ↥S) : G) ∈ U := (Subgroup.mem_inf.mp w.2).1
    have hwc : ∀ s ∈ S, s * ((w : ↥S) : G) = ((w : ↥S) : G) * s := fun s hs => by
      have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp w.2).2 ⟨s, hs⟩
      exact congrArg Subtype.val this
    have hw1' : ((w : ↥S) : G) ≠ 1 := fun e => hw1 (Subtype.ext (Subtype.ext e))
    have hord : orderOf ((w : ↥S) : G) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two]; exact hUel _ hwU
      · exact hw1'
    have hwz := h.data.base.zcen _ ((w : ↥S) : ↥S).2 hwc hord
    exact hwz ▸ hwU
  have hexu : ∃ u ∈ U, u ∉ zpowers z := by
    by_contra hcon
    have hle : U ≤ zpowers z := fun x hx => by
      by_contra hxz
      exact hcon ⟨x, hx, hxz⟩
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, h.orderOf_z] at this
    omega
  obtain ⟨u, huU, huz⟩ := hexu
  have hu1 : u ≠ 1 := fun e => huz (e ▸ one_mem _)
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hUel u huU) hu1
  have hconj : IsConj z u := hone z u h.orderOf_z hu2
  have hsyl : ¬ 2 ∣ S.index := by
    have := h.sylow_top
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at this
    simpa [Subgroup.relIndex_top_right] using this.2.2
  have hconcl := CFSG.GH74.GLS.Bg.thompson_lemma_16_21 (X := G) (P := S) (U := U) (z := z) (u := u)
    h.sylow.isPGroup hsyl h.center_cyclic hUS hUn hUcard hUel h.z_mem hz2 hz1
    (fun g hg => h.S_comm_z hg) huU huz hconj
  refine ⟨hzU, ?_⟩
  obtain ⟨e⟩ := hconcl.iso_S3
  have hcard := Nat.card_congr e.toEquiv
  unfold AutOrd
  rw [inf_top_eq, inf_top_eq]
  unfold Subgroup.relIndex
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  rw [h6] at hcard
  exact hcard

end P22

end CFSG.GH74.GLS.Stage2.Local
