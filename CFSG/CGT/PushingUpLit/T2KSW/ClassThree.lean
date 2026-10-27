module

public import CFSG.CGT.PushingUpLit.T2KSW.ClassThreeWC
public import CFSG.CGT.PushingUpLit.T2KSW.Prop28

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open scoped commutatorElement
open Aux

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

namespace ClassThree

omit [Finite G] in
theorem mul_comm_of_mem_sup {A B : Subgroup G} (hn : A ≤ Subgroup.normalizer (B : Set G))
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_mul hn).1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_mul hn).1 hy
  have c1 : Commute a a' := hA a ha a' ha'
  have c2 : Commute a b' := hAB a ha b' hb'
  have c3 : Commute b a' := (hAB a' ha' b hb).symm
  have c4 : Commute b b' := hB b hb b' hb'
  exact (c1.mul_right c2).mul_left (c3.mul_right c4)

end ClassThree

open ClassThree

theorem card_Ec_lt_card_T (hc : ClassThreeSetup G L M T n) (hRD : T ≤ Rl L T ⊔ Dc L T) :
    2 ^ (3 * n) * Nat.card (Ec L T) < Nat.card T := by
  have hs := hc.sec4
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hTRD : Rl L T ⊔ Dc L T = T := le_antisymm (sup_le Rl_le_T Dc_le_T) hRD
  have hT : Nat.card T = 2 ^ n * Nat.card (Dc L T) := by
    have := card_Rl_sup_Dc h hLM hc.MN hs.sylow
    rwa [hTRD] at this
  have hVT : blockU L ≤ T := NatBlock.blockU_le_sylow hLM hc.MN hs.sylow
  have hVD : blockU L ≤ Dc L T := blockU_le_Dc h hLM hc.MN hs.sylow
  have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    hVT.trans (hs.sylow.le.trans hc.ME)
  have hEV := card_sup_mul_card_inf_of_le_normalizer hVn
  have hEVcap : Ec L T ⊓ blockU L = blockZ L := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hVT hx.1, hx.2⟩, hx.1⟩⟩
  rw [hEVcap, h.card_blockU] at hEV
  have hZpos : 0 < Nat.card (blockZ L) := Nat.card_pos
  have hEVcard : Nat.card (Ec L T ⊔ blockU L : Subgroup G) = (2 ^ n) ^ 2 * Nat.card (Ec L T) := by
    apply Nat.eq_of_mul_eq_mul_right hZpos
    rw [hEV]
    ring
  have hEVD : Ec L T ⊔ blockU L ≤ Dc L T := sup_le Ec_le_Dc hVD
  have hle : (2 ^ n) ^ 2 * Nat.card (Ec L T) ≤ Nat.card (Dc L T) :=
    hEVcard ▸ Subgroup.card_le_of_le hEVD
  have h2n : 2 ^ (3 * n) = 2 ^ n * (2 ^ n) ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hT, h2n]
  have hpos : 0 < 2 ^ n := by positivity
  by_contra hnot
  push Not at hnot
  have hcard : Nat.card (Dc L T) ≤ (2 ^ n) ^ 2 * Nat.card (Ec L T) := by
    have : 2 ^ n * Nat.card (Dc L T) ≤ 2 ^ n * ((2 ^ n) ^ 2 * Nat.card (Ec L T)) := by
      calc 2 ^ n * Nat.card (Dc L T) ≤ 2 ^ n * (2 ^ n) ^ 2 * Nat.card (Ec L T) := hnot
        _ = 2 ^ n * ((2 ^ n) ^ 2 * Nat.card (Ec L T)) := by ring
    exact Nat.le_of_mul_le_mul_left this hpos
  have hDeq : Ec L T ⊔ blockU L = Dc L T :=
    Subgroup.eq_of_le_of_card_ge hEVD (by rw [hEVcard]; exact hcard)
  have habel : ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x := by
    rw [← hDeq, sup_comm]
    refine mul_comm_of_mem_sup (A := blockU L) (B := Ec L T) hVn
      (fun a ha a' ha' => h.blockU_comm a ha a' ha')
      (fun b hb b' hb' => congrArg Subtype.val (hs.S_elem.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩))
      (fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb.2 a (blockU_le L ha))
  obtain ⟨x, hx, y, hy, z, hz, hne⟩ := hc.comm3
  refine hne ?_
  rw [commutatorElement_eq_one_iff_mul_comm.2 (habel x hx y hy), commutatorElement_one_left]

namespace ClassThree

theorem ne_bot_of_natBlock {L : Subgroup G} (h : NatBlock L n) : L ≠ ⊥ := by
  intro hL
  have := h.sixty_le_card
  rw [hL, Subgroup.card_bot] at this
  omega

theorem exists_noncomm_of_natBlock {L : Subgroup G} (h : NatBlock L n) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  exact ne_bot_of_natBlock h
    (eq_bot_of_perfect_of_pairwise_comm h.perfect fun x _ y _ => hcomm x y)

end ClassThree

end CFSG.CGT.PushingUpLit.T2KSW
