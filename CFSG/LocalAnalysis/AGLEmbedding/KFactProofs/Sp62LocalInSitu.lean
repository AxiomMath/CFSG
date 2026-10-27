module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalViso
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Data

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Quasithin.H13
open scoped commutatorElement

theorem commutator_V0_eq_top :
    commutator V0 = ⊤ := by
  have hs := isSimpleGroup_V0
  rcases (inferInstance : (commutator V0).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    have hmem : ⁅aV, bV⁆ ∈ commutator V0 :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    have h' : elt cA * elt cB = elt cB * elt cA := congrArg Subtype.val hmem
    have := ((rep_elt (genB_isoB genB_cA)).comm_iff (rep_elt (genB_isoB genB_cB))).1 h'
    have hb : commB cA cB = true := beq_iff_eq.2 this
    rw [commB_cA_cB] at hb
    exact Bool.false_ne_true hb
  · exact h

theorem V0_perfect :
    ⁅V0, V0⁆ = V0 :=
  Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 commutator_V0_eq_top)

theorem V_quasi_W0
    (W : Subgroup H6)
    (hWW : W ≤ W0) (hVN : V0 ≤ Subgroup.normalizer (W : Set H6)) :
    V0 ≤ W ∨ ⁅W, V0⁆ = ⊥ := by
  have hs := isSimpleGroup_V0
  have hnormal : ((W ⊓ V0).subgroupOf V0).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact Subgroup.mem_inf.2
      ⟨(Subgroup.mem_normalizer_iff.1 (hVN g.2) n).1 (Subgroup.mem_inf.1 hn).1,
        mul_mem (mul_mem g.2 (Subgroup.mem_inf.1 hn).2) (inv_mem g.2)⟩
  rcases hnormal.eq_bot_or_eq_top with h | h
  · right
    have hbot : W ⊓ V0 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : V0) ∈ (W ⊓ V0).subgroupOf V0 := hx
      rw [h, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hx'
    rw [eq_bot_iff, ← hbot, Subgroup.commutator_le]
    intro w hw v hv
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · have h1 : v * w⁻¹ * v⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 (hVN hv) w⁻¹).1 (inv_mem hw)
      have := mul_mem hw h1
      simpa [commutatorElement_def, mul_assoc] using this
    · have h1 : w * v * w⁻¹ ∈ V0 :=
        (Subgroup.mem_normalizer_iff.1 (W0_le_normalizer_V0 (hWW hw)) v).1 hv
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hv)
  · left
    intro v hv
    have : (⟨v, hv⟩ : V0) ∈ (W ⊓ V0).subgroupOf V0 := by
      rw [h]
      exact Subgroup.mem_top _
    exact this.1

theorem dichotomy_W0
    (W : Subgroup H6)
    (hWW : W ≤ W0) (hWN : W0 ≤ Subgroup.normalizer (W : Set H6)) : W = ⊥ ∨ V0 ≤ W := by
  rcases V_quasi_W0 W hWW (V0_le_W0.trans hWN) with h | h
  · exact Or.inr h
  · left
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    rw [eq_bot_iff, ← W0_inf_centralizer_V0]
    exact le_inf hWW h

theorem relIndex_V0_W0 : V0.relIndex W0 = 2 := by
  have h := Subgroup.card_mul_index (V0.subgroupOf W0)
  rw [Subgroup.relIndex]
  have hc : Nat.card (V0.subgroupOf W0) = Nat.card V0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe V0_le_W0).toEquiv
  rw [hc, card_V0, Nat.card_congr (Equiv.refl _), card_W0] at h
  omega

theorem sp62InSitu_W0 :
    Sp62InSitu T0 W0 V0 where
  card_T := card_T0
  T_le := T0_le_V0
  V_le := V0_le_W0
  V_perfect := V0_perfect
  V_normal := W0_le_normalizer_V0
  V_index := relIndex_V0_W0.le
  V_iso := V_iso_V0
  V_quasi := V_quasi_W0
  V_centralizer := W0_inf_centralizer_V0
  dichotomy := dichotomy_W0
  centralizer_le := W0_inf_centralizer_T0_le

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
