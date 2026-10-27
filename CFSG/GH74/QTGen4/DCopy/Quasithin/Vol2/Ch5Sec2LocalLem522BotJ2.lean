module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotList
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotW
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotJ2

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

theorem stmt5_2_2_bot_J2_of_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    Stmt5_2_2_bot_J2_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n hyp _ hS3 h111 _ hL2 hQ8 hO6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := sec52S M H with hSdef
  set Q := pCoreOf 2 L₂ with hQdef
  have hSY : IsSylowTwoOf S (Dp ⊔ S) := by
    have h := h111.h2.sylow
    rwa [inf_eq_left.mpr le_sup_right] at h
  have hS7 : Nat.card ↥S = 2 ^ 7 := by
    rw [card_eq_two_mul_of_perm_three hSY hS3, hO6]
    norm_num
  have hSL7 : Nat.card ↥(S ⊓ L₂) = 2 ^ 7 := by
    rw [card_inf_of_card_oTwoQuot h111.h1.sylow (j := 2) (m := 15) (by norm_num)
      (by rw [hL2.card (by norm_num)]; norm_num), hQ8.1]
    norm_num
  have hSL : S ≤ L₂ := le_of_card_le_card_inf (hS7.trans hSL7.symm).le
  have hchar : CharTwo L₂ := by
    have hle : L₂ ≤ L₂ ⊔ S ⊔ borelOf (Dp ⊔ S) S := le_sup_left.trans le_sup_left
    refine CT.CharTwo.of_normal h111.h1.charTwo hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_)
    exact sup_le (sup_le Subgroup.le_normalizer h111.h1.normalizes) h111.h1.borel_le
  obtain ⟨z, hz, hz1, hzz, hcenQ, hsqQ⟩ := isQ8D8_central_facts hQ8
  have hz1' : (z : G) ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hzz' : (z : G) * z = 1 := congrArg Subtype.val hzz
  have hzQc : ∀ q ∈ Q, q * (z : G) = z * q := fun q hq =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨q, hq⟩)
  have hLQ : L₂ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 L₂
  have hcen : ∀ c ∈ Q, (∀ q ∈ Q, q * c = c * q) → c = 1 ∨ c = z := by
    intro c hc hcq
    rcases hcenQ ⟨c, hc⟩ (Subgroup.mem_center_iff.mpr fun q => Subtype.ext (hcq q q.2)) with
      h0 | h0
    · exact Or.inl (congrArg Subtype.val h0)
    · exact Or.inr (congrArg Subtype.val h0)
  have hsq : ∀ q ∈ Q, q * q = 1 ∨ q * q = z := by
    intro q hq
    rcases hsqQ ⟨q, hq⟩ with h0 | h0
    · exact Or.inl (congrArg Subtype.val h0)
    · exact Or.inr (congrArg Subtype.val h0)
  have hzL : ∀ l ∈ L₂, l * (z : G) = z * l := by
    intro l hl
    have hlz : l * (z : G) * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hl) z).mp z.2
    have hc : l * (z : G) * l⁻¹ = 1 ∨ l * (z : G) * l⁻¹ = z := by
      refine hcen _ hlz fun q hq => ?_
      have hq' : l⁻¹ * q * l⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hLQ (L₂.inv_mem hl)) q).mp hq
      rw [inv_inv] at hq'
      have h1 := hzQc _ hq'
      calc q * (l * z * l⁻¹) = l * ((l⁻¹ * q * l) * z) * l⁻¹ := by group
        _ = l * (z * (l⁻¹ * q * l)) * l⁻¹ := by rw [h1]
        _ = l * z * l⁻¹ * q := by group
    rcases hc with h0 | h0
    · exfalso
      apply hz1'
      calc (z : G) = l⁻¹ * (l * z * l⁻¹) * l := by group
        _ = 1 := by rw [h0]; group
    · calc l * (z : G) = l * z * l⁻¹ * l := by group
        _ = z * l := by rw [h0]
  have hSL' : IsSylowTwoOf S L₂ := by
    have h := h111.h1.sylow
    rwa [inf_eq_left.mpr hSL] at h
  have hQS : Q ≤ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSL'
  obtain ⟨hWS, hW2, hWc, hWN, hW16⟩ := hyp.commutator_facts_F4 h510 h331 hR
  obtain ⟨hST, -, -, -, -, -, -, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hSW : S ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    hST.trans (le_sup_right.trans hWN)
  have hW2' : ∀ x ∈ ⁅V, L⁆, x * x = 1 := fun x hx => by rw [← sq]; exact hW2 x hx
  have hWQ : ⁅V, L⁆ ≤ Q := le_of_forall_mem_pair hchar z.2 hz1' hzz' hzL (hWS.trans hSL)
    fun e he q hq => mem_pair_of_normal_elemAbelian hQ8 z.2 hz1' hzz'
      (fun s hs => hzL s (hSL hs)) hcen hsq hQS (hSL.trans hLQ) hWS hSW hW2' hWc he hq
  have h4 := card_le_four_of_isQ8D8 hQ8 (⁅V, L⁆.subgroupOf Q)
    (fun x hx => Subtype.ext (hW2' _ (Subgroup.mem_subgroupOf.mp hx)))
    (fun a ha b hb => Subtype.ext (hWc _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ).toEquiv] at h4
  omega

end CFSG.Quasithin.H13
