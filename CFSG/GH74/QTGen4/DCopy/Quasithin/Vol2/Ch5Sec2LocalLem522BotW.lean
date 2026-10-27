module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotS331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotW

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

namespace Hyp5_2_2p

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}

theorem commutator_facts_F4 (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    ⁅V, L⁆ ≤ sec52S M H ∧ (∀ x ∈ ⁅V, L⁆, x ^ 2 = 1) ∧
      (∀ a ∈ ⁅V, L⁆, ∀ b ∈ ⁅V, L⁆, a * b = b * a) ∧
      L ⊔ T ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) ∧
      16 ≤ Nat.card ↥⁅V, L⁆ := by
  have h := hyp.toHyp5_0_1
  have hV := hyp.ch5Module
  have hred := hV.isTwoReducedIn
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hVL : V ≤ Subgroup.normalizer (L : Set G) :=
    hred.1.trans (sup_le Subgroup.le_normalizer hTL)
  have hWL : ⁅V, L⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_right.mp hVL
  have hVT : V ≤ T := h.V_le_T hV
  obtain ⟨-, -, -, -, hSL, -, -, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hWS : ⁅V, L⁆ ≤ sec52S M H := by
    intro x hx
    have hxTL : x ∈ T ⊓ L := ⟨hVT (hWV hx), hWL hx⟩
    rw [← hSL] at hxTL
    exact hxTL.1
  have hn : Even n := by
    rcases hyp.n_cases with h2 | h4 | h8
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨4, by omega⟩
  refine ⟨hWS, fun x hx => hred.2.2.1.2 x (hWV hx), fun a ha b hb =>
    congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, hWV ha⟩ ⟨b, hWV hb⟩),
    le_normalizer_commutator_of hred.2.1 (sup_le Subgroup.le_normalizer hTL),
    h.sixteen_le_card_commutator hV hn⟩

theorem commutator_le_pCoreOf_F4 (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    ⁅V, L⁆ ≤ pCoreOf 2 (Dp ⊔ sec52S M H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWS, hW2, -, hN, -⟩ := hyp.commutator_facts_F4 h510 h331 hR
  obtain ⟨hST, -, -, -, -, -, -, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hDpL : Dp ≤ L := hyp.Dp_le.trans (hyp.notation59.2.1.1.trans inf_le_left)
  refine le_pCoreOf_of_le_normalizer 2 (hWS.trans le_sup_right) ?_ ?_
  · exact sup_le (hDpL.trans (le_sup_left.trans hN)) (hST.trans (le_sup_right.trans hN))
  · intro w
    exact ⟨1, Subtype.ext (by simpa [pow_one] using hW2 w w.2)⟩

end Hyp5_2_2p

end CFSG.Quasithin.H13
