module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcVz
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3Semi

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Fischer
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}

theorem le_M1_of_normalizes_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {A Y : Subgroup G} (hZA : sec53ZS T L < A) (hAV : A ≤ pCoreOf 2 L)
    (hTY : T ≤ Y) (hYA : Y ≤ Subgroup.normalizer (A : Set G)) : Y ≤ sec53M1 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨⟨-, -, hU1, -, -⟩, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  have hsup := sup_sec53_F4 h527 hyp hty hf
  have hV₁T : pCoreOf 2 L ≤ T := (le_sup_left.trans hsup.le).trans inf_le_left
  have hab := (l3facts_two_F4 h527 hyp hty hf).1
  have hA : A ≠ ⊥ := (bot_le.trans_lt hZA).ne'
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  refine le_of_normalizes_aux h.qtke h.sylow hV₁T (l3facts_one_F4 h527 h531 hyp hty hf).le
    ((l3facts_three_F4 h527 hyp hty hf).2.1 A hZA hAV).le
    (fun a ha b hb => comm_of_isElemAbelian hab ha hb) hZA.le hAV hA ?_ hTY hYA
  refine normalizer_le_of_isUniqueM hU1 (fun h0 => hA (le_bot_iff.mp (h0 ▸ hAV)))
    (pCoreOf_isPGroup 2 L) (sup_le ?_ (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
  exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L)

theorem le_M2_of_normalizes_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {A Y : Subgroup G} (hZA : sec53ZS T L < A)
    (hAV : A ≤ pCoreOf 2 (oTwoUpper H)) (hTY : T ≤ Y)
    (hYA : Y ≤ Subgroup.normalizer (A : Set G)) : Y ≤ sec53M2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨⟨-, -, -, hU2, -⟩, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  have hsup := sup_sec53_F4 h527 hyp hty hf
  have hV₂T : pCoreOf 2 (oTwoUpper H) ≤ T := (le_sup_right.trans hsup.le).trans inf_le_left
  have hab := (l3facts_two_F4 h527 hyp hty hf).2.1
  have hA : A ≠ ⊥ := (bot_le.trans_lt hZA).ne'
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  refine le_of_normalizes_aux h.qtke h.sylow hV₂T (l3facts_one_F4 h527 h531 hyp hty hf).le
    ((l3facts_three_F4 h527 hyp hty hf).2.2 A hZA hAV).le
    (fun a ha b hb => comm_of_isElemAbelian hab ha hb) hZA.le hAV hA ?_ hTY hYA
  refine normalizer_le_of_isUniqueM hU2 (fun h0 => hA (le_bot_iff.mp (h0 ▸ hAV)))
    (pCoreOf_isPGroup 2 _) (sup_le ?_ (hTK.trans (normalizer_le_normalizer_pCoreOf 2 _)))
  exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 _)

end CFSG.Quasithin.H13.Sec53L3
