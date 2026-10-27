module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3Dc
public import CFSG.Quasithin.Background.E2TwoProofSporGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.J3K

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.Schreier

@[expose] def e9w : List (List ℕ) := [[3, 3, 3, 3], [3, 0, 0, 0]]

@[expose] def e9B : List ℕ := [0, 1, 3, 2]

@[expose] noncomputable def e9F (i : ℕ) : ℕ → ℕ :=
  CFSG.KC.E64F.wordF (CFSG.KD.J3Dc.Lm 3) (e9w.getD i [])

@[expose] noncomputable def e9OK : Bool :=
  e9B.all (fun p => e9F 0 (e9F 0 (e9F 0 p)) == p && e9F 1 (e9F 1 (e9F 1 p)) == p &&
    e9F 0 (e9F 1 p) == e9F 1 (e9F 0 p)) &&
  e9B.any (fun p => e9F 0 p != p) && e9B.any (fun p => e9F 1 p != p) &&
  e9B.any (fun p => e9F 1 p != e9F 0 p) && e9B.any (fun p => e9F 1 p != e9F 0 (e9F 0 p))

theorem e9OK_eq : e9OK = true := by quickRfl

theorem e9_parts :
    (∀ p ∈ e9B, (e9F 0 (e9F 0 (e9F 0 p)) = p ∧ e9F 1 (e9F 1 (e9F 1 p)) = p) ∧
      e9F 0 (e9F 1 p) = e9F 1 (e9F 0 p)) ∧
    (∃ p ∈ e9B, e9F 0 p ≠ p) ∧ (∃ p ∈ e9B, e9F 1 p ≠ p) ∧ (∃ p ∈ e9B, e9F 1 p ≠ e9F 0 p) ∧
    (∃ p ∈ e9B, e9F 1 p ≠ e9F 0 (e9F 0 p)) := by
  have h := e9OK_eq
  unfold e9OK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

@[expose] noncomputable def e9x : ↥j3P := evalElt (gensY 3).toArray (e9w.getD 0 [])

@[expose] noncomputable def e9y : ↥j3P := evalElt (gensY 3).toArray (e9w.getD 1 [])

theorem gensY3_size : (gensY 3).toArray.size = 4 := by
  simp only [List.size_toArray, gensY, List.length_append, List.length_cons, List.length_nil,
    List.length_map]
  decide

theorem e9w_lt {i : ℕ} : ∀ l ∈ e9w.getD i [], l < (gensY 3).toArray.size := by
  rw [gensY3_size]
  intro l hl
  have hi : i < 2 ∨ 2 ≤ i := by omega
  rcases hi with hi | hi
  · interval_cases i <;> simp [e9w] at hl <;> omega
  · rw [List.getD_eq_default _ _ (by simp [e9w]; omega)] at hl
    simp at hl

theorem evalY3_mem (w : List ℕ) (hw : ∀ l ∈ w, l < (gensY 3).toArray.size) :
    evalElt (gensY 3).toArray w ∈ Y 3 := by
  refine evalElt_mem _ (fun l hl => ?_) w hw
  have h := evalElt_getD_mem_closure (gensY 3).toArray hl
  rwa [List.toList_toArray] at h

theorem e9x_mem : e9x ∈ Y 3 := evalY3_mem _ e9w_lt

theorem e9y_mem : e9y ∈ Y 3 := evalY3_mem _ e9w_lt

section Checks


theorem card_Y3 : Nat.card (Y 3) = 9 * Nat.card S := by
  rw [member_card (j := 3) (by norm_num)]
  rfl

theorem map_Y3 (α : MulAut ↥j3P) (hα : S.map α.toMonoidHom = S) :
    (Y 3).map α.toMonoidHom = Y 3 := by
  refine CFSG.Quasithin.E2P.SporB.map_eq_of_unique_card (S_le_Y 3) ?_ α hα
  intro Z hSZ hZc
  obtain ⟨j, hj, rfl⟩ := complete Z hSZ
  have hS0 : 0 < Nat.card S := Nat.card_pos
  rw [card_Y3] at hZc
  unfold memberOrTop at hZc ⊢
  by_cases hj5 : j < 5
  · rw [if_pos hj5] at hZc ⊢
    rw [member_card hj5] at hZc
    have hk : (#[1, 3, 3, 9, 15] : Array ℕ)[j]! = 9 := Nat.eq_of_mul_eq_mul_right hS0 hZc
    interval_cases j
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · rfl
    · exact absurd hk (by decide)
  · rw [if_neg hj5] at hZc
    rw [Subgroup.card_top, card_j3P, card_S] at hZc
    norm_num at hZc

theorem e9_act {i : ℕ} {p : ℕ} (hp : p < 6156) :
    act 6156 (evalElt (gensY 3).toArray (e9w.getD i [])) p = e9F i p := by
  rw [act_evalElt (gensY 3).toArray (tabs (gensY 3).toArray)
    (fun l hl => tabs_getD _ (by rw [tabs_size]; exact hl)) _ e9w_lt p hp]
  exact (CFSG.KC.E64F.wordImg_eq (good_Y 3) _ (by rw [tabs_size]; exact e9w_lt) p hp).1

theorem e9x_act {p : ℕ} (hp : p < 6156) : act 6156 e9x p = e9F 0 p := e9_act hp

theorem e9y_act {p : ℕ} (hp : p < 6156) : act 6156 e9y p = e9F 1 p := e9_act hp

theorem e9B_lt : ∀ p ∈ e9B, p < 6156 := by decide

theorem sep_eq_e9B : CFSG.KD.J3Dc.D.sep = e9B := facts.2.2.2.2.2.1

theorem eq_of_e9B {x y : ↥j3P} (h : ∀ p ∈ e9B, act 6156 x p = act 6156 y p) : x = y :=
  eq_of_act_eq_base e9B_lt (fun g hg => hsep g (by rw [sep_eq_e9B]; exact hg)) h

theorem e9F_lt {i p : ℕ} (hp : p < 6156) : e9F i p < 6156 := by
  rw [← e9_act hp]
  exact act_lt _ hp

theorem j3P_act_pow_three (x : ↥j3P) {p : ℕ} (hp : p < 6156) :
    act 6156 (x ^ 3) p = act 6156 x (act 6156 x (act 6156 x p)) := by
  rw [pow_three, act_mul _ _ hp, act_mul _ _ hp]

theorem e9x_pow_three : e9x ^ 3 = 1 := by
  refine eq_of_e9B fun p hp => ?_
  have hp' := e9B_lt p hp
  rw [act_one hp', j3P_act_pow_three _ hp', e9x_act hp', e9x_act (e9F_lt hp'),
    e9x_act (e9F_lt (e9F_lt hp'))]
  exact (e9_parts.1 p hp).1.1

theorem e9y_pow_three : e9y ^ 3 = 1 := by
  refine eq_of_e9B fun p hp => ?_
  have hp' := e9B_lt p hp
  rw [act_one hp', j3P_act_pow_three _ hp', e9y_act hp', e9y_act (e9F_lt hp'),
    e9y_act (e9F_lt (e9F_lt hp'))]
  exact (e9_parts.1 p hp).1.2

theorem e9x_mul_e9y : e9x * e9y = e9y * e9x := by
  refine eq_of_e9B fun p hp => ?_
  have hp' := e9B_lt p hp
  rw [act_mul _ _ hp', act_mul _ _ hp', e9x_act hp', e9y_act hp', e9x_act (e9F_lt hp'),
    e9y_act (e9F_lt hp')]
  exact (e9_parts.1 p hp).2

theorem e9x_ne_one : e9x ≠ 1 := by
  intro h
  obtain ⟨p, hp, hne⟩ := e9_parts.2.1
  have hp' := e9B_lt p hp
  rw [← e9x_act hp', h, act_one hp'] at hne
  exact hne rfl

theorem e9y_not_mem_zpowers : e9y ∉ Subgroup.zpowers e9x := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have e : e9x ^ k = e9x ^ (k % 3) := zpow_eq_zpow_emod' k e9x_pow_three
  rw [e] at hk
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · rw [h0, zpow_zero] at hk
    obtain ⟨p, hp, hne⟩ := e9_parts.2.2.1
    have hp' := e9B_lt p hp
    rw [← e9y_act hp', ← hk, act_one hp'] at hne
    exact hne rfl
  · rw [h1, zpow_one] at hk
    obtain ⟨p, hp, hne⟩ := e9_parts.2.2.2.1
    have hp' := e9B_lt p hp
    rw [← e9y_act hp', ← e9x_act hp', hk] at hne
    exact hne rfl
  · rw [h2, zpow_two] at hk
    obtain ⟨p, hp, hne⟩ := e9_parts.2.2.2.2
    have hp' := e9B_lt p hp
    have e1 : e9F 0 (e9F 0 p) = act 6156 e9y p := by
      rw [← hk, act_mul _ _ hp', e9x_act hp', e9x_act (e9F_lt hp')]
    rw [e1, e9y_act hp'] at hne
    exact hne rfl

end Checks

end CFSG.QuasithinUnique.Ch1.SporLat.J3K

end
