module

public import CFSG.Certificates.Kernel.SmithL6KMeet
public import Certificates.Data.Kernel.SmithL6KA

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

theorem sumRowK_get {B w0 m0 : Nat} :
    ∀ {W M : List Nat}, sumRowK B w0 m0 W M = true → ∀ j < W.length, j < M.length →
      (atLeast4 (m0 &&& M.getD j 0) || !B.testBit (w0 ^^^ W.getD j 0)) = true
  | [], _, _, j, hj, _ => by simp at hj
  | _ :: _, [], _, j, _, hm => by simp at hm
  | w :: W, m :: M, h, j, hj, hm => by
    unfold sumRowK at h
    rw [Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      simpa using sumRowK_get h.2 j (by simpa using hj) (by simpa using hm)

theorem four_le_ker {S : Finset Nat} (hS : XorClosed S) (h8 : S.card = 8) (φ : Nat) :
    4 ≤ (S.filter fun x => form φ x = false).card := by
  have hsum := Finset.card_filter_add_card_filter_not (s := S) (fun x => form φ x = false)
  rw [h8] at hsum
  by_cases hN : ∃ w ∈ S, form φ w = true
  · obtain ⟨w, hw, hφw⟩ := hN
    have hle : (S.filter fun x => ¬ form φ x = false).card ≤
        (S.filter fun x => form φ x = false).card := by
      refine Finset.card_le_card_of_injOn (fun x => x ^^^ w) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Bool.not_eq_false] at hx ⊢
        refine ⟨hS.2.2 x hx.1 w hw, ?_⟩
        rw [form_xor_right, hx.2, hφw]
        rfl
      · intro x _ y _ e
        have e' := congrArg (· ^^^ w) e
        simpa [Nat.xor_assoc] using e'
    omega
  · have h0 : (S.filter fun x => ¬ form φ x = false).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx hφ
      exact hN ⟨x, hx, by simpa using hφ⟩
    omega

end CFSG.SmithL6.K
