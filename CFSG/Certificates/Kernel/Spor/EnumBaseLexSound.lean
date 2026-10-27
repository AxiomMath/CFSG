module

public import Certificates.Data.Kernel.Spor.EnumBaseLex
public import CFSG.Certificates.Kernel.Spor.EnumBaseSound

public section

namespace CFSG.KS.EnumBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

theorem lexPosK_spec {k cnt : Nat} {PL POS : Nat → Nat} {i : Nat}
    (h : lexPosK k cnt PL POS i = true) :
    (0 < i → i + 1 < cnt →
      lexLtK (parOf PL i) (labOf PL i) (parOf PL (i + 1)) (labOf PL (i + 1)) = true) ∧
    ∀ j < k, r32 POS (i * k + j) = 0 ∨
      lexLtK i j (parOf PL (r32 POS (i * k + j))) (labOf PL (r32 POS (i * k + j))) = false := by
  unfold lexPosK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hi hc => ?_, fun j hj => ?_⟩
  · have e : Nat.beq i 0 = false := by rw [beq_eq]; simpa using Nat.pos_iff_ne_zero.1 hi
    rw [bIf_eq, e, if_neg Bool.false_ne_true, bIf_eq, if_pos (by rw [blt_eq]; exact decide_eq_true hc)]
      at h1
    exact h1
  · have hq := allN_spec h2 j hj
    rw [strictB_eq] at hq
    simp only [Nat.add_eq, Nat.mul_eq] at hq
    by_cases e : r32 POS (i * k + j) = 0
    · exact Or.inl e
    · right
      have e' : Nat.beq (r32 POS (i * k + j)) 0 = false := by rw [beq_eq]; simpa using e
      rw [bIf_eq, e', if_neg Bool.false_ne_true, bIf_eq] at hq
      cases hl : lexLtK i j (parOf PL (r32 POS (i * k + j))) (labOf PL (r32 POS (i * k + j)))
      · rfl
      · rw [hl, if_pos rfl] at hq
        exact absurd hq Bool.false_ne_true

end CFSG.KS.EnumBase

end
