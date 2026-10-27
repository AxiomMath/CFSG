module

public import Certificates.Data.Kernel.Spor.Fi24PumpK
public import CFSG.Certificates.Kernel.Spor.Fi24BaseSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixPSound

public section

namespace CFSG.KS.Fi24PumpK

open CFSG.KC.Fi24PumpK CFSG.KC.Fi24Base CFSG.KC.Fi24FixP CFSG.KS.Fi24Base
  CFSG.Sporadic.Fi24.Native Finset

variable {f : Nat → Nat → Nat}

theorem letLt_iff (w : List Nat) : letLt w = true ↔ ∀ l ∈ w, l < 26 := by
  induction w with
  | nil => simp [letLt]
  | cons l w ih =>
    change (Nat.blt l 26 && letLt w) = true ↔ _
    rw [Bool.and_eq_true, ih, Nat.blt_eq, List.forall_mem_cons]

theorem repW_succ (w : List Nat) (p : Nat) : repW w (p + 1) = w ++ repW w p := rfl

theorem mem_repW {w : List Nat} {l : Nat} : ∀ p, l ∈ repW w p → l ∈ w
  | 0, h => absurd h List.not_mem_nil
  | p + 1, h => by
    rw [repW_succ, List.mem_append] at h
    rcases h with h | h
    · exact h
    · exact mem_repW p h

theorem apF_eq_foldr : ∀ w : List Nat, (∀ l ∈ w, l < 26) → ∀ x, apF f w x = w.foldr f x
  | [], _, _ => rfl
  | l :: w, hw, x => by
    rw [apF_cons, letF_of_lt (hw l List.mem_cons_self),
      apF_eq_foldr w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) x, List.foldr_cons]

theorem eqB_iff (u v : List Nat) :
    eqB f u v = true ↔ ∀ b ∈ chainBase.toList, apF f u b = apF f v b := by
  unfold eqB
  rw [eqL_eq, List.all_eq_true]
  simp only [beq_iff_eq]

theorem pairOK_spec {A : Nat → Nat → Nat} (hσ : ∀ l < 26, ∀ q < 524288, f l q < 524288)
    (hA : ∀ l < 26, ∀ v q, q < 524288 → (A l v).testBit q = v.testBit (f l q))
    {r v : List Nat} {p n : Nat} (h : pairOK (eqB f) A r v p n = true) :
    (∀ l ∈ r, l < 26) ∧ (∀ l ∈ v, l < 26) ∧
      (∀ b ∈ chainBase.toList, (repW v p).foldr f b = b) ∧
      (∃ b ∈ chainBase.toList, v.foldr f b ≠ b) ∧
      (∀ b ∈ chainBase.toList, (r ++ v).foldr f b = (v ++ r).foldr f b) ∧
      #((range 306936).filter fun x => v.foldr f x = x) = n := by
  unfold pairOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hr, hv⟩, hpow⟩, hne⟩, hcomm⟩, hfix⟩ := h
  rw [letLt_iff] at hr hv
  have hvp : ∀ l ∈ repW v p, l < 26 := fun l hl => hv l (mem_repW p hl)
  have hrv : ∀ l ∈ r ++ v, l < 26 := fun l hl => by
    rcases List.mem_append.1 hl with h | h
    · exact hr l h
    · exact hv l h
  have hvr : ∀ l ∈ v ++ r, l < 26 := fun l hl => by
    rcases List.mem_append.1 hl with h | h
    · exact hv l h
    · exact hr l h
  refine ⟨hr, hv, fun b hb => ?_, ?_, fun b hb => ?_, ?_⟩
  · have := (eqB_iff _ _).1 hpow b hb
    rwa [apF_eq_foldr _ hvp] at this
  · by_contra hc
    push Not at hc
    have : eqB f v [] = true := (eqB_iff _ _).2 fun b hb => by
      rw [apF_eq_foldr _ hv]
      exact hc b hb
    rw [this] at hne
    exact Bool.noConfusion hne
  · have := (eqB_iff _ _).1 hcomm b hb
    rwa [apF_eq_foldr _ hrv, apF_eq_foldr _ hvr] at this
  · exact CFSG.KS.Fi24FixP.fixOK_spec (fun l hl q hq => hσ l (hv l hl) q hq) (fun l hl => hA l (hv l hl)) hfix

end CFSG.KS.Fi24PumpK

end
