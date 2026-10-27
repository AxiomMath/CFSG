
module

public import Certificates.Data.Kernel.SporSch.J4SCols
public import CFSG.Sporadic.Schreier.J4SCommGenInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch.C11

private theorem xorSubK_eq : ∀ (V : List Nat) (m : Nat),
    xorSubK V m = CFSG.Sporadic.J4Schreier.xorSub V m
  | [], _ => rfl
  | v :: V, m => by
    change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 v (Nat.beq (Nat.mod m 2) 1))
      (xorSubK V (Nat.div m 2)) = _
    rw [xorSubK_eq V, CFSG.Sporadic.J4Schreier.xorSub, CFSG.KS.Raw.Orb.nIf_eq]
    by_cases hm : m % 2 = 1
    · have hb : Nat.beq (Nat.mod m 2) 1 = true := Nat.beq_eq.mpr hm
      rw [if_pos hb, if_pos hm]
      rfl
    · have hb : ¬ Nat.beq (Nat.mod m 2) 1 = true := fun h => hm (Nat.eq_of_beq_eq_true h)
      rw [if_neg hb, if_neg hm]
      rfl

private theorem testBit_foldr_or (g : Nat → Nat) (k : Nat) : ∀ (l : List Nat),
    (l.foldr (fun c s => s ||| (1 <<< g c)) 0).testBit k = true ↔ ∃ c ∈ l, g c = k
  | [] => by simp
  | c :: l => by
    rw [List.foldr_cons, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_foldr_or g k l, decide_eq_true_iff]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm

private theorem full_cover (g : Nat → Nat) {N : Nat}
    (h : (List.range N).foldr (fun c s => s ||| (1 <<< g c)) 0 = (1 <<< N) - 1) :
    ∀ k < N, ∃ c < N, g c = k := by
  intro k hk
  have hb : ((List.range N).foldr (fun c s => s ||| (1 <<< g c)) 0).testBit k = true := by
    rw [h, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    simpa using hk
  obtain ⟨c, hc, e⟩ := (testBit_foldr_or g k _).1 hb
  exact ⟨c, List.mem_range.1 hc, e⟩

theorem span_sound {V : List Nat} (h : spanK V = true) :
    ∀ c < 2048, ∃ m < 2048, CFSG.Sporadic.J4Schreier.xorSub V m = c := by
  unfold spanK at h
  have e := Nat.eq_of_beq_eq_true h
  rw [CFSG.KS.Raw.Orb.foldN_eq] at e
  intro c hc
  obtain ⟨m, hm, e⟩ := full_cover (xorSubK V) (N := 2048) e c hc
  exact ⟨m, hm, by rw [← xorSubK_eq]; exact e⟩

end CFSG.KS.SporSch.C11

end
