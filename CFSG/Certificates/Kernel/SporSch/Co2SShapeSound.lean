
module

public import Certificates.Data.Kernel.SporSch.Co2SShape
public import CFSG.Sporadic.Co2Schreier.WitCheckInputs
import CFSG.Certificates.Kernel.Spor.DistinctSound
public import CFSG.Certificates.Kernel.Spor.Co2ChainSound

public section

namespace CFSG.KS.Co2SShape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Shape CFSG.Sporadic.Co2Schreier
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2.Native

theorem mapL_eq {α β : Type} (f : α → β) : ∀ l : List α, mapL f l = l.map f
  | [] => rfl
  | x :: l => congrArg (List.cons (f x)) (mapL_eq f l)

theorem sndL_eq (l : List Nat) : sndL l = l.getD 1 0 := by
  rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

theorem eqNLL_iff : ∀ a b : List (List Nat), eqNLL a b = true ↔ a = b
  | [], [] => iff_of_true rfl rfl
  | [], _ :: _ => iff_of_false Bool.false_ne_true (List.cons_ne_nil _ _).symm
  | _ :: _, [] => iff_of_false Bool.false_ne_true (List.cons_ne_nil _ _)
  | x :: xs, y :: ys => by
    change Bool.rec (motive := fun _ => Bool) false (eqNLL xs ys) (eqNL x y) = true ↔ _
    rw [bAnd_iff, eqNLL_iff xs ys, eqNL_iff, List.cons.injEq]

theorem rowsK_iff (n b : Nat) (l : List Nat) :
    rowsK n b l = true ↔ (l.length == n && l.all (· < b)) = true := by
  unfold rowsK
  rw [bAnd_iff, Nat.beq_eq, lenL_eq, allL_eq, Bool.and_eq_true, beq_iff_eq]
  simp only [Nat.blt_eq, decide_eq_true_eq, List.all_eq_true]

theorem extWordsOK_of {k : Nat} {D : List (List Int)} (h : wordsL k D 0 = true) :
    extWordsOK k D = true := by
  unfold extWordsOK
  rw [List.all_eq_true]
  intro t ht
  have := wordsL_spec k D 0 h t (List.mem_range.1 ht)
  rwa [Nat.zero_add, Nat.add_comm] at this

theorem localShapeK_sound {L : LocalCert} (h : localShapeK L = true) : localShapeOK L = true := by
  unfold localShapeK at h
  simp only [bAnd_iff, Nat.beq_eq, lenL_eq, allL_eq, eqNL_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := h
  unfold localShapeOK
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  simp only [List.all_eq_true, lettersK_eq, Nat.beq_eq, beq_iff_eq] at *
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, extWordsOK_of h10, h11, h12, h13, h14, h15, h16,
    h17, extWordsOK_of h18, h19, h20, h21, h22, h23, h24, chainK_sound h25, chainK_sound h26,
    chainK_sound h27, chainK_sound h28, chainK_sound h29, chainK_sound h30⟩

theorem witShapeK_sound {W : WitCert} (h : witShapeK W = true) : witShapeOK W = true := by
  unfold witShapeK at h
  simp only [bAnd_iff, Nat.beq_eq, lenL_eq, allL_eq, eqNL_iff, eqNLL_iff, mapL_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩ := h
  obtain ⟨hnd, hb⟩ := distinctL_sound h24
  unfold witShapeOK rows22OK
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, decide_eq_true_eq]
  simp only [List.all_eq_true, rowsK_iff, lettersK_eq, Bool.and_eq_true, beq_iff_eq,
    Nat.blt_eq, decide_eq_true_eq, Nat.beq_eq, sndL_eq, bAnd_iff, and_assoc, Nat.reducePow] at *
  exact ⟨h1, h2, h3, h4, h5, chainK_sound h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, fun x hx => (hb x hx).1, hnd, h25, extWordsOK_of h26, h27,
    h28, h29, h30, h31.1, h31.2, h32, h33, h34⟩

end CFSG.KS.Co2SShape

end
