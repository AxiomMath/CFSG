
module

public import Certificates.Data.Kernel.OpsF2KFusQ
public import CFSG.Certificates.Kernel.OpsF2KMcertSound
public import CFSG.Certificates.Kernel.Co1F2Sound
import all CFSG.Certificates.Kernel.OpsF2KMcertSound
import all CFSG.Certificates.Kernel.OpsF2KEnumSound
import all CFSG.Certificates.Kernel.LocalCompCubSound
import CFSG.Certificates.Kernel.Misc.F2BfsRec2Sound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KC.Loop CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native
open CFSG.KC.Co1F2 (unpackR)
open CFSG.KC.Misc.G24 (mulF2)
open CFSG.KC.F2BfsRec (mulF2_eq_mulF)

theorem qIf_eq (c : Bool) (t e : Nat) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem qStrict_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem qBeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hc : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hc) h

theorem pqF_succ (d n X e : Nat) : pqF d (n + 1) X e = nIf(Nat.beq e 0, idF d, nIf(Nat.beq e 1, X,
    strictN (mulF2 d X X) fun S => strictN (pqF d n S (Nat.shiftRight e 1)) fun Y =>
      nIf(Nat.beq (Nat.land e 1) 1, mulF2 d X Y, Y))) := rfl

theorem unpackR_pqF (d : Nat) : ∀ n X e, e < 2 ^ n →
    unpackR d (pqF d n X e) = (ops2 d).pow (unpackR d X) e := by
  intro n
  induction n with
  | zero =>
    intro X e he
    have h0 : e = 0 := by simpa using he
    subst h0
    unfold Ops.pow
    rw [if_pos rfl]
    exact unpackR_idF_eq_one d
  | succ n ih =>
    intro X e he
    rw [pqF_succ]
    simp only [qIf_eq, qStrict_eq, mulF2_eq_mulF]
    unfold Ops.pow
    by_cases h0 : e = 0
    · subst h0
      have hb : Nat.beq 0 0 = true := rfl
      rw [if_pos hb, if_pos rfl]
      exact unpackR_idF_eq_one d
    rw [qBeq_false h0, if_neg Bool.false_ne_true, if_neg h0]
    by_cases h1 : e = 1
    · subst h1
      have hb : Nat.beq 1 1 = true := rfl
      rw [if_pos hb, if_pos rfl]
    rw [qBeq_false h1, if_neg Bool.false_ne_true, if_neg h1]
    have hs : Nat.shiftRight e 1 = e / 2 := by
      change e >>> 1 = e / 2
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    have ha : Nat.land e 1 = e % 2 := Nat.and_one_is_mod e
    have hlt : e / 2 < 2 ^ n := by
      rw [pow_succ] at he
      omega
    have key := ih (mulF d X X) (e / 2) hlt
    rw [unpackR_mulF] at key
    rw [hs, ha]
    dsimp only
    by_cases ho : e % 2 = 1
    · have hb : Nat.beq (e % 2) 1 = true := by rw [ho]; rfl
      rw [if_pos hb, if_pos ho, unpackR_mulF, key]
    · rw [qBeq_false ho, if_neg Bool.false_ne_true, if_neg ho, key]

theorem pqF_lt (d : Nat) : ∀ n X e, X < 2 ^ (d * d) → pqF d n X e < 2 ^ (d * d) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ => idF_lt d
  | succ n ih =>
    intro X e hX
    rw [pqF_succ]
    simp only [qIf_eq, qStrict_eq, mulF2_eq_mulF]
    split
    · exact idF_lt d
    split
    · exact hX
    split
    · exact mulF_lt _ _ _
    · exact ih _ _ (mulF_lt _ _ _)

theorem powK_lt (d X e : Nat) : powK d X e < 2 ^ (d * d) := by
  change strictN (mulF d (CFSG.KC.LocalComp.Cub.powFR d X e 16 15)
    (CFSG.KC.LocalComp.Cub.powFR d X e 16 15))
    (fun sq => nIf(bit e ((16 - 1) - 15), mulF d sq X, sq)) < _
  rw [qStrict_eq, qIf_eq]
  split <;> exact mulF_lt _ _ _

theorem pqK_eq_powK {d X e : Nat} (hX : X < 2 ^ (d * d)) (he : e < 2 ^ 16) :
    pqK d X e = powK d X e :=
  unpackR_inj (pqF_lt d 16 X e hX) (powK_lt d X e) (by rw [pqK, unpackR_pqF d 16 X e he,
    unpackR_powK he])

theorem mulF_idF_right {d Y : Nat} (hY : Y < 2 ^ (d * d)) : mulF d Y (idF d) = Y :=
  CFSG.KC.F2Mat.matOfF_inj (mulF_lt _ _ _) hY (by
    rw [CFSG.KC.F2Mat.matOfF_mulF, CFSG.KC.F2Mat.matOfF_idF, mul_one])

theorem getR_lt {d : Nat} {R : List Nat} (hR : ∀ x ∈ R, x < 2 ^ (d * d)) (i : Nat) :
    getR d R i < 2 ^ (d * d) := by
  unfold getR
  rw [List.getD_eq_getElem?_getD]
  cases h : R[i]? with
  | none => exact idF_lt d
  | some x => exact hR x (List.mem_of_getElem? h)

theorem set_lt {d k v : Nat} {R : List Nat} (hR : ∀ x ∈ R, x < 2 ^ (d * d))
    (hv : v < 2 ^ (d * d)) : ∀ x ∈ R.set k v, x < 2 ^ (d * d) := fun x hx =>
  (List.mem_or_eq_of_mem_set hx).elim (hR x) fun h => h ▸ hv

theorem stepQ_eq {d : Nat} {R : List Nat} (hR : ∀ x ∈ R, x < 2 ^ (d * d)) :
    ∀ op : Op, expOK op = true →
      stepQ d R op = stepK d R op ∧ ∀ x ∈ stepK d R op, x < 2 ^ (d * d)
  | .mul i j k, _ => by
    refine ⟨?_, set_lt hR (mulF_lt _ _ _)⟩
    change R.set k (mulF2 d (getR d R i) (getR d R j)) = R.set k (mulF d (getR d R i) (getR d R j))
    rw [mulF2_eq_mulF]
  | .pow e i k, he => by
    have he' : e < 2 ^ 16 := by simpa [expOK] using he
    refine ⟨?_, set_lt hR (powK_lt _ _ _)⟩
    change R.set k (pqK d (getR d R i) e) = R.set k (powK d (getR d R i) e)
    rw [pqK_eq_powK (getR_lt hR i) he']

theorem foldl_stepQ_eq (d : Nat) : ∀ (prog : List Op) (R : List Nat),
    (∀ x ∈ R, x < 2 ^ (d * d)) → prog.all expOK = true →
      prog.foldl (stepQ d) R = prog.foldl (stepK d) R ∧
        ∀ x ∈ prog.foldl (stepK d) R, x < 2 ^ (d * d)
  | [], _, hR, _ => ⟨rfl, hR⟩
  | op :: prog, R, hR, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨e, hb⟩ := stepQ_eq hR op h.1
    rw [List.foldl_cons, List.foldl_cons, e]
    exact foldl_stepQ_eq d prog _ hb h.2

theorem runQ_eq {d A B n : Nat} {prog : List Op} (hs : seedsOK d A B = true)
    (hexp : prog.all expOK = true) :
    runQ d A B n prog = runK d A B n prog ∧ ∀ x ∈ runK d A B n prog, x < 2 ^ (d * d) := by
  simp only [seedsOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨-, hA⟩, hB⟩ := hs
  refine foldl_stepQ_eq d prog _ ?_ hexp
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨r, -, rfl⟩ := hx
  split
  · exact hA
  split
  · exact hB
  · exact idF_lt d

theorem evalWQ_eq {d n : Nat} {R : List Nat} (hR : ∀ x ∈ R, x < 2 ^ (d * d)) :
    ∀ w : Word, wordLtK n w = true → evalWQ d R w = evalWK d R w
  | [], _ => rfl
  | [p], h => by
    have he : p.2 < 2 ^ 16 := by
      simp only [wordLtK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      exact h.2
    change pqK d (getR d R p.1) p.2 = mulF d (powK d (getR d R p.1) p.2) (idF d)
    rw [pqK_eq_powK (getR_lt hR _) he, mulF_idF_right (powK_lt _ _ _)]
  | p :: q :: w, h => by
    have h' := h
    simp only [wordLtK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h'
    have ht : wordLtK n (q :: w) = true := by
      simp only [wordLtK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
      exact h'.2
    change mulF2 d (pqK d (getR d R p.1) p.2) (evalWQ d R (q :: w)) =
      mulF d (powK d (getR d R p.1) p.2) (evalWK d R (q :: w))
    rw [mulF2_eq_mulF, pqK_eq_powK (getR_lt hR _) h'.1.2, evalWQ_eq hR (q :: w) ht]

theorem factK_of_Q {d n : Nat} {R : List Nat} (hR : ∀ x ∈ R, x < 2 ^ (d * d)) :
    ∀ f : MFact, factQ d R n f = true → factK d R n f = true
  | .ord r e, h => by
    simp only [factQ, factK, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨hr, he⟩, he16⟩, hb⟩ := h
    rw [← pqK_eq_powK (getR_lt hR r) (by omega)]
    exact ⟨⟨⟨hr, he⟩, he16⟩, hb⟩
  | .conj g u w, h => by
    simp only [factQ, factK, Bool.and_eq_true, decide_eq_true_eq, mulF2_eq_mulF] at h ⊢
    obtain ⟨⟨⟨hg, hu⟩, hw⟩, hb⟩ := h
    rw [← evalWQ_eq hR u hu, ← evalWQ_eq hR w hw]
    exact ⟨⟨⟨hg, hu⟩, hw⟩, hb⟩
  | .ne w₁ w₂ t, h => by
    simp only [factQ, factK, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨h1, h2⟩, ht⟩, hb⟩ := h
    rw [← evalWQ_eq hR w₁ h1, ← evalWQ_eq hR w₂ h2]
    exact ⟨⟨⟨h1, h2⟩, ht⟩, hb⟩
  | .eq w₁ w₂, h => by
    simp only [factQ, factK, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, hb⟩ := h
    rw [← evalWQ_eq hR w₁ h1, ← evalWQ_eq hR w₂ h2]
    exact ⟨⟨h1, h2⟩, hb⟩

theorem fusK_of_Q {d A B nregs : Nat} {prog : List Op} {D : CFSG.RankThree.PartOne.CTP.Fus.Spec}
    (h : fusQ d A B nregs prog D = true) : fusK d A B nregs prog D = true := by
  simp only [fusQ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hexp⟩, hn⟩, hprog⟩, hf⟩, hrA⟩, hrB⟩, hbA⟩, hbB⟩, hwf⟩ := h
  obtain ⟨hR, hbd⟩ := runQ_eq (n := nregs) hs hexp
  rw [hR] at hf hbA hbB
  simp only [fusK, mcertK, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hexp⟩, hn⟩, hprog⟩, ?_⟩, hrA⟩, hrB⟩, hbA⟩, hbB⟩, hwf⟩
  rw [List.all_eq_true] at hf ⊢
  exact fun f hf' => factK_of_Q hbd f (hf f hf')

theorem fusCheck_of_Q {d A B nregs : Nat} {csA csB : List Char} {sA sB : String}
    {prog : List Op} {D : CFSG.RankThree.PartOne.CTP.Fus.Spec}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : sA = String.ofList csA) (hsB : sB = String.ofList csB)
    (h : fusQ d A B nregs prog D = true) :
    CFSG.RankThree.PartOne.CTP.Fus.fusCheck (ops2 d) sA sB nregs prog D = true :=
  fusCheck_of_K hA hB hsA hsB (fusK_of_Q h)

end CFSG.KC.OpsF2K

end
