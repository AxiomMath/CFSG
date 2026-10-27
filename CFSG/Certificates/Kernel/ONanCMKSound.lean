module

public import Certificates.Data.Kernel.ONanCMK
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp

public section

namespace CFSG.OddStandard.ONanRec.CMK

open CFSG.OddStandard.ONanRec.CM CFSG.KC.Enum CFSG.KS CFSG.KS.PK

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem packL_cons (x : Nat) (l : List Nat) : packL (x :: l) = x ||| (packL l <<< 9) := rfl

theorem packL_eq : ∀ {l : List Nat}, (∀ x ∈ l, x < 2 ^ 9) →
    packL l = enc 9 (fun i => l.getD i 0) l.length
  | [], _ => rfl
  | x :: l, hl => by
    have hx : x < 2 ^ 9 := hl x (by simp)
    have h1 : enc 9 (fun i => (x :: l).getD i 0) 1 = x := by simp [enc]
    have h2 : enc 9 (fun i => (x :: l).getD (1 + i) 0) l.length
        = enc 9 (fun i => l.getD i 0) l.length :=
      enc_congr fun i _ => by rw [Nat.add_comm 1 i, List.getD_cons_succ]
    rw [packL_cons, lor_shiftLeft_eq_add hx, packL_eq (fun y hy => hl y (by simp [hy])),
      List.length_cons, Nat.add_comm l.length 1, enc_add, h1, h2, Nat.mul_one]

theorem getD_lt {l : List Nat} {i : Nat} (hi : i < l.length) {P : Nat → Prop}
    (h : ∀ x ∈ l, P x) : P (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h _ (List.getElem_mem hi)

theorem fd_packL {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ 9) {i : Nat} (hi : i < l.length) :
    fd 9 (packL l) i = l.getD i 0 := by
  rw [packL_eq hl]
  refine fd_enc (fun j hj => getD_lt hj hl) hi

theorem fd_idK {x : Nat} (hx : x < 480) : fd 9 idK x = x := by
  unfold idK
  rw [fd_packL (fun y hy => by simp at hy; omega) (by simpa using hx)]
  simp [List.getD_eq_getElem?_getD, hx]

theorem fd_mulK (p q : Nat) {x : Nat} (hx : x < 480) : fd 9 (mulK p q) x = fd 9 p (fd 9 q x) := by
  unfold mulK
  exact fd_pcomp (by decide) 9 p q hx

theorem lenL_eq : ∀ l : List Nat, lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenL_eq l)

theorem allLt_spec : ∀ {l : List Nat}, allLt l = true → ∀ x ∈ l, x < 480
  | [], _, _, hx => absurd hx List.not_mem_nil
  | y :: l, h, x, hx => by
    have e : allLt (y :: l) = (Nat.blt y 480 && allLt l) := rfl
    rw [e, Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact allLt_spec h.2 x hx

theorem getElem!_eq_getD {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    a[i]! = a.toList.getD i default := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases a[i]? <;> rfl

theorem ap_eq (t : Tab) (x : Nat) : ap t x = t.toList.getD x 0 := getElem!_eq_getD t x

theorem compTab_size (n : Nat) (s t : Tab) : (compTab n s t).size = n := by simp [compTab]

theorem idTab_size (n : Nat) : (idTab n).size = n := by simp [idTab]

theorem ap_compTab {n : Nat} {s t : Tab} {x : Nat} (hx : x < n) :
    ap (compTab n s t) x = ap s (ap t x) := by
  have hs : x < (compTab n s t).size := by rw [compTab_size]; exact hx
  conv_lhs => unfold ap
  rw [getElem!_pos (compTab n s t) x hs]
  simp [compTab]

theorem ap_idTab {n x : Nat} (hx : x < n) : ap (idTab n) x = x := by
  have hs : x < (idTab n).size := by rw [idTab_size]; exact hx
  unfold ap
  rw [getElem!_pos (idTab n) x hs]
  simp [idTab]

theorem wordTab_size (n : Nat) (L : Array Tab) : ∀ w : List Nat, (wordTab n L w).size = n
  | [] => idTab_size n
  | c :: w => compTab_size n L[c]! (wordTab n L w)

theorem beq_of_ap {n : Nat} {A B : Tab} (hA : A.size = n) (hB : B.size = n)
    (h : ∀ x < n, ap A x = ap B x) : (A == B) = true := by
  rw [beq_iff_eq]
  refine Array.ext (by rw [hA, hB]) fun i hi hi' => ?_
  have e := h i (by omega)
  unfold ap at e
  rwa [getElem!_pos A i hi, getElem!_pos B i hi'] at e

theorem lettersK_spec (hL : lettersK = true) :
    (∀ i < 6, lenL (genL i) = 480 ∧ allLt (genL i) = true) ∧
      ∀ i < 6, mulK (letK (2 * i + 1)) (letK (2 * i)) = idK ∧
        mulK (letK (2 * i)) (letK (2 * i + 1)) = idK := by
  unfold lettersK at hL
  simpa only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] using hL

theorem gen_ap (hL : lettersK = true) {i : Nat} (hi : i < 6) {y : Nat} (hy : y < 480) :
    ap cmGenTabs[i]! y = fd 9 (genK i) y ∧ fd 9 (genK i) y < 480 := by
  obtain ⟨hlen, hlt⟩ := (lettersK_spec hL).1 i hi
  rw [lenL_eq] at hlen
  have hl := allLt_spec hlt
  have e : ap cmGenTabs[i]! y = (genL i).getD y 0 := by
    rw [ap_eq, getElem!_eq_getD]
    rfl
  have hy' : y < (genL i).length := by omega
  have e' : fd 9 (genK i) y = (genL i).getD y 0 :=
    fd_packL (fun x hx => Nat.lt_trans (hl x hx) (by decide)) hy'
  rw [e, e']
  exact ⟨rfl, getD_lt hy' hl⟩

theorem tab_getElem! (a : Array Tab) (i : Nat) : a[i]! = a.toList.getD i #[] := by
  rw [getElem!_eq_getD]
  rfl

theorem cmLetters_toList : cmLetters.toList =
    [cmGenTabs[0]!, cmGenTabs[0]!, cmGenTabs[1]!, cmGenTabs[1]!, cmGenTabs[2]!, cmGenTabs[2]!,
      cmGenTabs[3]!, cmGenTabs[3]!, cmGenTabs[4]!, cmGenTabs[4]!, cmGenTabs[5]!,
      compTab 480 cmGenTabs[5]! (compTab 480 cmGenTabs[5]! cmGenTabs[5]!)] := by
  simp only [cmLetters, List.toList_toArray]

theorem letter_ap (hL : lettersK = true) {c : Nat} (hc : c < 12) {y : Nat} (hy : y < 480) :
    ap cmLetters[c]! y = fd 9 (letK c) y ∧ fd 9 (letK c) y < 480 := by
  rw [tab_getElem!, cmLetters_toList]
  unfold letK lettersL
  match c, hc with
  | 0, _ =>
    simp only [List.getD_cons_zero]
    exact gen_ap hL (i := 0) (by decide) hy
  | 1, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 0) (by decide) hy
  | 2, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 1) (by decide) hy
  | 3, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 1) (by decide) hy
  | 4, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 2) (by decide) hy
  | 5, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 2) (by decide) hy
  | 6, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 3) (by decide) hy
  | 7, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 3) (by decide) hy
  | 8, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 4) (by decide) hy
  | 9, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 4) (by decide) hy
  | 10, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact gen_ap hL (i := 5) (by decide) hy
  | n + 12, h => exact absurd h (by omega)
  | 11, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    obtain ⟨h1, h1'⟩ := gen_ap hL (i := 5) (by decide) hy
    obtain ⟨h2, h2'⟩ := gen_ap hL (i := 5) (by decide) h1'
    obtain ⟨h3, h3'⟩ := gen_ap hL (i := 5) (by decide) h2'
    rw [ap_compTab hy, ap_compTab hy, fd_mulK _ _ hy, fd_mulK _ _ hy, h1, h2, h3]
    exact ⟨rfl, h3'⟩

theorem wordTab_nil (n : Nat) (L : Array Tab) : wordTab n L [] = idTab n := rfl

theorem wordTab_cons (n : Nat) (L : Array Tab) (c : Nat) (w : List Nat) :
    wordTab n L (c :: w) = compTab n L[c]! (wordTab n L w) := rfl

theorem ptK_cons (c : Nat) (w : List Nat) (x : Nat) : ptK (c :: w) x = fd 9 (letK c) (ptK w x) :=
  rfl

theorem wordTab_ap' {L : Array Tab}
    (hL : ∀ c < 12, ∀ y < 480, ap L[c]! y = fd 9 (letK c) y ∧ fd 9 (letK c) y < 480) :
    ∀ w : List Nat, (∀ c ∈ w, c < 12) →
      ∀ x < 480, ap (wordTab 480 L w) x = ptK w x ∧ ptK w x < 480
  | [], _, x, hx => by
    rw [wordTab_nil, ap_idTab hx]
    exact ⟨rfl, hx⟩
  | c :: w, hw, x, hx => by
    obtain ⟨h1, h2⟩ := wordTab_ap' hL w (fun d hd => hw d (List.mem_cons_of_mem c hd)) x hx
    obtain ⟨h3, h4⟩ := hL c (hw c List.mem_cons_self) _ h2
    rw [wordTab_cons, ptK_cons, ap_compTab hx, h1]
    exact ⟨h3, h4⟩

theorem wordTab_ap (hL : lettersK = true) (w : List Nat) (hw : ∀ c ∈ w, c < 12) {x : Nat}
    (hx : x < 480) : ap (wordTab 480 cmLetters w) x = ptK w x ∧ ptK w x < 480 :=
  wordTab_ap' (fun _ hc _ hy => letter_ap hL hc hy) w hw x hx

theorem fd_wordK : ∀ w : List Nat, ∀ x < 480, fd 9 (wordK w) x = ptK w x
  | [], _, hx => fd_idK hx
  | c :: w, x, hx => by
    have e : wordK (c :: w) = mulK (letK c) (wordK w) := strictN_eq' _ _
    rw [e, fd_mulK _ _ hx, fd_wordK w x hx]
    rfl

theorem cmLettersOK_of (hL : lettersK = true) : cmLettersOK = true := by
  have hp := (lettersK_spec hL).2
  unfold cmLettersOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, allBelow, decide_eq_true_eq]
  refine ⟨fun c hc p hp' => ?_, fun i hi => ⟨?_, ?_⟩⟩
  · rw [(letter_ap hL hc hp').1]
    exact (letter_ap hL hc hp').2
  · refine beq_of_ap (compTab_size _ _ _) (idTab_size 480) fun x hx => ?_
    obtain ⟨a1, a2⟩ := letter_ap hL (c := 2 * i) (by omega) hx
    obtain ⟨b1, -⟩ := letter_ap hL (c := 2 * i + 1) (by omega) a2
    rw [ap_compTab hx, a1, b1, ← fd_mulK _ _ hx, (hp i hi).1, fd_idK hx, ap_idTab hx]
  · refine beq_of_ap (compTab_size _ _ _) (idTab_size 480) fun x hx => ?_
    obtain ⟨a1, a2⟩ := letter_ap hL (c := 2 * i + 1) (by omega) hx
    obtain ⟨b1, -⟩ := letter_ap hL (c := 2 * i) (by omega) a2
    rw [ap_compTab hx, a1, b1, ← fd_mulK _ _ hx, (hp i hi).2, fd_idK hx, ap_idTab hx]

theorem cmRelOK_of (hL : lettersK = true) (hR : relsK cmRelCodes = true) : cmRelOK = true := by
  unfold relsK at hR
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hR
  unfold cmRelOK
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨hlt, hid⟩ := hR w hw
  refine beq_of_ap (wordTab_size _ _ _) (idTab_size 480) fun x hx => ?_
  rw [(wordTab_ap hL w hlt hx).1, ← fd_wordK w x hx, hid, fd_idK hx, ap_idTab hx]

theorem levelOK_of (hL : lettersK = true) {prev : List Nat} (hp : ∀ b ∈ prev, b < 480)
    {L : ChainLevel} (h : levelK prev L = true) : levelOK cmLetters prev L = true ∧ L.base < 480 := by
  unfold levelK at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Nat.blt_eq] at h
  obtain ⟨⟨hb, hw⟩, hn⟩ := h
  refine ⟨?_, hb⟩
  unfold levelOK
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun qw hq => ?_, decide_eq_true (CFSG.Decide.nodup_of_bitsetNodup_nat hn)⟩
  obtain ⟨⟨hlt, hfix⟩, htgt⟩ := hw qw hq
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨fun b hb' => ?_, ?_⟩, fun c hc => hlt c hc⟩
  · rw [(wordTab_ap hL qw.2 hlt (hp b hb')).1]
    exact hfix b hb'
  · rw [(wordTab_ap hL qw.2 hlt hb).1]
    exact htgt

theorem chainOK_of' (hL : lettersK = true) : ∀ (c : List ChainLevel) (prev : List Nat),
    (∀ b ∈ prev, b < 480) → chainK prev c = true → chainOK cmLetters prev c = true
  | [], _, _, _ => rfl
  | L :: rest, prev, hp, h => by
    simp only [chainK, Bool.and_eq_true] at h
    obtain ⟨hl, hb⟩ := levelOK_of hL hp h.1
    have hp' : ∀ b ∈ prev ++ [L.base], b < 480 := by
      intro b hb'
      rcases List.mem_append.1 hb' with hb' | hb'
      · exact hp b hb'
      · rw [List.mem_singleton.1 hb']
        exact hb
    simp only [chainOK, hl, chainOK_of' hL rest _ hp' h.2, Bool.and_self]

theorem chainOK_of (hL : lettersK = true) {c : List ChainLevel} (h : chainK [] c = true) :
    chainOK cmLetters [] c = true :=
  chainOK_of' hL c [] (fun _ hb => absurd hb List.not_mem_nil) h

end CFSG.OddStandard.ONanRec.CMK
