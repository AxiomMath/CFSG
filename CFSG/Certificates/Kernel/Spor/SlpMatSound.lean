module

public import Certificates.Data.Kernel.Spor.SlpPlan
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CFSG.KC.SlpM

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KS.Mat3

@[expose] def decC (c : Nat) : Int := if c % 2 = 1 then -((c / 2 : Nat) : Int) else ((c / 2 : Nat) : Int)

@[expose] def decW (cs : List Nat) : List Int := cs.map decC

variable {M : Type*} [Monoid M]

@[expose] def semLetter (g : Int → M) (L : Array M) (z : Int) : M :=
  if z.natAbs ≤ 2 then g z
  else if 0 < z then L.getD (2 * (z.natAbs - 3)) 1 else L.getD (2 * (z.natAbs - 3) + 1) 1

@[expose] def semWord (g : Int → M) (L : Array M) (w : List Int) : M := (w.map (semLetter g L)).prod

@[expose] def semWordInv (g : Int → M) (L : Array M) (w : List Int) : M :=
  (w.reverse.map fun z => semLetter g L (-z)).prod

@[expose] def semStep (g : Int → M) (L : Array M) (w : List Int) : Array M :=
  (L.push (semWord g L w)).push (semWordInv g L w)

@[expose] def semArr (g : Int → M) (Ws : Array (List Int)) : Array M := Ws.foldl (semStep g) #[]

@[expose] def gen3 (gA gB : M) (z : Int) : M := if z = 1 ∨ z = -1 then gA else if z = 2 then gB else gB ^ 2

@[expose] def semN (g : Int → M) (W : List (List Nat)) (n : Nat) : M :=
  (semArr g (W.map decW).toArray).getD n 1

@[expose] def semE (g : Int → M) (W : List (List Nat)) (u : List Nat) : M :=
  semWord g (semArr g (W.map decW).toArray) (decW u)

theorem semStep_size (g : Int → M) (L : Array M) (w : List Int) : (semStep g L w).size = L.size + 2 := by
  simp [semStep]

theorem semStep_getElem? (g : Int → M) (L : Array M) (w : List Int) {k : Nat} (hk : k < L.size) :
    (semStep g L w)[k]? = L[k]? := by
  unfold semStep
  rw [Array.getElem?_push, if_neg (by simp; omega), Array.getElem?_push, if_neg (by omega)]

theorem foldl_semStep_getD (g : Int → M) (Es : List (List Int)) :
    ∀ (L : Array M) (k : Nat), k < L.size → (Es.foldl (semStep g) L).getD k 1 = L.getD k 1 := by
  induction Es with
  | nil => intro L k _; rfl
  | cons w Es ih =>
    intro L k hk
    rw [List.foldl_cons, ih _ k (by rw [semStep_size]; omega)]
    simp only [Array.getD_eq_getD_getElem?]
    rw [semStep_getElem? g L w hk]

theorem foldl_semStep_size (g : Int → M) (Es : List (List Int)) :
    ∀ L : Array M, (Es.foldl (semStep g) L).size = L.size + 2 * Es.length := by
  induction Es with
  | nil => intro L; simp
  | cons w Es ih =>
    intro L
    rw [List.foldl_cons, ih, semStep_size, List.length_cons]
    omega

theorem semArr_size (g : Int → M) (Ws : Array (List Int)) : (semArr g Ws).size = 2 * Ws.size := by
  unfold semArr
  rw [← Array.foldl_toList, foldl_semStep_size]
  simp

theorem semArr_append_getD (g : Int → M) (Ws Es : Array (List Int)) {k : Nat} (hk : k < 2 * Ws.size) :
    (semArr g (Ws ++ Es)).getD k 1 = (semArr g Ws).getD k 1 := by
  have hs := semArr_size g Ws
  unfold semArr at hs ⊢
  rw [Array.foldl_append, ← Array.foldl_toList (xs := Es)]
  exact foldl_semStep_getD g Es.toList _ k (by omega)

section ChunkLemmas

theorem chk_natRec (k : List (Nat × Nat) → Bool) (n x : Nat) (E : List (Nat × Nat)) :
    Nat.rec (motive := fun _ => Bool) (k (List.cons (Prod.mk n (nat_lit 0)) E))
      (fun v _ => k (List.cons (Prod.mk n (Nat.succ v)) E)) x = k ((n, x) :: E) := by
  cases x <;> rfl

theorem chk_orB {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all [orB]

theorem chk_notB {a : Bool} (h : notB a = true) : a = false := by
  cases a <;> simp_all [notB]

theorem chk_nIf (b : Bool) (x y : Nat) :
    Bool.rec (motive := fun _ => Nat) y x b = if b = true then x else y := by
  cases b <;> rfl

theorem chk_shr (c : Nat) : Nat.shiftRight c 1 = c / 2 := by
  change c >>> 1 = _
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem chk_beq_false {x y : Nat} (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem chk_land (c : Nat) : Nat.land c 1 = c % 2 := by
  change c &&& 1 = _
  rw [Nat.and_one_is_mod]

theorem chk_look_mem : ∀ {E : List (Nat × Nat)} {n : Nat}, has E n = true → (n, look E n) ∈ E
  | [], _, h => by simp [has] at h
  | p :: E, n, h => by
    change orB (Nat.beq p.1 n) (has E n) = true at h
    change (n, Bool.rec (motive := fun _ => Nat) (look E n) p.2 (Nat.beq p.1 n)) ∈ p :: E
    by_cases hp : p.1 = n
    · have hb : Nat.beq p.1 n = true := by rw [hp]; exact Nat.beq_refl n
      rw [hb]
      have : p = (n, p.2) := Prod.ext hp rfl
      rw [← this]
      exact List.mem_cons_self
    · have hb : Nat.beq p.1 n = false := chk_beq_false hp
      rw [hb] at h ⊢
      rcases chk_orB h with h1 | h1
      · exact absurd h1 (by simp)
      · exact List.mem_cons_of_mem _ (chk_look_mem h1)

theorem chk_lettersOK : ∀ {E : List (Nat × Nat)} {bnd : Bool} {j : Nat} {inv : Bool}
    {cs : List Nat}, lettersOK E bnd j inv cs = true → ∀ c ∈ cs, letOK E bnd j inv c = true
  | _, _, _, _, [], _, c, hc => by simp at hc
  | E, bnd, j, inv, c' :: cs, h, c, hc => by
    obtain ⟨h1, h2⟩ := CFSG.KS.Mat3.andB_true3 h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h1
    · exact chk_lettersOK h2 c hc

theorem chk_revApp : ∀ (L acc : List Nat), revApp L acc = L.reverse ++ acc
  | [], acc => rfl
  | c :: L, acc => by
    change revApp L (c :: acc) = _
    rw [chk_revApp L (c :: acc)]
    simp

theorem chk_nthW : ∀ (W : List (List Nat)) (j : Nat), nthW W j = W.getD j []
  | [], j => rfl
  | w :: W, 0 => rfl
  | w :: W, j + 1 => by
    change nthW W j = _
    rw [chk_nthW W j]
    rfl

variable {M : Type*} [Monoid M]

theorem chk_semArr_toArray (g : Int → M) (l : List (List Int)) :
    semArr g l.toArray = l.foldl (semStep g) #[] := by
  unfold semArr
  rw [← Array.foldl_toList]

theorem chk_foldl_size (g : Int → M) (l : List (List Int)) :
    (l.foldl (semStep g) #[]).size = 2 * l.length := by
  rw [foldl_semStep_size]
  simp

theorem chk_semStep_getD (g : Int → M) (L : Array M) (w : List Int) :
    (semStep g L w).getD L.size 1 = semWord g L w ∧
      (semStep g L w).getD (L.size + 1) 1 = semWordInv g L w := by
  unfold semStep
  constructor
  · simp [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  · have hs : L.size + 1 = (L.push (semWord g L w)).size := by simp
    rw [Array.getD_eq_getD_getElem?, hs, Array.getElem?_push_size]
    rfl

theorem chk_fold_entries (g : Int → M) (l : List (List Int)) {j : Nat} (hj : j < l.length) :
    (l.foldl (semStep g) #[]).getD (2 * j) 1 =
        semWord g ((l.take j).foldl (semStep g) #[]) l[j] ∧
      (l.foldl (semStep g) #[]).getD (2 * j + 1) 1 =
        semWordInv g ((l.take j).foldl (semStep g) #[]) l[j] := by
  have hl : l.take j ++ l[j] :: l.drop (j + 1) = l := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hLs : ((l.take j).foldl (semStep g) #[]).size = 2 * j := by
    rw [chk_foldl_size, List.length_take, min_eq_left hj.le]
  have key : ∀ k, k < 2 * j + 2 → (l.foldl (semStep g) #[]).getD k 1 =
      (semStep g ((l.take j).foldl (semStep g) #[]) l[j]).getD k 1 := by
    intro k hk
    conv_lhs => rw [← hl]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_semStep_getD g _ _ k (by rw [semStep_size, hLs]; omega)
  have hS := chk_semStep_getD g ((l.take j).foldl (semStep g) #[]) l[j]
  rw [hLs] at hS
  exact ⟨(key _ (by omega)).trans hS.1, (key _ (by omega)).trans hS.2⟩

theorem chk_fold_prefix (g : Int → M) (l : List (List Int)) {j k : Nat} (hj : j ≤ l.length)
    (hk : k < 2 * j) :
    (l.foldl (semStep g) #[]).getD k 1 = ((l.take j).foldl (semStep g) #[]).getD k 1 := by
  conv_lhs => rw [← List.take_append_drop j l]
  rw [List.foldl_append]
  exact foldl_semStep_getD g _ _ k (by rw [chk_foldl_size, List.length_take, min_eq_left hj]; omega)

theorem chk_fold_oob (g : Int → M) (l : List (List Int)) {k : Nat} (hk : 2 * l.length ≤ k) :
    (l.foldl (semStep g) #[]).getD k 1 = 1 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [chk_foldl_size]; omega)]
  rfl

end ChunkLemmas

section ChunkSound

open CFSG.KS.Mat3

variable {d f N LO RM CI ONE UP : Nat} {GA GB GB2 : Nat} {gA gB : Matrix (Fin d) (Fin d) (ZMod 3)}

theorem chk_letter (inv : Bool) (c : Nat) :
    (if inv = true then -decC c else decC c) =
      if negC inv c = true then -((c / 2 : Nat) : Int) else ((c / 2 : Nat) : Int) := by
  have h2 : c % 2 = 0 ∨ c % 2 = 1 := Nat.mod_two_eq_zero_or_one c
  cases inv <;> unfold negC decC <;> rw [chk_land] <;>
    rcases h2 with h2 | h2 <;> simp [h2]

theorem chk_prodV (hc : consts3OK d f N LO RM CI ONE UP = true) (fv : Nat → Nat)
    (φ : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) :
    ∀ cs : List Nat, (∀ c ∈ cs, Canon3 N (fv c) ∧ mat3 d N (fv c) = φ c) →
      Canon3 N (prodV (mul3s d N LO CI RM) ONE fv cs) ∧
        mat3 d N (prodV (mul3s d N LO CI RM) ONE fv cs) = (cs.map φ).prod
  | [], _ => by
    obtain ⟨h1, h2⟩ := one3_sound hc
    exact ⟨h1, by rw [List.map_nil, List.prod_nil]; exact h2⟩
  | [c], h => by
    obtain ⟨h1, h2⟩ := h c (List.mem_singleton_self c)
    refine ⟨h1, ?_⟩
    change mat3 d N (fv c) = _
    rw [h2, List.map_singleton, List.prod_singleton]
  | c :: c' :: cs, h => by
    have ih := chk_prodV hc fv φ (c' :: cs) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨h1, h2⟩ := h c List.mem_cons_self
    change Canon3 N (mul3s d N LO CI RM (fv c) (prodV (mul3s d N LO CI RM) ONE fv (c' :: cs))) ∧
      mat3 d N (mul3s d N LO CI RM (fv c) (prodV (mul3s d N LO CI RM) ONE fv (c' :: cs))) = _
    obtain ⟨h3, h4⟩ := mul3s_sound hc h1 ih.1
    refine ⟨h3, ?_⟩
    rw [h4, h2, ih.2]
    simp only [List.map_cons, List.prod_cons]

theorem chk_letV (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB)
    {W : List (List Nat)} {E : List (Nat × Nat)}
    (hE : ∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1)
    {L : Array (Matrix (Fin d) (Fin d) (ZMod 3))} {bnd : Bool} {j : Nat} {inv : Bool} {c : Nat}
    (hok : letOK E bnd j inv c = true)
    (hL : ∀ k, (bnd = true → k < 2 * j) → L.getD k 1 = semN (gen3 gA gB) W k) :
    Canon3 N (letV GA GB GB2 E inv c) ∧
      mat3 d N (letV GA GB GB2 E inv c) =
        semLetter (gen3 gA gB) L (if inv = true then -decC c else decC c) := by
  rw [chk_letter]
  have hnode : nodeC inv c = 2 * (c / 2 - 3) + (if negC inv c = true then 1 else 0) := by
    unfold nodeC
    rw [chk_shr, chk_nIf]
    rfl
  unfold letV
  unfold letOK at hok
  simp only [chk_shr, chk_nIf, hnode] at hok ⊢
  generalize c / 2 = a at hok ⊢
  generalize negC inv c = b at hok ⊢
  by_cases h0 : a = 0
  · subst h0
    have e : Nat.beq 0 0 = true := rfl
    simp only [e, if_true]
    refine ⟨hB2.1, ?_⟩
    rw [hB2.2]
    cases b <;> simp [semLetter, gen3, pow_two]
  have hb0 : Nat.beq a 0 = false := chk_beq_false h0
  simp only [hb0, Bool.false_eq_true, if_false]
  by_cases h1 : a = 1
  · subst h1
    have e : Nat.beq 1 1 = true := rfl
    simp only [e, if_true]
    refine ⟨hA.1, ?_⟩
    rw [hA.2]
    cases b <;> simp [semLetter, gen3]
  have hb1 : Nat.beq a 1 = false := chk_beq_false h1
  simp only [hb1, Bool.false_eq_true, if_false]
  by_cases h2 : a = 2
  · subst h2
    have e : Nat.beq 2 2 = true := rfl
    simp only [e, if_true]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      refine ⟨hB.1, ?_⟩
      rw [hB.2]
      simp [semLetter, gen3]
    · simp only [if_true]
      refine ⟨hB2.1, ?_⟩
      rw [hB2.2]
      simp [semLetter, gen3, pow_two]
  have hb2 : Nat.beq a 2 = false := chk_beq_false h2
  simp only [hb2, Bool.false_eq_true, if_false]
  have ha3 : 3 ≤ a := by omega
  have hlt : Nat.blt a 3 = false := by
    cases h : Nat.blt a 3
    · rfl
    · exact absurd (Eq.mp Nat.blt_eq h) (by omega)
  rw [hlt] at hok
  obtain ⟨hbd, hhas⟩ := CFSG.KS.Mat3.andB_true3 hok
  have hmem := hE _ (chk_look_mem hhas)
  refine ⟨hmem.1, ?_⟩
  rw [hmem.2]
  have hk : bnd = true → 2 * (a - 3) + (if b = true then 1 else 0) < 2 * j := by
    intro hbnd
    rcases chk_orB hbd with h | h
    · rw [hbnd] at h
      exact absurd (chk_notB h) (by simp)
    · have := Eq.mp Nat.blt_eq h
      simp only [Nat.sub_eq] at this
      split_ifs <;> omega
  rw [← hL _ hk]
  unfold semLetter
  cases b
  · simp only [Bool.false_eq_true, if_false, Nat.add_zero, Int.natAbs_natCast]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [if_true, Int.natAbs_neg, Int.natAbs_natCast]
    rw [if_neg (by omega), if_neg (by omega)]

theorem chk_word (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB)
    {W : List (List Nat)} {E : List (Nat × Nat)}
    (hE : ∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1)
    {L : Array (Matrix (Fin d) (Fin d) (ZMod 3))} {bnd : Bool} {j : Nat} {inv : Bool}
    {cs : List Nat} (hok : lettersOK E bnd j inv cs = true)
    (hL : ∀ k, (bnd = true → k < 2 * j) → L.getD k 1 = semN (gen3 gA gB) W k) :
    Canon3 N (prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E inv) cs) ∧
      mat3 d N (prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E inv) cs) =
        (cs.map fun c => semLetter (gen3 gA gB) L (if inv = true then -decC c else decC c)).prod :=
  chk_prodV hc _ _ cs fun c hcs =>
    chk_letV hc hA hB hB2 hE (chk_lettersOK hok c hcs) hL

theorem chk_node (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB)
    {W : List (List Nat)} {E : List (Nat × Nat)}
    (hE : ∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1)
    {n : Nat} (hok : nodeOK W E n = true) :
    Canon3 N (nodeV (mul3s d N LO CI RM) ONE GA GB GB2 W E n) ∧
      mat3 d N (nodeV (mul3s d N LO CI RM) ONE GA GB GB2 W E n) = semN (gen3 gA gB) W n := by
  set l : List (List Int) := W.map decW with hl
  have hsem : ∀ k, semN (gen3 gA gB) W k = (l.foldl (semStep (gen3 gA gB)) #[]).getD k 1 := by
    intro k
    unfold semN
    rw [chk_semArr_toArray]
  set j := n / 2 with hj
  have hn : n = 2 * j + n % 2 := by omega
  unfold nodeV nodeLetters
  unfold nodeOK nodeLetters at hok
  rw [chk_shr, chk_nthW] at hok ⊢
  rw [← hj] at hok ⊢
  have hone := one3_sound hc
  have hlen : l.length = W.length := by rw [hl, List.length_map]
  have hpre : j ≤ W.length → ∀ k, (true = true → k < 2 * j) →
      ((l.take j).foldl (semStep (gen3 gA gB)) #[]).getD k 1 = semN (gen3 gA gB) W k := by
    intro hjW k hk
    rw [hsem, chk_fold_prefix (gen3 gA gB) l (by omega) (hk rfl)]
  have hW0 : ¬ j < W.length → W.getD j [] = [] := by
    intro hjl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have hw : ∀ hjl : j < l.length, l[j] = decW (W.getD j []) := by
    intro hjl
    simp [hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hjl)]
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h0
  · have hb : Nat.beq (Nat.land n 1) 1 = false := by rw [chk_land, h0]; rfl
    have ho : oddN n = false := hb
    simp only [hb, ho] at hok ⊢
    by_cases hjl : j < W.length
    · have hjl' : j < l.length := by omega
      obtain ⟨h1, h2⟩ := chk_word hc hA hB hB2 hE hok (hpre hjl.le)
      refine ⟨h1, ?_⟩
      rw [h2, hsem, hn, h0, Nat.add_zero, (chk_fold_entries (gen3 gA gB) l hjl').1, hw hjl']
      simp [semWord, decW, List.map_map, Function.comp_def]
    · rw [hW0 hjl]
      refine ⟨hone.1, ?_⟩
      rw [show prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E false) [] = ONE from rfl,
        hone.2, hsem, chk_fold_oob]
      omega
  · have hb : Nat.beq (Nat.land n 1) 1 = true := by rw [chk_land, h0]; rfl
    have ho : oddN n = true := hb
    simp only [hb, ho] at hok ⊢
    by_cases hjl : j < W.length
    · have hjl' : j < l.length := by omega
      obtain ⟨h1, h2⟩ := chk_word hc hA hB hB2 hE hok (hpre hjl.le)
      refine ⟨h1, ?_⟩
      rw [h2, hsem, hn, h0, (chk_fold_entries (gen3 gA gB) l hjl').2, hw hjl', chk_revApp,
        List.append_nil]
      simp [semWordInv, decW, List.map_map, List.map_reverse, Function.comp_def]
    · rw [hW0 hjl]
      refine ⟨hone.1, ?_⟩
      rw [show prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E true) (revApp [] []) = ONE from rfl,
        hone.2, hsem, chk_fold_oob]
      omega

theorem chk_runNodes (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB)
    {W : List (List Nat)} {fin : List (Nat × Nat) → Bool} :
    ∀ (nodes : List Nat) (E : List (Nat × Nat)),
      (∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1) →
      runNodes (mul3s d N LO CI RM) ONE GA GB GB2 W fin nodes E = true →
      ∃ E' : List (Nat × Nat),
        (∀ q ∈ E', Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1) ∧ fin E' = true
  | [], E, hE, h => ⟨E, hE, h⟩
  | n :: ns, E, hE, h => by
    change andB (nodeOK W E n) (Nat.rec (motive := fun _ => Bool)
      (runNodes (mul3s d N LO CI RM) ONE GA GB GB2 W fin ns ((n, 0) :: E))
      (fun v _ => runNodes (mul3s d N LO CI RM) ONE GA GB GB2 W fin ns ((n, Nat.succ v) :: E))
      (nodeV (mul3s d N LO CI RM) ONE GA GB GB2 W E n)) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KS.Mat3.andB_true3 h
    have key : ∀ x : Nat, Nat.rec (motive := fun _ => Bool)
        (runNodes (mul3s d N LO CI RM) ONE GA GB GB2 W fin ns ((n, 0) :: E))
        (fun v _ => runNodes (mul3s d N LO CI RM) ONE GA GB GB2 W fin ns ((n, Nat.succ v) :: E)) x =
        runNodes (mul3s d N LO CI RM) ONE GA GB GB2 W fin ns ((n, x) :: E) := by
      intro x
      cases x <;> rfl
    rw [key] at h2
    have hn := chk_node hc hA hB hB2 hE h1
    refine chk_runNodes hc hA hB hB2 ns _ ?_ h2
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hn
    · exact hE q hq

theorem chk_runIns (hLO : LO = 2 ^ N - 1) {W : List (List Nat)} {R : Nat → Nat}
    {k : List (Nat × Nat) → Bool} {ins : List (Nat × Nat)}
    (hin : ∀ p ∈ ins, mat3 d N (R p.2) = semN (gen3 gA gB) W p.1) :
    ∀ (ins' : List (Nat × Nat)), (∀ p ∈ ins', p ∈ ins) → ∀ E : List (Nat × Nat),
      (∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1) →
      runIns (valid3 N LO) R k ins' E = true →
      ∃ E' : List (Nat × Nat),
        (∀ q ∈ E', Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1) ∧ k E' = true
  | [], _, E, hE, h => ⟨E, hE, h⟩
  | p :: ps, hps, E, hE, h => by
    change andB (valid3 N LO (R p.2)) (Nat.rec (motive := fun _ => Bool)
      (runIns (valid3 N LO) R k ps ((p.1, 0) :: E))
      (fun v _ => runIns (valid3 N LO) R k ps ((p.1, Nat.succ v) :: E)) (R p.2)) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KS.Mat3.andB_true3 h
    have key : ∀ x : Nat, Nat.rec (motive := fun _ => Bool)
        (runIns (valid3 N LO) R k ps ((p.1, 0) :: E))
        (fun v _ => runIns (valid3 N LO) R k ps ((p.1, Nat.succ v) :: E)) x =
        runIns (valid3 N LO) R k ps ((p.1, x) :: E) := by
      intro x
      cases x <;> rfl
    rw [key] at h2
    have hcan : Canon3 N (R p.2) := (valid3_iff hLO).1 h1
    refine chk_runIns hLO hin ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _ ?_ h2
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨hcan, hin p (hps p List.mem_cons_self)⟩
    · exact hE q hq

theorem chk_outs {W : List (List Nat)} {R : Nat → Nat} {E : List (Nat × Nat)}
    (hE : ∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1) :
    ∀ {outs : List (Nat × Nat)}, outsOK R E outs = true →
      ∀ p ∈ outs, Canon3 N (R p.2) ∧ mat3 d N (R p.2) = semN (gen3 gA gB) W p.1
  | [], _, p, hp => by simp at hp
  | o :: os, h, p, hp => by
    change andB (andB (has E o.1) (Nat.beq (look E o.1) (R o.2))) (outsOK R E os) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KS.Mat3.andB_true3 h
    obtain ⟨h3, h4⟩ := CFSG.KS.Mat3.andB_true3 h1
    rcases List.mem_cons.1 hp with rfl | hp
    · have hm := hE _ (chk_look_mem h3)
      rw [Nat.eq_of_beq_eq_true h4] at hm
      exact hm
    · exact chk_outs hE h2 p hp

theorem chk_semE (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB)
    {W : List (List Nat)} {E : List (Nat × Nat)}
    (hE : ∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1)
    {u : List Nat} (hok : lettersOK E false 0 false u = true) :
    Canon3 N (prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E false) u) ∧
      mat3 d N (prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E false) u) =
        semE (gen3 gA gB) W u := by
  obtain ⟨h1, h2⟩ := chk_word hc hA hB hB2 hE hok
    (L := semArr (gen3 gA gB) (W.map decW).toArray) (fun k _ => rfl)
  refine ⟨h1, ?_⟩
  rw [h2]
  simp [semE, semWord, decW, List.map_map, Function.comp_def]

theorem chk_eqs (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB)
    {W : List (List Nat)} {E : List (Nat × Nat)}
    (hE : ∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1) :
    ∀ {eqs : List (List Nat × List Nat)}, eqsOK (mul3s d N LO CI RM) ONE GA GB GB2 E eqs = true →
      ∀ e ∈ eqs, semE (gen3 gA gB) W e.1 = semE (gen3 gA gB) W e.2
  | [], _, e, he => by simp at he
  | e' :: es, h, e, he => by
    change andB (andB (andB (lettersOK E false 0 false e'.1) (lettersOK E false 0 false e'.2))
      (Nat.beq (prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E false) e'.1)
        (prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E false) e'.2)))
      (eqsOK (mul3s d N LO CI RM) ONE GA GB GB2 E es) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KS.Mat3.andB_true3 h
    obtain ⟨h3, h4⟩ := CFSG.KS.Mat3.andB_true3 h1
    obtain ⟨h5, h6⟩ := CFSG.KS.Mat3.andB_true3 h3
    rcases List.mem_cons.1 he with rfl | he
    · rw [← (chk_semE hc hA hB hB2 hE h5).2, ← (chk_semE hc hA hB hB2 hE h6).2,
        Nat.eq_of_beq_eq_true h4]
    · exact chk_eqs hc hA hB hB2 hE h2 e he

theorem chk_neqs (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB) (hN : N = d * d)
    {W : List (List Nat)} {E : List (Nat × Nat)}
    (hE : ∀ q ∈ E, Canon3 N q.2 ∧ mat3 d N q.2 = semN (gen3 gA gB) W q.1) :
    ∀ {neqs : List (List Nat × List Nat)},
      neqsOK (mul3s d N LO CI RM) ONE GA GB GB2 E neqs = true →
      ∀ e ∈ neqs, semE (gen3 gA gB) W e.1 ≠ semE (gen3 gA gB) W e.2
  | [], _, e, he => by simp at he
  | e' :: es, h, e, he => by
    change andB (andB (andB (lettersOK E false 0 false e'.1) (lettersOK E false 0 false e'.2))
      (notB (Nat.beq (prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E false) e'.1)
        (prodV (mul3s d N LO CI RM) ONE (letV GA GB GB2 E false) e'.2))))
      (neqsOK (mul3s d N LO CI RM) ONE GA GB GB2 E es) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KS.Mat3.andB_true3 h
    obtain ⟨h3, h4⟩ := CFSG.KS.Mat3.andB_true3 h1
    obtain ⟨h5, h6⟩ := CFSG.KS.Mat3.andB_true3 h3
    rcases List.mem_cons.1 he with rfl | he
    · intro heq
      have w1 := chk_semE hc hA hB hB2 hE h5
      have w2 := chk_semE hc hA hB hB2 hE h6
      have hx := mat3_inj hN w1.1 w2.1 (by rw [w1.2, w2.2]; exact heq)
      have hb := chk_notB h4
      rw [hx] at hb
      exact absurd (Nat.beq_refl _) (by rw [hb]; simp)
    · exact chk_neqs hc hA hB hB2 hN hE h2 e he

end ChunkSound

theorem chunkOK_spec {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true)
    {GA GB GB2 : Nat} {gA gB : Matrix (Fin d) (Fin d) (ZMod 3)}
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB)
    {W : List (List Nat)} {R : Nat → Nat} {ins : List (Nat × Nat)} {nodes : List Nat}
    {outs : List (Nat × Nat)} {eqs neqs : List (List Nat × List Nat)}
    (h : chunkOK (mul3s d N LO CI RM) ONE (valid3 N LO) GA GB GB2 W R ins nodes outs eqs neqs = true)
    (hin : ∀ p ∈ ins, mat3 d N (R p.2) = semN (gen3 gA gB) W p.1) :
    (∀ p ∈ outs, Canon3 N (R p.2) ∧ mat3 d N (R p.2) = semN (gen3 gA gB) W p.1) ∧
      (∀ e ∈ eqs, semE (gen3 gA gB) W e.1 = semE (gen3 gA gB) W e.2) ∧
      ∀ e ∈ neqs, semE (gen3 gA gB) W e.1 ≠ semE (gen3 gA gB) W e.2 := by
  obtain ⟨-, hN, hLO, -, -, -⟩ := CFSG.KS.Mat3.consts3_facts hc
  unfold chunkOK at h
  obtain ⟨E1, hE1, h1⟩ := chk_runIns hLO hin ins (fun p hp => hp) [] (by simp) h
  obtain ⟨E2, hE2, h2⟩ := chk_runNodes hc hA hB hB2 nodes E1 hE1 h1
  obtain ⟨ho, h3⟩ := CFSG.KS.Mat3.andB_true3 h2
  obtain ⟨he, hne⟩ := CFSG.KS.Mat3.andB_true3 h3
  exact ⟨chk_outs hE2 ho, chk_eqs hc hA hB hB2 hE2 he, chk_neqs hc hA hB hB2 hN hE2 hne⟩

theorem andB_iff (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_iff (a b : Bool) : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem allLt_spec {n : Nat} {f : Nat → Bool} (h : allLt n f = true) : ∀ k < n, f k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    have h' := (andB_iff _ _).1 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h'.1 k hk
    · exact h'.2

theorem allL_spec {α : Type} {l : List α} {f : α → Bool} (h : allL l f = true) : ∀ a ∈ l, f a = true := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons b l ih =>
    intro a ha
    have h' := (andB_iff _ _).1 h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h'.1
    · exact ih h'.2 a ha

theorem memP_spec {q : Nat × Nat} {l : List (Nat × Nat)} (h : memP q l = true) : q ∈ l := by
  induction l with
  | nil => simp [memP] at h
  | cons p l ih =>
    rcases (orB_iff _ _).1 h with h1 | h1
    · obtain ⟨e1, e2⟩ := (andB_iff _ _).1 h1
      have : p = q := Prod.ext (Nat.eq_of_beq_eq_true e1) (Nat.eq_of_beq_eq_true e2)
      exact this ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h1)

theorem planOK_spec {K nR base : Nat} {LY PC PN : Nat → Nat} {IN OU : Nat → List (Nat × Nat)}
    (h : planOK K nR base LY PC PN IN OU = true) :
    (∀ k < K, ∀ p ∈ IN k, 0 < p.2 ∧ p.2 < nR ∧ PN p.2 = p.1 ∧ PC p.2 < k ∧
      (LY (PC p.2) = LY k ∨ p.1 < base)) ∧
    ∀ r < nR, 0 < r → PC r < K ∧ (PN r, r) ∈ OU (PC r) := by
  obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h
  refine ⟨fun k hk p hp => ?_, fun r hr hr0 => ?_⟩
  · have := allL_spec (allLt_spec h1 k hk) p hp
    obtain ⟨⟨a1, a2⟩, a3, a4, a5⟩ := by simpa only [andB_iff] using this
    refine ⟨blt_true a1, blt_true a2, Nat.eq_of_beq_eq_true a3, blt_true a4, ?_⟩
    rcases (orB_iff _ _).1 a5 with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    · exact Or.inr (blt_true e)
  · have := allLt_spec h2 r hr
    rcases (orB_iff _ _).1 this with h0 | h0
    · exact absurd (Nat.eq_of_beq_eq_true h0) (by omega)
    · obtain ⟨e1, e2⟩ := (andB_iff _ _).1 h0
      exact ⟨blt_true e1, memP_spec e2⟩

theorem lenL_eq {α : Type} (l : List α) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => change Nat.succ (lenL l) = _; rw [ih]; rfl

theorem appL_eq (a b : List (List Nat)) : appL a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons w a ih => change w :: appL a b = _; rw [ih]; rfl

theorem nthL_eq {α : Type} (d : α) (l : List α) (j : Nat) : nthL d l j = l.getD j d := by
  induction l generalizing j with
  | nil => rfl
  | cons a l ih =>
    cases j with
    | zero => rfl
    | succ j => change nthL d l j = _; rw [ih]; rfl

theorem eqLN_spec : ∀ {a b : List Nat}, eqLN a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqLN] at h
  | _ :: _, [], h => by simp [eqLN] at h
  | x :: a, y :: b, h => by
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h
    rw [Nat.eq_of_beq_eq_true h1, eqLN_spec h2]

theorem memE_spec {e : List Nat × List Nat} : ∀ {l : List (List Nat × List Nat)}, memE e l = true → e ∈ l
  | [], h => by simp [memE] at h
  | p :: l, h => by
    rcases (orB_iff _ _).1 h with h1 | h1
    · obtain ⟨e1, e2⟩ := (andB_iff _ _).1 h1
      have : p = e := Prod.ext (eqLN_spec e1) (eqLN_spec e2)
      exact this ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memE_spec h1)

theorem anyLt_spec {f : Nat → Bool} : ∀ {n : Nat}, anyLt n f = true → ∃ k < n, f k = true
  | 0, h => by simp [anyLt] at h
  | n + 1, h => by
    rcases (orB_iff _ _).1 h with h1 | h1
    · obtain ⟨k, hk, e⟩ := anyLt_spec h1
      exact ⟨k, by omega, e⟩
    · exact ⟨n, by omega, h1⟩

theorem hasEq_spec {LY : Nat → Nat} {EQ : Nat → List (List Nat × List Nat)} {K l : Nat}
    {e : List Nat × List Nat} (h : hasEq LY EQ K l e = true) : ∃ k < K, LY k = l ∧ e ∈ EQ k := by
  obtain ⟨k, hk, h1⟩ := anyLt_spec h
  obtain ⟨e1, e2⟩ := (andB_iff _ _).1 h1
  exact ⟨k, hk, Nat.eq_of_beq_eq_true e1, memE_spec e2⟩

theorem decC_natAbs (c : Nat) : (decC c).natAbs = c / 2 := by
  unfold decC
  split_ifs
  · rw [Int.natAbs_neg, Int.natAbs_natCast]
  · rw [Int.natAbs_natCast]

theorem slpC_spec : ∀ {W : List (List Nat)} {j0 : Nat}, slpC W j0 = true →
    ∀ i < W.length, ∀ c ∈ W[i]!, 0 < c / 2 ∧ (c / 2 ≤ 2 ∨ c / 2 < j0 + i + 3)
  | [], _, _, i, hi, _, _ => absurd hi (by simp)
  | w :: W, j0, h, i, hi, c, hc => by
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h
    cases i with
    | zero =>
      have := allL_spec h1 c (by simpa using hc)
      have hs : Nat.shiftRight c 1 = c / 2 := by change c >>> 1 = _; rw [Nat.shiftRight_eq_div_pow]
      dsimp only at this
      rw [hs] at this
      obtain ⟨a1, a2⟩ := (andB_iff _ _).1 this
      refine ⟨blt_true a1, ?_⟩
      rcases (orB_iff _ _).1 a2 with e | e
      · exact Or.inl (Nat.le_of_ble_eq_true e)
      · exact Or.inr (by have := blt_true e; change c / 2 < j0 + 3 at this; omega)
    | succ i =>
      have := slpC_spec h2 i (by simpa using hi) c (by simpa using hc)
      change 0 < c / 2 ∧ (c / 2 ≤ 2 ∨ c / 2 < Nat.succ j0 + i + 3) at this
      refine ⟨this.1, ?_⟩
      omega

theorem slp_records {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true)
    {GA GB GB2 : Nat} {gA gB : Matrix (Fin d) (Fin d) (ZMod 3)}
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB)
    {WL : Nat → List (List Nat)} {base : Nat}
    (hW : ∀ l l' n, n < base → semN (gen3 gA gB) (WL l) n = semN (gen3 gA gB) (WL l') n)
    {K nR : Nat} {R : Nat → Nat} {LY PC PN : Nat → Nat} {IN OU : Nat → List (Nat × Nat)}
    {ND : Nat → List Nat} {EQ NE : Nat → List (List Nat × List Nat)}
    (hk : ∀ k < K, chunkOK (mul3s d N LO CI RM) ONE (valid3 N LO) GA GB GB2 (WL (LY k)) R (IN k)
      (ND k) (OU k) (EQ k) (NE k) = true)
    (hp : planOK K nR base LY PC PN IN OU = true) :
    (∀ r < nR, 0 < r → Canon3 N (R r) ∧ mat3 d N (R r) = semN (gen3 gA gB) (WL (LY (PC r))) (PN r)) ∧
      ∀ k < K, (∀ e ∈ EQ k, semE (gen3 gA gB) (WL (LY k)) e.1 = semE (gen3 gA gB) (WL (LY k)) e.2) ∧
        ∀ e ∈ NE k, semE (gen3 gA gB) (WL (LY k)) e.1 ≠ semE (gen3 gA gB) (WL (LY k)) e.2 := by
  obtain ⟨pin, prec⟩ := planOK_spec hp
  have hout : ∀ k, k < K → ∀ p ∈ OU k,
      Canon3 N (R p.2) ∧ mat3 d N (R p.2) = semN (gen3 gA gB) (WL (LY k)) p.1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkK
      refine (chunkOK_spec hc hA hB hB2 (hk k hkK) fun p hp => ?_).1
      obtain ⟨h0, hr, hn, hlt, hly⟩ := pin k hkK p hp
      obtain ⟨hK, hm⟩ := prec p.2 hr h0
      have := (ih (PC p.2) hlt hK (PN p.2, p.2) hm).2
      rw [this, hn]
      rcases hly with e | e
      · rw [e]
      · exact hW _ _ _ e
  refine ⟨fun r hr hr0 => ?_, fun k hkK => ?_⟩
  · obtain ⟨hK, hm⟩ := prec r hr hr0
    exact hout (PC r) hK (PN r, r) hm
  · have := chunkOK_spec hc hA hB hB2 (hk k hkK) fun p hp => by
      obtain ⟨h0, hr, hn, hlt, hly⟩ := pin k hkK p hp
      obtain ⟨hK, hm⟩ := prec p.2 hr h0
      have := (hout (PC p.2) hK (PN p.2, p.2) hm).2
      rw [this, hn]
      rcases hly with e | e
      · rw [e]
      · exact hW _ _ _ e
    exact this.2

end CFSG.KC.SlpM

end
