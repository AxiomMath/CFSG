module

public import CFSG.Certificates.Kernel.Spor.PK.Words
public import CFSG.Certificates.Kernel.Spor.PK.NatChain

public section

namespace CFSG.KS.PK

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.TW CFSG.Sporadic.Mathieu.Native

@[expose] def gensT (n : Nat) (tA tB : Table) (z : Int) : Nat → Nat :=
  if z = 1 then ap tA else if z = -1 then finv n (ap tA) else if z = 2 then ap tB else finv n (ap tB)

theorem compT_TR {n : Nat} (hn : n < 2 ^ 32) {P Q : Table} {f g : Nat → Nat} (hP : TR n P f)
    (hQ : TR n Q g) : TR n (compT n P Q) fun x => f (g x) := by
  refine ⟨by simp [compT], fun i hi => ?_⟩
  obtain ⟨hq1, hq2⟩ := hQ.2 i hi
  obtain ⟨hp1, hp2⟩ := hP.2 _ hq2
  refine ⟨?_, hp2⟩
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have e : (Q[i]!).toNat = g i := hq1
  rw [e]
  exact hp1

theorem powT_TR {n : Nat} (hn : n < 2 ^ 32) {P : Table} {f : Nat → Nat} (hP : TR n P f) (e : Nat) :
    TR n (powT n e P) (itr f e) := by
  induction e with
  | zero => exact idT_TR hn
  | succ e ih => exact compT_TR (f := f) (g := itr f e) hn hP ih

theorem isIdT_iff {n : Nat} {T : Table} {f : Nat → Nat} (hT : TR n T f) :
    isIdT n T = true ↔ ∀ x < n, f x = x := by
  unfold isIdT
  rw [allIn_iff]
  constructor
  · intro h x hx
    have h1 := h x hx
    rw [(hT.2 x hx).1] at h1
    simpa using h1
  · intro h x hx
    rw [(hT.2 x hx).1, h x hx]
    simp

theorem invT_TR' {n : Nat} (hn : n < 2 ^ 32) {P : Table} {f : Nat → Nat} (hP : TR n P f)
    (hf : IsPermN n f) : TR n (invT n P) (finv n f) := by
  refine invT_TR hn hP fun i hi => ?_
  obtain ⟨h1, h2⟩ := finv_spec hf hi
  exact ⟨h1, h2, finv_apply hf hi⟩

private theorem isPermN_getD {n : Nat} {M : List (Nat → Nat)} (h : ∀ f ∈ M, IsPermN n f)
    (l : Nat) : IsPermN n (M.getD l id) := by
  by_cases hl : l < M.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    exact h _ (List.getElem_mem hl)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 hl)]
    exact isPermN_id n

private theorem letFnPerm {n : Nat} {G : Int → Nat → Nat}
    (hG : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (G z)) {M : List (Nat → Nat)}
    (hM : ∀ f ∈ M, IsPermN n f) {z : Int} (hz : z ≠ 0) : IsPermN n (letFn G M z) := by
  unfold letFn
  split
  · exact hG z hz ‹_›
  · split <;> exact isPermN_getD hM _

private theorem wordFnPerm {n : Nat} {G : Int → Nat → Nat}
    (hG : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (G z)) {M : List (Nat → Nat)}
    (hM : ∀ f ∈ M, IsPermN n f) {wd : List Int} (hwd : ∀ z ∈ wd, z ≠ 0) :
    IsPermN n (wordFn G M wd) := by
  induction wd with
  | nil => exact isPermN_id n
  | cons z wd ih =>
    exact (letFnPerm hG hM (hwd z List.mem_cons_self)).comp
      (ih fun y hy => hwd y (List.mem_cons_of_mem _ hy))

private theorem letTR {n : Nat} {gens : Int → Table} {G : Int → Nat → Nat}
    (hG : ∀ z, TR n (gens z) (G z)) {L : Array Table} {M : List (Nat → Nat)} {j : Nat}
    (hL : ∀ l < 2 * j, TR n L[l]! (M.getD l id)) {z : Int}
    (hz : z.natAbs ≤ 2 ∨ z.natAbs < j + 3) :
    TR n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L z) (letFn G M z) := by
  unfold CFSG.Sporadic.Fi23.Native.slpLetterT letFn
  by_cases h : z.natAbs ≤ 2
  · rw [if_pos h, if_pos h]
    exact hG z
  · rw [if_neg h, if_neg h]
    have h3 : z.natAbs < j + 3 := hz.resolve_left h
    by_cases hp : 0 < z
    · rw [if_pos hp, if_pos hp]
      exact hL _ (by omega)
    · rw [if_neg hp, if_neg hp]
      exact hL _ (by omega)

private def stepL (n : Nat) (gens : Int → Table) (L : Array Table) (w : List Int) : Array Table :=
  let T := wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L) w
  (L.push T).push (invT n T)

private theorem push_get!_lt {α : Type} [Inhabited α] (L : Array α) (a : α) {l : Nat}
    (hl : l < L.size) : (L.push a)[l]! = L[l]! := by
  rw [getElem!_pos _ l (by simp; omega), getElem!_pos _ l hl, Array.getElem_push_lt]

private theorem push_get!_eq {α : Type} [Inhabited α] (L : Array α) (a : α) :
    (L.push a)[L.size]! = a := by
  rw [getElem!_pos _ L.size (by simp), Array.getElem_push_eq]

private theorem getD_append_lt {α : Type} (M M' : List α) (d : α) {l : Nat} (h : l < M.length) :
    (M ++ M').getD l d = M.getD l d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_ge {α : Type} (M M' : List α) (d : α) {l : Nat} (h : M.length ≤ l) :
    (M ++ M').getD l d = M'.getD (l - M.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem slp_fold {n : Nat} (hn : n < 2 ^ 32) {gens : Int → Table} {G : Int → Nat → Nat}
    (hG : ∀ z, TR n (gens z) (G z)) (hGp : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (G z)) :
    ∀ (ws : List (List Int)) (j : Nat) (L : Array Table) (M : List (Nat → Nat)),
      L.size = 2 * j → M.length = 2 * j → (∀ l < 2 * j, TR n L[l]! (M.getD l id)) →
      (∀ f ∈ M, IsPermN n f) →
      (∀ i < ws.length, ∀ z ∈ ws.getD i [], z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + i + 3)) →
      (ws.foldl (stepL n gens) L).size = 2 * (j + ws.length) ∧
        ∀ l < 2 * (j + ws.length),
          TR n (ws.foldl (stepL n gens) L)[l]! ((lettersFrom n G M ws).getD l id) := by
  intro ws
  induction ws with
  | nil =>
    intro j L M hL hM hTR _ _
    refine ⟨by simpa using hL, fun l hl => ?_⟩
    exact hTR l (by simpa using hl)
  | cons wd ws ih =>
    intro j L M hL hM hTR hperm hok
    have hwd : ∀ z ∈ wd, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := fun z hz => by
      have := hok 0 (by simp) z (by simpa using hz)
      simpa using this
    have hWp : IsPermN n (wordFn G M wd) := wordFnPerm hGp hperm fun z hz => (hwd z hz).1
    have hWT : TR n (wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L) wd) (wordFn G M wd) :=
      wordT_TR hn wd fun z hz => letTR hG hTR (hwd z hz).2
    have hWi := invT_TR' hn hWT hWp
    have e1 : (wd :: ws).foldl (stepL n gens) L = ws.foldl (stepL n gens) (stepL n gens L wd) := rfl
    have e2 : lettersFrom n G M (wd :: ws) =
        lettersFrom n G (M ++ [wordFn G M wd, finv n (wordFn G M wd)]) ws := rfl
    rw [e1, e2]
    have hsz : (stepL n gens L wd).size = 2 * (j + 1) := by
      simp [stepL, hL]
      omega
    have key := ih (j + 1) (stepL n gens L wd) (M ++ [wordFn G M wd, finv n (wordFn G M wd)]) hsz
      (by simp [hM]; omega) ?_ ?_ ?_
    · have h2 : j + 1 + ws.length = j + (ws.length + 1) := by omega
      rw [h2] at key
      simpa using key
    · intro l hl
      show TR n ((L.push _).push _)[l]! _
      by_cases h1 : l < 2 * j
      · rw [getD_append_lt _ _ _ (by omega), push_get!_lt _ _ (by simp; omega),
          push_get!_lt _ _ (by omega)]
        exact hTR l h1
      · by_cases h2 : l = 2 * j
        · subst h2
          rw [getD_append_ge _ _ _ (by omega), hM, Nat.sub_self, ← hL, push_get!_lt _ _ (by simp),
            push_get!_eq]
          exact hWT
        · have h3 : l = 2 * j + 1 := by omega
          subst h3
          rw [getD_append_ge _ _ _ (by omega), hM, show 2 * j + 1 - 2 * j = 1 by omega]
          have h4 := push_get!_eq (L.push (wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L) wd))
            (invT n (wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L) wd))
          rw [Array.size_push, hL] at h4
          rw [h4]
          exact hWi
    · intro f hf
      rw [List.mem_append] at hf
      rcases hf with hf | hf
      · exact hperm f hf
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · exact hWp
        · exact hWp.finv
    · intro i hi z hz
      have := hok (i + 1) (by simpa using hi) z (by simpa using hz)
      have e : j + (i + 1) + 3 = j + 1 + i + 3 := by omega
      rw [e] at this
      exact this

private theorem gens_TR {n : Nat} {D : Data} (hn : n < 2 ^ 32) (hA : TR n D.tA (ap D.tA))
    (hA' : IsPermN n (ap D.tA)) (hB : TR n D.tB (ap D.tB)) (hB' : IsPermN n (ap D.tB)) (z : Int) :
    TR n (genAB n D z) (gensT n D.tA D.tB z) := by
  unfold genAB gensT
  by_cases h1 : z = 1
  · simp only [h1, if_true]
    exact hA
  by_cases h2 : z = -1
  · simp only [h1, h2, if_true, if_false]
    exact invT_TR' hn hA hA'
  by_cases h3 : z = 2
  · simp only [h1, h2, h3, if_true, if_false]
    exact hB
  · simp only [h1, h2, h3, if_true, if_false]
    exact invT_TR' hn hB hB'

private theorem gens_perm {n : Nat} {D : Data} (hA' : IsPermN n (ap D.tA))
    (hB' : IsPermN n (ap D.tB)) (z : Int) : IsPermN n (gensT n D.tA D.tB z) := by
  unfold gensT
  by_cases h1 : z = 1
  · simp only [h1, if_true]
    exact hA'
  by_cases h2 : z = -1
  · simp only [h1, h2, if_true, if_false]
    exact hA'.finv
  by_cases h3 : z = 2
  · simp only [h1, h2, h3, if_true, if_false]
    exact hB'
  · simp only [h1, h2, h3, if_true, if_false]
    exact hB'.finv

theorem letters_TR {n : Nat} {D : Data} (hn : n < 2 ^ 32) (hA : TR n D.tA (ap D.tA))
    (hA' : IsPermN n (ap D.tA)) (hB : TR n D.tB (ap D.tB)) (hB' : IsPermN n (ap D.tB))
    (hws : CFSG.KS.Mathieu.wordsOK D.words.toList 0 = true) :
    (letters n D).size = 2 * D.words.size ∧ ∀ l < 2 * D.words.size,
      TR n (letters n D)[l]! ((lettersFn n (gensT n D.tA D.tB) D.words.toList).getD l id) := by
  have hws' := (wordsOK_iff _ 0).1 hws
  have e : letters n D = D.words.toList.foldl (stepL n (genAB n D)) #[] := by
    rw [Array.foldl_toList]
    rfl
  have key := slp_fold hn (gens_TR hn hA hA' hB hB') (fun z _ _ => gens_perm hA' hB' z)
    D.words.toList 0 #[] [] (by simp) (by simp) (fun l hl => absurd hl (by simp))
    (fun f hf => absurd hf (by simp))
    (fun i hi z hz => ⟨(hws' i hi z hz).1, (hws' i hi z hz).2.1⟩)
  rw [e]
  simp only [Nat.zero_add, Array.length_toList] at key
  exact key

private theorem lettersFrom_prefix (n : Nat) (G : Int → Nat → Nat) (ws : List (List Int)) :
    ∀ M : List (Nat → Nat), ∃ R, lettersFrom n G M ws = M ++ R := by
  induction ws with
  | nil => intro M; exact ⟨[], by simp [lettersFrom]⟩
  | cons wd ws ih =>
    intro M
    obtain ⟨R, hR⟩ := ih (M ++ [wordFn G M wd, finv n (wordFn G M wd)])
    refine ⟨[wordFn G M wd, finv n (wordFn G M wd)] ++ R, ?_⟩
    have e2 : lettersFrom n G M (wd :: ws) =
        lettersFrom n G (M ++ [wordFn G M wd, finv n (wordFn G M wd)]) ws := rfl
    rw [e2, hR, List.append_assoc]

private theorem getD_pair_zero {α : Type} (M R : List α) (a b d : α) :
    (M ++ [a, b] ++ R).getD M.length d = a ∧ (M ++ [a, b] ++ R).getD (M.length + 1) d = b := by
  rw [List.append_assoc]
  constructor
  · rw [getD_append_ge _ _ _ (Nat.le_refl _), Nat.sub_self]
    simp
  · rw [getD_append_ge _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    simp

private theorem lettersFrom_odd (n : Nat) (G : Int → Nat → Nat) (ws : List (List Int)) :
    ∀ (M : List (Nat → Nat)) {j : Nat}, j < ws.length →
      (lettersFrom n G M ws).getD (M.length + 2 * j + 1) id =
        finv n ((lettersFrom n G M ws).getD (M.length + 2 * j) id) := by
  induction ws with
  | nil => intro M j hj; exact absurd hj (by simp)
  | cons wd ws ih =>
    intro M j hj
    have e2 : lettersFrom n G M (wd :: ws) =
        lettersFrom n G (M ++ [wordFn G M wd, finv n (wordFn G M wd)]) ws := rfl
    rw [e2]
    cases j with
    | zero =>
      obtain ⟨R, hR⟩ := lettersFrom_prefix n G ws (M ++ [wordFn G M wd, finv n (wordFn G M wd)])
      rw [hR]
      simp only [Nat.mul_zero, Nat.add_zero]
      obtain ⟨h1, h2⟩ := getD_pair_zero M R (wordFn G M wd) (finv n (wordFn G M wd)) id
      rw [h1, h2]
    | succ j =>
      have h := ih (M ++ [wordFn G M wd, finv n (wordFn G M wd)]) (j := j) (by simpa using hj)
      have e1 : (M ++ [wordFn G M wd, finv n (wordFn G M wd)]).length = M.length + 2 := by simp
      rw [e1] at h
      have e3 : M.length + 2 * (j + 1) = M.length + 2 + 2 * j := by omega
      rw [e3]
      exact h

theorem lettersFn_odd {n : Nat} (gens : Int → Nat → Nat) (ws : List (List Int)) {j : Nat}
    (hj : j < ws.length) :
    (lettersFn n gens ws).getD (2 * j + 1) id = finv n ((lettersFn n gens ws).getD (2 * j) id) := by
  have h := lettersFrom_odd n gens ws [] hj
  simp only [List.length_nil, Nat.zero_add] at h
  exact h

private theorem isPermN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ x < n, f x = g x)
    (hf : IsPermN n f) : IsPermN n g :=
  ⟨fun x hx => by rw [← h x hx]; exact hf.1 x hx,
    fun x hx y hy e => hf.2 x hx y hy (by rw [h x hx, h y hy]; exact e)⟩

private theorem finv_finv {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) {x : Nat} (hx : x < n) :
    finv n (finv n f) x = f x := by
  have h := finv_apply hf.finv (hf.1 x hx)
  rwa [finv_apply hf hx] at h

theorem lettersOK_letters {n : Nat} {D : Data} (hn : n < 2 ^ 32) (hD : D.words.size < 2 ^ 31)
    (hA : TR n D.tA (ap D.tA)) (hA' : IsPermN n (ap D.tA)) (hB : TR n D.tB (ap D.tB))
    (hB' : IsPermN n (ap D.tB)) (hws : CFSG.KS.Mathieu.wordsOK D.words.toList 0 = true) :
    LettersOK n (letters n D) := by
  obtain ⟨hsz, hTR⟩ := letters_TR hn hA hA' hB hB' hws
  have hlen : D.words.toList.length = D.words.size := Array.length_toList
  have hP : ∀ l < 2 * D.words.size,
      IsPermN n ((lettersFn n (gensT n D.tA D.tB) D.words.toList).getD l id) := fun l hl =>
    lettersFn_isPermN (fun z _ _ => gens_perm hA' hB' z) hws (by rw [hlen]; exact hl)
  have hodd : ∀ j < D.words.size,
      (lettersFn n (gensT n D.tA D.tB) D.words.toList).getD (2 * j + 1) id =
        finv n ((lettersFn n (gensT n D.tA D.tB) D.words.toList).getD (2 * j) id) :=
    fun j hj => lettersFn_odd _ _ (by rw [hlen]; exact hj)
  generalize lettersFn n (gensT n D.tA D.tB) D.words.toList = M at hTR hP hodd
  have hT : ∀ l < 2 * D.words.size, ∀ x < n, tabF (letters n D) l x = M.getD l id x :=
    fun l hl x hx => ((hTR l hl).2 x hx).1
  refine ⟨by omega, by omega, fun l hl => ?_⟩
  rw [hsz] at hl
  refine ⟨(hTR l hl).1, isPermN_congr (fun x hx => (hT l hl x hx).symm) (hP l hl), fun x hx => ?_⟩
  by_cases hev : l % 2 = 0
  · obtain ⟨j, rfl⟩ : ∃ j, l = 2 * j := ⟨l / 2, by omega⟩
    have hj : j < D.words.size := by omega
    have hinv : invL (2 * j) = 2 * j + 1 := by simp [invL]
    rw [hinv, hT (2 * j + 1) (by omega) x hx, hodd j hj]
    exact finv_congr (fun y hy => (hT (2 * j) hl y hy).symm) x
  · obtain ⟨j, rfl⟩ : ∃ j, l = 2 * j + 1 := ⟨l / 2, by omega⟩
    have hj : j < D.words.size := by omega
    have hinv : invL (2 * j + 1) = 2 * j := by
      unfold invL
      rw [if_neg hev]
      omega
    rw [hinv, hT (2 * j) (by omega) x hx]
    have hfp := hP (2 * j) (by omega)
    rw [finv_congr (g := finv n (M.getD (2 * j) id))
      (fun y hy => by rw [hT _ hl y hy, hodd j hj]) x, finv_finv hfp hx]

end CFSG.KS.PK

end
