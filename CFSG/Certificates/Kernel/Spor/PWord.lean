module

public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.CBfsKSound
public import Certificates.Data.CFSGNative.ONSchreier.Tools

public section

namespace CFSG.KS.PW

open CFSG.ONSchreier.Native CFSG.KS.TW

theorem ofFn_get' {n x : Nat} {f : Nat → Nat} (hx : x < n) :
    (Array.ofFn (n := n) fun i => f i.val)[x]! = f x := by
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem pcomp_get' {n : Nat} {t u : Array Nat} {i : Nat} (hi : i < n) :
    (pcomp n t u)[i]! = t[u[i]!]! := by
  unfold pcomp
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem pid_get' {n i : Nat} (hi : i < n) : (pid n)[i]! = i := by
  unfold pid
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem arr_ext {n : Nat} {g : Array Nat} {F : Nat → Nat} (hs : g.size = n)
    (h : ∀ x < n, g[x]! = F x) : g = Array.ofFn (n := n) fun i => F i.val := by
  apply Array.ext
  · rw [hs, Array.size_ofFn]
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, h i hi, ofFn_get' (f := F) hi]

theorem pword_size {n : Nat} {S Si : Array (Array Nat)} :
    ∀ w : List Int, (pword n S Si w).size = n
  | [] => by simp [pword, pid]
  | _ :: _ => by simp [pword, pcomp]

@[expose] def LettersOK (n m : Nat) (S Si : Array (Array Nat)) (G GI : Nat → Nat → Nat) : Prop :=
  ∀ j < m, ∀ x < n, S[j]![x]! = G j x ∧ Si[j]![x]! = GI j x ∧ G j x < n ∧ GI j x < n

theorem pletter_get {n m : Nat} {S Si : Array (Array Nat)} {G GI : Nat → Nat → Nat}
    (h : LettersOK n m S Si G GI) {l : Int} (hl : l ≠ 0 ∧ l.natAbs ≤ m) {x : Nat} (hx : x < n) :
    (pletter S Si l)[x]! = GZ G GI l x ∧ GZ G GI l x < n := by
  unfold pletter GZ
  by_cases hp : 0 < l
  · have hj : l.toNat - 1 < m := by omega
    simp only [hp, ite_true]
    exact ⟨(h _ hj x hx).1, (h _ hj x hx).2.2.1⟩
  · have hj : (-l).toNat - 1 < m := by omega
    simp only [hp, ite_false]
    exact ⟨(h _ hj x hx).2.1, (h _ hj x hx).2.2.2⟩

theorem pword_get {n m : Nat} {S Si : Array (Array Nat)} {G GI : Nat → Nat → Nat}
    (h : LettersOK n m S Si G GI) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) → ∀ x < n,
      (pword n S Si w)[x]! = w.foldr (GZ G GI) x ∧ w.foldr (GZ G GI) x < n
  | [], _, x, hx => ⟨pid_get' hx, hx⟩
  | l :: w, hw, x, hx => by
    obtain ⟨e, hlt⟩ := pword_get h w (fun z hz => hw z (List.mem_cons_of_mem l hz)) x hx
    obtain ⟨e', hlt'⟩ := pletter_get h (hw l List.mem_cons_self) hlt
    simp only [pword, List.foldr_cons]
    rw [pcomp_get' hx, e, e']
    exact ⟨rfl, hlt'⟩

theorem pword_eq {n m : Nat} {S Si : Array (Array Nat)} {G GI : Nat → Nat → Nat}
    (h : LettersOK n m S Si G GI) {w : List Int} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) :
    pword n S Si w = Array.ofFn (n := n) fun i => w.foldr (GZ G GI) i.val := by
  apply Array.ext
  · rw [pword_size, Array.size_ofFn]
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, (pword_get h w hw i hi).1,
      ofFn_get' (f := fun x => w.foldr (GZ G GI) x) hi]

theorem pwords_eq (n : Nat) (S Si : Array (Array Nat)) (ws : Array (List Int)) :
    pwords n S Si ws = ws.map (pword n S Si) := by
  unfold pwords
  simp

theorem pwords_get {n : Nat} {S Si : Array (Array Nat)} {ws : Array (List Int)} {j : Nat}
    (hj : j < ws.size) : (pwords n S Si ws)[j]! = pword n S Si ws[j]! := by
  rw [pwords_eq, getElem!_pos _ j (by simpa using hj), Array.getElem_map,
    getElem!_pos ws j hj]

@[expose] def ExtOK (n : Nat) (F FI : Nat → Nat → Nat) (k : Nat) (S Si : Array (Array Nat)) :
    Prop :=
  S.size = k ∧ Si.size = k ∧ ∀ j < k, S[j]! = (Array.ofFn (n := n) fun i => F j i.val) ∧
    ∀ x < n, Si[j]![x]! = FI j x

theorem extendStrong_get {n m s : Nat} {orig : Array (Array Nat)} {W : Array (List Int)}
    {F FI : Nat → Nat → Nat}
    (hm : orig.size = m) (hs : W.size = s) (hms : m ≤ s)
    (hO : ∀ j < m, orig[j]! = Array.ofFn (n := n) fun i => F j i.val)
    (hW : ∀ j, m ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, F j x = W[j]!.foldr (GZ F FI) x)
    (hinv : ∀ j < s, ∀ x < n, F j x < n ∧ FI j x < n ∧ FI j (F j x) = x) :
    (extendStrong n orig W).size = s ∧
      ∀ j < s, (extendStrong n orig W)[j]! = Array.ofFn (n := n) fun i => F j i.val := by
  have hpc : ∀ j < s, ∀ x < n, (pinvCand n (Array.ofFn (n := n) fun i => F j i.val))[x]! = FI j x :=
    fun j hj x hx => CFSG.KS.CB.pinvCand_get (fun y hy => (hinv j hj y hy).1)
      (fun y hy => (hinv j hj y hy).2.2) hx
  have step : ∀ k, m + k < s → ∀ S Si, ExtOK n F FI (m + k) S Si →
      ExtOK n F FI (m + k + 1) (S.push (pword n S Si W[m + k]!))
        (Si.push (pinvCand n (pword n S Si W[m + k]!))) := by
    intro k hk S Si ⟨hS, hSi, hj⟩
    have hL : LettersOK n (m + k) S Si F FI := by
      intro j hj' x hx
      obtain ⟨e1, e2⟩ := hj j hj'
      refine ⟨by rw [e1, ofFn_get' hx], e2 x hx, (hinv j (by omega) x hx).1,
        (hinv j (by omega) x hx).2.1⟩
    obtain ⟨hw, hf⟩ := hW (m + k) (by omega) hk
    have ep : pword n S Si W[m + k]! = Array.ofFn (n := n) fun i => F (m + k) i.val := by
      rw [pword_eq hL hw]
      congr 1
      funext i
      exact (hf i.val i.isLt).symm
    rw [ep]
    refine ⟨by simp [hS], by simp [hSi], fun j hj' => ?_⟩
    rcases Nat.lt_or_ge j (m + k) with h | h
    · obtain ⟨e1, e2⟩ := hj j h
      refine ⟨?_, fun x hx => ?_⟩
      · rw [getElem!_pos _ j (by simp [hS]; omega), Array.getElem_push_lt (by omega),
          ← getElem!_pos S j (by omega), e1]
      · rw [getElem!_pos (Si.push _) j (by simp [hSi]; omega), Array.getElem_push_lt (by omega),
          ← getElem!_pos Si j (by omega), e2 x hx]
    · have e : j = m + k := by omega
      subst e
      refine ⟨?_, fun x hx => ?_⟩
      · rw [getElem!_pos _ (m + k) (by simp [hS]), Array.getElem_push]
        simp [hS]
      · rw [getElem!_pos (Si.push _) (m + k) (by simp [hSi]), Array.getElem_push]
        simp only [hSi, Nat.lt_irrefl, ↓reduceDIte]
        exact hpc _ hk x hx
  have hloop : ∀ k, m + k ≤ s → ExtOK n F FI (m + k)
      ((List.range' m k).foldl (fun (p : Array (Array Nat) × Array (Array Nat)) j =>
        (p.1.push (pword n p.1 p.2 W[j]!), p.2.push (pinvCand n (pword n p.1 p.2 W[j]!))))
        (orig, orig.map (pinvCand n))).1
      ((List.range' m k).foldl (fun (p : Array (Array Nat) × Array (Array Nat)) j =>
        (p.1.push (pword n p.1 p.2 W[j]!), p.2.push (pinvCand n (pword n p.1 p.2 W[j]!))))
        (orig, orig.map (pinvCand n))).2 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hm, by simp [hm], fun j hj => ⟨hO j hj, fun x hx => ?_⟩⟩
      simp only [List.range'_zero, List.foldl_nil]
      rw [getElem!_pos _ j (by simp [hm]; exact hj), Array.getElem_map, ← getElem!_pos orig j
        (by omega), hO j hj]
      exact hpc j (by omega) x hx
    | succ k ih =>
      intro hk
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact step k (by omega) _ _ (ih (by omega))
  obtain ⟨hS, -, hj⟩ := hloop (s - m) (by omega)
  have e : extendStrong n orig W = ((List.range' m (s - m)).foldl
      (fun (p : Array (Array Nat) × Array (Array Nat)) j =>
        (p.1.push (pword n p.1 p.2 W[j]!), p.2.push (pinvCand n (pword n p.1 p.2 W[j]!))))
      (orig, orig.map (pinvCand n))).1 := by
    unfold extendStrong
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl, hm, hs]
  rw [e]
  have hms' : m + (s - m) = s := by omega
  rw [hms'] at hS hj
  exact ⟨hS, fun j hj' => (hj j hj').1⟩

theorem posArr_spec {n : Nat} {R : Array Nat} (hR : ∀ i < R.size, R[i]! < n)
    (hd : ∀ i < R.size, ∀ j < i, R[j]! ≠ R[i]!) :
    (posArr n R).size = n ∧ ∀ i < R.size, (posArr n R)[R[i]!]! = i := by
  have heq : posArr n R =
      (List.range' 0 R.size).foldl (fun p i => p.set! R[i]! i) (Array.replicate n R.size) := by
    unfold posArr
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  rw [heq]
  exact CFSG.KS.CB.set_loop hR hd

@[expose] def bpt (B : Array (Array Nat)) (u : Nat) : Nat := B[u / 2]![u % 2]!

theorem blockPos_loop {n : Nat} {B : Array (Array Nat)} (h2 : ∀ i < B.size, B[i]!.size = 2) :
    ∀ k ≤ B.size, (List.range' 0 k).foldl (fun t i => B[i]!.foldl (fun t p => t.set! p i) t)
        (Array.replicate n B.size) =
      (List.range' 0 (2 * k)).foldl (fun t u => t.set! (bpt B u) (u / 2)) (Array.replicate n B.size)
  | 0, _ => rfl
  | k + 1, hk => by
    have e2k : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    have q0 : 2 * k / 2 = k := by omega
    have q1 : (2 * k + 1) / 2 = k := by omega
    have r0 : 2 * k % 2 = 0 := by omega
    have r1 : (2 * k + 1) % 2 = 1 := by omega
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      blockPos_loop h2 k (by omega), e2k,
      List.range'_1_concat, List.range'_1_concat, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add]
    generalize (List.range' 0 (2 * k)).foldl (fun t u => t.set! (bpt B u) (u / 2))
      (Array.replicate n B.size) = t
    have hs := h2 k (by omega)
    rcases hB : B[k]! with ⟨l⟩
    have hl : l.length = 2 := by
      rw [hB] at hs
      simpa using hs
    match l, hl with
    | [a, b], _ =>
      have e1 : bpt B (2 * k) = a := by
        unfold bpt
        rw [q0, r0, hB]
        rfl
      have e2 : bpt B (2 * k + 1) = b := by
        unfold bpt
        rw [q1, r1, hB]
        rfl
      rw [e1, e2, q0, q1]
      simp

theorem blockPos_spec {n : Nat} {B : Array (Array Nat)} (h2 : ∀ i < B.size, B[i]!.size = 2)
    (hlt : ∀ u < 2 * B.size, bpt B u < n) (hd : ∀ u < 2 * B.size, ∀ v < u, bpt B v ≠ bpt B u) :
    (blockPos n B).size = n ∧ ∀ u < 2 * B.size, (blockPos n B)[bpt B u]! = u / 2 := by
  have heq : blockPos n B = (List.range' 0 B.size).foldl
      (fun t i => B[i]!.foldl (fun t p => t.set! p i) t) (Array.replicate n B.size) := by
    unfold blockPos
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  rw [heq, blockPos_loop h2 B.size (Nat.le_refl _)]
  exact set_loopV hlt hd

end CFSG.KS.PW

end
