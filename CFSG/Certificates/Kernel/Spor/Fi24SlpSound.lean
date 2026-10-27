module

public import CFSG.Certificates.Kernel.Spor.SlpMatSound
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7GenData
public import CFSG.Sporadic.Fi24.ExtWSpec

public section

namespace CFSG.KC.SlpM

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.HardMathSupport.Dickson.I271.Fi7

abbrev Mat781 := Matrix (Fin 781) (Fin 781) (ZMod 3)

noncomputable abbrev gW : Int → Mat781 := gen3 (matW 781 781 (matA ())) (matW 781 781 (matB ()))

@[expose] def Good (X : Array W) (M : Mat781) : Prop := canonRows 781 X = true ∧ matW 781 781 X = M

theorem Good.mulW {X Y : Array W} {M N : Mat781} (hX : Good X M) (hY : Good Y N) :
    Good (mulW X Y) (M * N) :=
  ⟨canonRows_mulW hX.1 hY.1, by
    rw [matW_mulW (m := 781) (by norm_num) (RowsWF.of_canonRows hX.1) (RowsWF.of_canonRows hY.1)
      (by rw [(canonRows_spec hY.1).1]), hX.2, hY.2]⟩

theorem Good.congr {X : Array W} {M N : Mat781} (h : Good X M) (e : M = N) : Good X N := e ▸ h

theorem good_idW : Good (idW 781) 1 := ⟨canonRows_idW, matW_idW (by norm_num)⟩

theorem good_matA : Good (matA ()) (matW 781 781 (matA ())) :=
  ⟨by unfold matA; exact canonRows_rowsOfSeed 781 le_rfl _, rfl⟩

theorem good_matB : Good (matB ()) (matW 781 781 (matB ())) :=
  ⟨by unfold matB; exact canonRows_rowsOfSeed 781 le_rfl _, rfl⟩

theorem good_powW {X : Array W} {M : Mat781} (h : Good X M) : ∀ e : Nat, Good (powW 781 X e) (M ^ e)
  | 0 => by rw [pow_zero]; exact good_idW
  | e + 1 => by rw [Native.powW, pow_succ]; exact (good_powW h e).mulW h

theorem good_mGen (z : Int) : Good (mGen z) (gW z) := by
  unfold mGen
  change Good _ (gen3 _ _ z)
  unfold gen3
  split_ifs
  · exact good_matA
  · exact good_matB
  · exact good_powW good_matB 2

theorem good_foldl {f : Int → Array W} {g : Int → Mat781} :
    ∀ (ls : List Int), (∀ z ∈ ls, Good (f z) (g z)) → ∀ {acc : Array W} {M0 : Mat781}, Good acc M0 →
      Good (ls.foldl (fun acc z => Native.mulW acc (f z)) acc) (M0 * (ls.map g).prod)
  | [], _, _, _, h => by simpa using h
  | z :: ls, h, _, _, h0 => by
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact good_foldl ls (fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))
      (h0.mulW (h z List.mem_cons_self))

theorem good_mProd {f : Int → Array W} {g : Int → Mat781} (w : List Int)
    (h : ∀ z ∈ w, Good (f z) (g z)) : Good (mProd f w) (w.map g).prod := by
  cases w with
  | nil => exact good_idW
  | cons l ls =>
    unfold mProd
    have := good_foldl ls (fun z hz => h z (List.mem_cons_of_mem _ hz)) (h l List.mem_cons_self)
    rwa [List.map_cons, List.prod_cons]

@[expose] def OkZ (n : Nat) (z : Int) : Prop := z.natAbs ≤ 2 ∨ z.natAbs < n + 3

@[expose] def Inv (L : Array (Array W)) (S : Array Mat781) : Prop :=
  L.size = S.size ∧ ∀ k < L.size, Good L[k]! (S.getD k 1)

theorem good_mLetter {L : Array (Array W)} {S : Array Mat781} {n : Nat} (hI : Inv L S)
    (hn : L.size = 2 * n) {z : Int} (hz : OkZ n z) : Good (mLetter L z) (semLetter gW S z) := by
  unfold mLetter semLetter
  split_ifs with h1 h2
  · exact good_mGen z
  · exact hI.2 _ (by rcases hz with h | h <;> omega)
  · exact hI.2 _ (by rcases hz with h | h <;> omega)

theorem okZ_neg {n : Nat} {z : Int} (h : OkZ n z) : OkZ n (-z) := by
  unfold OkZ at *
  rwa [Int.natAbs_neg]

theorem good_mWord {L : Array (Array W)} {S : Array Mat781} {n : Nat} (hI : Inv L S)
    (hn : L.size = 2 * n) {w : List Int} (hw : ∀ z ∈ w, OkZ n z) :
    Good (mWord L w) (semWord gW S w) :=
  good_mProd w fun z hz => good_mLetter hI hn (hw z hz)

theorem good_mWordInv {L : Array (Array W)} {S : Array Mat781} {n : Nat} (hI : Inv L S)
    (hn : L.size = 2 * n) {w : List Int} (hw : ∀ z ∈ w, OkZ n z) :
    Good (mWordInv L w) (semWordInv gW S w) :=
  good_mProd w.reverse fun z hz => good_mLetter hI hn (okZ_neg (hw z (List.mem_reverse.1 hz)))

theorem push_getElem!_lt {α : Type} [Inhabited α] (L : Array α) (x : α) {k : Nat} (hk : k < L.size) :
    (L.push x)[k]! = L[k]! := by
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_push_lt hk, getElem!_pos L k hk]

theorem push_getElem!_eq {α : Type} [Inhabited α] (L : Array α) (x : α) :
    (L.push x)[L.size]! = x := by
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

theorem inv_step {L : Array (Array W)} {S : Array Mat781} {n : Nat} (hI : Inv L S)
    (hn : L.size = 2 * n) {w : List Int} (hw : ∀ z ∈ w, OkZ n z) :
    Inv ((L.push (mWord L w)).push (mWordInv L w)) (semStep gW S w) := by
  refine ⟨by rw [semStep_size]; simp [hI.1], fun k hk => ?_⟩
  simp only [Array.size_push] at hk
  have hS : S.size = L.size := hI.1.symm
  rcases (by omega : k < L.size ∨ k = L.size ∨ k = L.size + 1) with h | rfl | rfl
  · rw [push_getElem!_lt _ _ (by simp; omega), push_getElem!_lt _ _ h]
    have e : (semStep gW S w).getD k 1 = S.getD k 1 := by
      simp only [Array.getD_eq_getD_getElem?]
      rw [semStep_getElem? gW S w (by omega)]
    rw [e]
    exact hI.2 k h
  · rw [push_getElem!_lt _ _ (by simp), push_getElem!_eq]
    have e : (semStep gW S w).getD L.size 1 = semWord gW S w := by
      unfold semStep
      simp only [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_push, if_neg (by simp; omega), Array.getElem?_push, if_pos hS.symm]
      rfl
    rw [e]
    exact good_mWord hI hn hw
  · have e1 : L.size + 1 = (L.push (mWord L w)).size := by simp
    rw [e1, push_getElem!_eq]
    have e : (semStep gW S w).getD (L.size + 1) 1 = semWordInv gW S w := by
      unfold semStep
      simp only [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_push, if_pos (by simp; omega)]
      rfl
    rw [← e1, e]
    exact good_mWordInv hI hn hw

theorem inv_foldl : ∀ (ws : List (List Int)) {L : Array (Array W)} {S : Array Mat781} {n : Nat},
    Inv L S → L.size = 2 * n → (∀ i < ws.length, ∀ z ∈ ws[i]!, OkZ (n + i) z) →
    Inv (ws.foldl (fun L w => (L.push (mWord L w)).push (mWordInv L w)) L)
      (ws.foldl (semStep gW) S) ∧
      (ws.foldl (fun L w => (L.push (mWord L w)).push (mWordInv L w)) L).size = 2 * (n + ws.length)
  | [], _, _, _, hI, hn, _ => ⟨hI, by simpa using hn⟩
  | w :: ws, L, S, n, hI, hn, h => by
    rw [List.foldl_cons, List.foldl_cons]
    have hw : ∀ z ∈ w, OkZ n z := by simpa using h 0 (by simp)
    have := inv_foldl ws (inv_step hI hn hw) (n := n + 1) (by simp [hn]; omega) fun i hi z hz => by
      have := h (i + 1) (by simp; omega) z (by simpa using hz)
      rwa [show n + (i + 1) = n + 1 + i by omega] at this
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem mLetters_good {Ws : Array (List Int)} (hs : CFSG.Sporadic.Fi23.Native.slpOK Ws = true) :
    Inv (mLetters Ws) (semArr gW Ws) ∧ (mLetters Ws).size = 2 * Ws.size := by
  have h : ∀ i < Ws.toList.length, ∀ z ∈ Ws.toList[i]!, OkZ (0 + i) z := by
    intro i hi z hz
    unfold CFSG.Sporadic.Fi23.Native.slpOK CFSG.Sporadic.Th.Native.allIn at hs
    rw [Nat.all_eq_finRange_all, List.all_eq_true] at hs
    have := hs ⟨i, by simpa using hi⟩ (List.mem_finRange _)
    simp only [Nat.sub_zero, Nat.zero_add, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Bool.or_eq_true, decide_eq_true_eq] at this
    have hz' : z ∈ Ws[i]! := by
      rwa [getElem!_pos Ws i (by simpa using hi), ← Array.getElem_toList,
        ← getElem!_pos Ws.toList i hi]
    have := (this z hz').2
    unfold OkZ
    omega
  have := inv_foldl Ws.toList (L := #[]) (S := #[]) (n := 0) ⟨rfl, fun k hk => absurd hk (by simp)⟩
    rfl h
  unfold mLetters semArr
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simpa using this

theorem mWord_good {Ws : Array (List Int)} (hs : CFSG.Sporadic.Fi23.Native.slpOK Ws = true)
    {w : List Int} (hw : ∀ z ∈ w, OkZ Ws.size z) : Good (mWord (mLetters Ws) w) (semWord gW (semArr gW Ws) w) :=
  good_mWord (mLetters_good hs).1 (mLetters_good hs).2 hw

theorem slpOK_of_slpC {W : List (List Nat)} (h : slpC W 0 = true) :
    CFSG.Sporadic.Fi23.Native.slpOK (W.map decW).toArray = true := by
  unfold CFSG.Sporadic.Fi23.Native.slpOK CFSG.Sporadic.Th.Native.allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨i, hi⟩ _
  simp only [List.size_toArray, List.length_map, Nat.sub_zero] at hi
  simp only [Nat.zero_add, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
    decide_eq_true_eq]
  intro z hz
  have e : (W.map decW).toArray[i]! = decW W[i]! := by
    rw [getElem!_pos _ i (by simpa using hi), List.getElem_toArray, List.getElem_map,
      getElem!_pos W i hi]
  rw [e] at hz
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
  have := slpC_spec h i hi c hc
  rw [decC_natAbs]
  refine ⟨fun h0 => ?_, by omega⟩
  have := decC_natAbs c
  rw [h0] at this
  simp at this
  omega

theorem eqRows_of_good {X Y : Array W} {M : Mat781} (hX : Good X M) (hY : Good Y M) :
    eqRows 781 X Y = true := by
  have e : X = Y := eq_of_matW_eq hX.1 hY.1 (by rw [hX.2, hY.2])
  unfold eqRows
  rw [e, (canonRows_spec hY.1).1]
  simp

theorem eqRows_false_of_good {X Y : Array W} {M N : Mat781} (hX : Good X M) (hY : Good Y N)
    (h : M ≠ N) : eqRows 781 X Y = false := by
  cases hb : eqRows 781 X Y
  · rfl
  · exact absurd (by rw [← hX.2, ← hY.2, (eq_of_eqRows hb).2]) h

end CFSG.KC.SlpM

end
