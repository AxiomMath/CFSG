module

public import CFSG.Certificates.Kernel.Spor.RawTreeSound
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Co2

theorem rawInvs_get {n : Nat} {S : Array (Array Nat)} {i : Nat} (hi : i < S.size) :
    (rawInvs n S)[i]! = invCand n S[i]! := by
  rw [rawInvs, getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos _ i hi]

theorem wordA_prefix {n j : Nat} {S T : Array (Array Nat)} (hS : j ≤ S.size) (hT : j ≤ T.size)
    (he : ∀ i < j, S[i]! = T[i]!) :
    ∀ w : List Int, lettersOK j w = true → wordA n S (rawInvs n S) w = wordA n T (rawInvs n T) w
  | [], _ => rfl
  | l :: w, hl => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hl
    have ih := wordA_prefix (n := n) hS hT he w (by simpa [lettersOK] using hw)
    simp only [wordA]
    rw [ih]
    congr 1
    unfold letterA
    split_ifs with hpos
    · have hi : l.toNat - 1 < j := by omega
      exact he _ hi
    · have hi : (-l).toNat - 1 < j := by omega
      rw [rawInvs_get (by omega), rawInvs_get (by omega), he _ hi]

theorem eq_of_eqA_size {n : Nat} {a b : Array Nat} (ha : a.size = n) (hb : b.size = n)
    (h : eqA n a b = true) : a = b := by
  rw [eqA, allLt_iff] at h
  apply Array.ext (ha.trans hb.symm)
  intro i h1 h2
  have := h i (ha ▸ h1)
  rw [getElem!_pos a i h1, getElem!_pos b i h2] at this
  exact beq_iff_eq.1 this

theorem wordA_size {n : Nat} {S Sinv : Array (Array Nat)} :
    ∀ w : List Int, (wordA n S Sinv w).size = n
  | [] => by simp [wordA, idA]
  | l :: w => by simp [wordA, compA]

theorem extract_push {S : Array (Array Nat)} {m : Nat} (hm : m < S.size) :
    (S.extract 0 m).push S[m]! = S.extract 0 (m + 1) := by
  apply Array.ext
  · simp [Nat.min_eq_left (Nat.le_of_lt hm), Nat.min_eq_left hm]
  · intro i h1 h2
    rw [Array.getElem_push]
    split_ifs with hi
    · simp
    · have hi' : i = m := by simp at h1 hi; omega
      subst hi'
      simp [getElem!_pos S i hm]

theorem strongOf_eq {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {S O : Array (Array Nat)}
    {base : Array Nat} {D : List (List Int)} {W : Array (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hkO : kO ≤ kS) (hO : O.size = kO) (hOS : ∀ k < kO, O[k]! = S[k]!)
    (hW : W = CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) :
    CFSG.Sporadic.FischerOddCore.strongOf n O W = S := by
  have hH := rawHeadK_sound hb hh
  have hsz : S.size = kS := hb.2.2.2.1
  have hun : ∀ j < kS, S[j]!.size = n := fun j hj => by
    rw [hb.2.2.2.2.1 j hj, unpack, Array.size_ofFn]
  unfold rawHeadOK at hH
  simp only [Bool.and_eq_true] at hH
  have hwd := hH.1.1.2
  have hWs : W.size = kS := by
    rw [hW, CFSG.Sporadic.Schreier.Co3.Native.wordsArr, Array.size_ofFn]
  have hext : (S.extract 0 kO).size = kO := by simp [hsz, Nat.min_eq_left hkO]
  have key : ∀ m ≤ kS, (List.range m).foldl (fun S' j =>
      if j < O.size then S'.push O[j]! else S'.push (wordA n S' (rawInvs n S') W[j]!)) #[] =
      S.extract 0 m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        ← extract_push (by omega)]
      split_ifs with hmO
      · rw [hOS m (by omega)]
      · congr 1
        have h1 := allLt_spec hwd (i := m) (by omega)
        rw [hext] at h1
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1
        rcases h1 with h1 | ⟨hl, he⟩
        · omega
        · rw [← hW] at hl he
          rw [wordA_prefix (n := n) (j := m) (S := S.extract 0 m) (T := S)
            (by rw [Array.size_extract]; omega) (by omega)
            (fun i hi => by
              rw [getElem!_pos _ i (by rw [Array.size_extract]; omega), getElem!_pos S i (by omega)]
              simp) _ hl]
          exact (eq_of_eqA_size (hun m (by omega)) (wordA_size _) he).symm
  unfold CFSG.Sporadic.FischerOddCore.strongOf
  rw [hWs, key kS le_rfl, ← hsz, Array.extract_size]

end CFSG.KS.Raw

end
