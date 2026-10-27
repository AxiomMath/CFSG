module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.KC.U6Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

theorem wordA_size (n : ℕ) (S Sinv : Array (Array ℕ)) : ∀ w, (wordA n S Sinv w).size = n
  | [] => by simp [wordA, idA]
  | _ :: _ => by simp [wordA, compA]

theorem wordA_congr {n k : ℕ} {S T : Array (Array ℕ)} (hS : k ≤ S.size) (hT : k ≤ T.size)
    (h : ∀ i < k, S[i]! = T[i]!) :
    ∀ w, lettersOK k w = true → wordA n S (rawInvs n S) w = wordA n T (rawInvs n T) w
  | [], _ => rfl
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true] at hw
    have ih := wordA_congr (n := n) hS hT h w hw.2
    have hl := hw.1
    simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] at hl
    simp only [wordA, ih]
    congr 1
    unfold letterA
    have hinv : ∀ i < k, (rawInvs n S)[i]! = (rawInvs n T)[i]! := fun i hi => by
      rw [rawInvs, rawInvs, getElem!_pos _ i (by simp; omega), getElem!_pos _ i (by simp; omega),
        Array.getElem_map, Array.getElem_map, ← getElem!_pos S i (by omega),
        ← getElem!_pos T i (by omega), h i hi]
    split_ifs with hl'
    · exact h _ (by omega)
    · exact hinv _ (by omega)

theorem foldl_push_eq {SA : Array (Array ℕ)} (hn : ∀ j < SA.size, SA[j]!.size = 693) :
    ∀ (ws : List (List ℤ)) (k : ℕ), k + ws.length = SA.size →
      (∀ m < ws.length, lettersOK (k + m) ws[m]! = true ∧
        eqA 693 SA[k + m]! (wordA 693 SA (rawInvs 693 SA) ws[m]!) = true) →
      ws.foldl (fun S w => S.push (wordA 693 S (rawInvs 693 S) w)) (SA.extract 0 k) = SA
  | [], k, hk, _ => by
    apply Array.ext
    · simp at hk ⊢
      omega
    · intro i h1 h2
      simp
  | w :: ws, k, hk, h => by
    simp only [List.length_cons] at hk
    rw [List.foldl_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at h0
    have hkS : k < SA.size := by omega
    have e1 : wordA 693 (SA.extract 0 k) (rawInvs 693 (SA.extract 0 k)) w =
        wordA 693 SA (rawInvs 693 SA) w :=
      wordA_congr (by simp; omega) (by omega) (fun i hi => by
        rw [getElem!_pos _ i (by simp; omega), Array.getElem_extract, getElem!_pos SA i (by omega)]
        simp) w h0.1
    have e2 : SA[k]! = wordA 693 SA (rawInvs 693 SA) w := by
      apply Array.ext
      · rw [hn k hkS, wordA_size]
      · intro i h1 h2
        have hi : i < 693 := by rw [hn k hkS] at h1; exact h1
        have := CFSG.Monster.B.Co2.allLt_spec h0.2 hi
        rw [beq_iff_eq, getElem!_pos _ i h1, getElem!_pos _ i h2] at this
        exact this
    have e3 : (SA.extract 0 k).push (wordA 693 (SA.extract 0 k) (rawInvs 693 (SA.extract 0 k)) w) =
        SA.extract 0 (k + 1) := by
      rw [e1, ← e2]
      apply Array.ext
      · simp
        omega
      · intro i h1 h2
        simp only [Array.size_push, Array.size_extract] at h1
        rw [Array.getElem_push]
        split_ifs with hi
        · simp
        · have : i = k := by simp at hi; omega
          subst this
          simp [getElem!_pos SA i hkS]
    rw [e3]
    refine foldl_push_eq hn ws (k + 1) (by omega) fun m hm => ?_
    have := h (m + 1) (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 m] using this

theorem S_eq_of_rawChainOK' (c : ChainData) {SA : Array (Array ℕ)}
    (hraw : rawChainOK 693 (SA.extract 0 c.gens.length) SA c.B
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr c.gens.length SA.size c.words) 1 = true)
    (hsize : SA.size = c.gens.length + c.words.length)
    (hO : ∀ j < c.gens.length, SA[j]! = c.O[j]!)
    (hn : ∀ j < SA.size, SA[j]!.size = 693) : c.S = SA := by
  have hF := CFSG.Certificates.chainCheckFacts hraw
  have hOe : c.O = SA.extract 0 c.gens.length := by
    apply Array.ext
    · simp only [ChainData.O_size, Array.size_extract]
      omega
    · intro i h1 h2
      have hi : i < c.gens.length := by rw [ChainData.O_size] at h1; exact h1
      rw [← getElem!_pos c.O i h1, ← hO i hi, getElem!_pos SA i (by omega)]
      simp
  rw [ChainData.S, hOe]
  refine foldl_push_eq hn c.words c.gens.length hsize.symm fun m hm => ?_
  have hj : c.gens.length + m < SA.size := by omega
  have hw := hF.words _ hj (by simp only [Array.size_extract]; omega)
  have eW : (CFSG.Sporadic.Schreier.Co3.Native.wordsArr c.gens.length SA.size c.words)[
      c.gens.length + m]! = c.words[m]! := by
    rw [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, getElem!_pos _ _ (by simpa using hj),
      Array.getElem_ofFn]
    simp [List.getD_eq_getElem?_getD, getElem!_pos c.words m hm, List.getElem?_eq_getElem hm]
  rw [eW] at hw
  exact hw

end CFSG.KC.U6Sec3

end
