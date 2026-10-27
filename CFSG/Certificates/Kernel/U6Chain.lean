module

public import CFSG.Certificates.NativeValidSchreier
public import CFSG.Sporadic.Schreier.Enumeration
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Co3.Native

variable {n : ℕ}

theorem evalCodes_eq_evalWord {j : ℕ} (L : List (Equiv.Perm (Fin n)))
    (gs : ℕ → Equiv.Perm (Fin n)) (hgs : ∀ h < j, L.getD h 1 = gs h) :
    ∀ w : List ℤ, lettersOK j w = true →
      evalCodes L w = Quiver.SchreierGraph.evalWord (fun h : Fin j => gs h) (toLetters j w)
  | [], _ => rfl
  | z :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hz0, hzj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    have hcons : toLetters j (z :: w) = (⟨z.natAbs - 1, by omega⟩, decide (0 < z)) ::
        toLetters j w := by
      simp [toLetters, hz0, hzj]
    rw [hcons, evalCodes, evalCodes_eq_evalWord L gs hgs w hw']
    by_cases hpos : 0 < z
    · have e : z.toNat - 1 = z.natAbs - 1 := by omega
      rw [ite_eq_left hpos, decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true, e,
        hgs _ (by omega)]
    · have e : (-z).toNat - 1 = z.natAbs - 1 := by omega
      rw [ite_eq_right hpos, decide_eq_false hpos, Quiver.SchreierGraph.evalWord_cons_false, e,
        hgs _ (by omega)]

theorem buildStrong_append (S : List (Equiv.Perm (Fin n))) (ws vs : List (List ℤ)) :
    buildStrong S (ws ++ vs) = buildStrong (buildStrong S ws) vs := by
  induction ws generalizing S with
  | nil => rfl
  | cons w ws ih => exact ih _

theorem buildStrong_prefix (S : List (Equiv.Perm (Fin n))) (ws : List (List ℤ)) :
    ∃ R, buildStrong S ws = S ++ R := by
  induction ws generalizing S with
  | nil => exact ⟨[], (List.append_nil S).symm⟩
  | cons w ws ih =>
    obtain ⟨R, hR⟩ := ih (S ++ [tab (evalCodes S w)])
    exact ⟨[tab (evalCodes S w)] ++ R, by rw [buildStrong, hR, List.append_assoc]⟩

theorem buildStrong_getD_lt (S : List (Equiv.Perm (Fin n))) (ws : List (List ℤ)) {h : ℕ}
    (hh : h < S.length) : (buildStrong S ws).getD h 1 = S.getD h 1 := by
  obtain ⟨R, hR⟩ := buildStrong_prefix S ws
  rw [hR, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hh]

theorem buildStrong_getD (S : List (Equiv.Perm (Fin n))) (ws : List (List ℤ)) {t : ℕ}
    (ht : t < ws.length) :
    (buildStrong S ws).getD ((buildStrong S (ws.take t)).length) 1 =
      tab (evalCodes (buildStrong S (ws.take t)) (ws.getD t [])) := by
  set P := buildStrong S (ws.take t)
  have e : ws = ws.take t ++ (ws.getD t [] :: ws.drop (t + 1)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    simp
  have hb : buildStrong S ws =
      buildStrong (P ++ [tab (evalCodes P (ws.getD t []))]) (ws.drop (t + 1)) := by
    conv_lhs => rw [e]
    rw [buildStrong_append, buildStrong]
  obtain ⟨R, hR⟩ := buildStrong_prefix (P ++ [tab (evalCodes P (ws.getD t []))]) (ws.drop (t + 1))
  rw [hb, hR, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (le_refl _)]
  simp

theorem length_buildStrong_take (S : List (Equiv.Perm (Fin n))) (ws : List (List ℤ)) {t : ℕ}
    (ht : t ≤ ws.length) : (buildStrong S (ws.take t)).length = S.length + t := by
  rw [length_buildStrong, List.length_take, min_eq_left ht]

theorem rep_of_eqA {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (hu : Rep n u g)
    (he : eqA n t u = true) : Rep n t g := fun x => by
  have := allLt_spec he x.2
  rw [beq_iff_eq] at this
  rw [this, hu x]

theorem certificate_chainArrays (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List ℤ)) {k : ℕ} (base : Vector (Fin n) k) (hbase : base.toList.Nodup)
    {O S : Array (Array ℕ)} {baseA : Array ℕ} {chunks : ℕ}
    (h : rawChainOK n O S baseA (wordsArr gens.length (gens.length + words.length) words)
      chunks = true)
    (hO : O.size = gens.length) (hS : S.size = gens.length + words.length)
    (hrep : ∀ j < gens.length, Rep n O[j]! (gens.getD j 1))
    (hbA : baseA.size = k) (hbv : ∀ i : Fin k, ((base.get i : Fin n) : ℕ) = baseA[(i : ℕ)]!) :
    ChainArrays (certificate hn gens words base hbase) O S baseA
      (wordsArr gens.length (gens.length + words.length) words) := by
  have hF := chainCheckFacts h
  set W := wordsArr gens.length (gens.length + words.length) words
  set gs : ℕ → Equiv.Perm (Fin n) := fun h => (buildStrong gens words).getD h 1 with hgs
  have hWj : ∀ j, gens.length ≤ j → j < gens.length + words.length →
      W[j]! = words.getD (j - gens.length) [] := by
    intro j hj1 hj2
    simp only [W, wordsArr]
    rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn]
    simp [show ¬ j < gens.length by omega]
  have hstrong : ∀ j, j < S.size → Rep n S[j]! (gs j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjo : j < gens.length
      · have hr := hrep j hjo
        have he := hF.initial j (by omega)
        rw [show gs j = gens.getD j 1 from buildStrong_getD_lt gens words hjo]
        exact rep_of_eqA hr he
      · obtain ⟨hl, he⟩ := hF.words j hj (by omega)
        have hSinv : ∀ h < j, Rep n (rawInvs n S)[h]! (gs h)⁻¹ := fun h hh =>
          rep_inv_of_isInvA (ih h hh (by omega)) (hF.strong_inv h (by omega))
        have hw := rep_wordA (n := n) (fun h hh => ih h hh (by omega)) hSinv W[j]! hl
        set t := j - gens.length with ht
        have htw : t < words.length := by omega
        have hlen := length_buildStrong_take gens words (le_of_lt htw)
        have hjt : j = (buildStrong gens (words.take t)).length := by omega
        have hgj : gs j = evalCodes (buildStrong gens (words.take t)) (words.getD t []) := by
          rw [hgs]
          simp only
          rw [hjt, buildStrong_getD gens words htw, tab_eq]
        rw [hgj, ← hWj j (by omega) (by omega)]
        rw [evalCodes_eq_evalWord (j := j) _ gs (fun h hh => ?_) _ hl]
        · exact rep_of_eqA hw he
        · rw [hgs]
          simp only
          obtain ⟨R, hR⟩ := buildStrong_prefix (buildStrong gens (words.take t))
            (words.drop t)
          rw [← buildStrong_append, List.take_append_drop] at hR
          rw [hR, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega)]
  refine ⟨hO, by rw [hS]; rfl, hbA, fun j => ?_, fun j => ?_, hbv, fun j hj => ?_⟩
  · convert hrep j.val j.2 using 1
    simp [certificate, Vector.get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.2]
    rfl
  · have hj : j.val < (buildStrong gens words).length := by
      rw [length_buildStrong]
      exact j.2
    convert hstrong j.val (by rw [hS]; exact j.2) using 1
    simp [certificate, Vector.get, gs, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]
    rfl
  · have hjs : j.val < gens.length + words.length := j.2
    simp only [certificate] at hj ⊢
    rw [hWj j.val hj hjs]
    obtain ⟨hl, -⟩ := hF.words j.val (by rw [hS]; exact hjs) (by rw [hO]; exact hj)
    rw [hWj j.val hj hjs] at hl
    simp only [decodeWord, toLetters]
    apply List.filterMap_congr
    intro z hz
    have hzl := List.all_eq_true.1 hl z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hzl
    simp only [decodeLetter]
    rw [dite_eq_left (by omega), dite_eq_left ⟨hzl.1, hzl.2⟩]

end CFSG.Certificates

end
