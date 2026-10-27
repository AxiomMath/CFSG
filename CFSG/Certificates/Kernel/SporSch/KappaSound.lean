module

public import Certificates.Data.Kernel.SporSch.Kappa
import all CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.SporSch.AnyN
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native

private theorem posIn_getElem! {I : Array Nat} {j : Nat} (hj : j < I.size)
    (hd : ∀ i < j, I[i]! ≠ I[j]!) : posIn I I[j]! = j := by
  unfold posIn
  rw [show I.findIdx? (· == I[j]!) = some j from ?_]
  · rfl
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨hj, by simp [getElem!_pos I j hj], fun i hi => ?_⟩
  have := hd i hi
  rw [getElem!_pos I i (by omega), getElem!_pos I j hj] at this
  simpa [getElem!_pos I j hj] using this

private theorem compA_getElem! {n i : Nat} {t u : Array Nat} (hi : i < n) :
    (compA n t u)[i]! = t[u[i]!]! := by
  rw [getElem!_pos _ i (by simpa [compA] using hi)]
  exact CFSG.KS.Prim.compA_getElem _

private theorem restrictA_getElem! {I m : Array Nat} {j : Nat} (hj : j < I.size) :
    (restrictA I m)[j]! = posIn I m[I[j]!]! := by
  rw [getElem!_pos _ j (by simpa [restrictA] using hj)]
  simp [restrictA, getElem!_pos I j hj]

private theorem anyLt_of_exists {f : Nat → Bool} {j : Nat} :
    ∀ {m : Nat}, j < m → f j = true → anyLt m f = true
  | 0, hj, _ => absurd hj (Nat.not_lt_zero j)
  | m + 1, hj, hf => by
    unfold anyLt at *
    rw [Nat.any_succ, Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact Or.inl (anyLt_of_exists h hf)
    · subst h
      exact Or.inr hf

theorem kappaK_sound {n w k w' IP CP CIP M K : Nat}
    (h : kappaK n w k w' IP CP CIP M K = true) :
    renameA k (unpack k w' CP) (restrictA (unpack k w IP) (unpack n w M)) = unpack k w' K := by
  unfold kappaK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, hIr, hId, hP, hK, hchk⟩ := h
  have hP' : permOK k w' (mask w') (k * w') CP CIP = true := hP
  obtain ⟨hc, hsurj⟩ := CFSG.KS.Prim.perm_facts hP'
  obtain ⟨-, -, -, hKr⟩ := CFSG.KS.Prim.canon_facts hK
  have hinv := (CFSG.KS.Prim.invEqK_sound hP').1
  have hci : ∀ j < k, pg w' (mask w') CIP j < k ∧
      pg w' (mask w') CP (pg w' (mask w') CIP j) = j := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := hsurj j hj
    rw [(hc i hi).2]
    exact ⟨hi, rfl⟩
  have hd : ∀ i < k, ∀ j < i, pg w (mask w) IP j ≠ pg w (mask w) IP i := by
    intro i hi j hj e
    have := allN_spec (allN_spec hId i hi) j hj
    rw [e, Nat.beq_refl] at this
    exact Bool.false_ne_true this
  have hIs : (unpack k w IP).size = k := CFSG.KS.Prim.unpack_size k w IP
  apply Array.ext
  · simp [renameA, compA, CFSG.KS.Prim.unpack_size]
  · intro i h1 h2
    have hi : i < k := by simpa [CFSG.KS.Prim.unpack_size] using h2
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2]
    obtain ⟨hj, hcj⟩ := hci i hi
    obtain ⟨ht, hct⟩ := hci _ (hKr i hi)
    have e := Nat.eq_of_beq_eq_true (allN_spec hchk _ hj)
    rw [hcj] at e
    have hpos : posIn (unpack k w IP) (unpack k w IP)[pg w' (mask w') CIP (pg w' (mask w') K i)]! =
        pg w' (mask w') CIP (pg w' (mask w') K i) := by
      refine posIn_getElem! (by omega) fun a ha => ?_
      rw [CFSG.KS.Prim.unpack_get (by omega), CFSG.KS.Prim.unpack_get ht]
      exact hd _ ht a ha
    rw [CFSG.KS.Prim.unpack_get hi, renameA, compA_getElem! hi, hinv,
      CFSG.KS.Prim.unpack_get hi, compA_getElem! hj, restrictA_getElem! (by omega), CFSG.KS.Prim.unpack_get (p := IP) hj,
      CFSG.KS.Prim.unpack_get (p := M) (by simpa [Nat.blt_eq] using allN_spec hIr _ hj), e,
      ← CFSG.KS.Prim.unpack_get ht, hpos, CFSG.KS.Prim.unpack_get ht, hct]

theorem coversK_sound {n w kg kh : Nat} {G H : Nat → Nat} {gs hs : Array (Array Nat)}
    (hg : gs.size = kg ∧ ∀ i < kg, gs[i]! = unpack n w (G i))
    (hh : hs.size = kh ∧ ∀ j < kh, hs[j]! = unpack n w (H j))
    (h : coversK n w G kg H kh = true) :
    coversOK n gs hs = true := by
  unfold coversK at h
  simp only [bAnd_iff] at h
  obtain ⟨hG, -, h1, h2⟩ := h
  obtain ⟨hgs, hgi⟩ := hg
  obtain ⟨hhs, hhi⟩ := hh
  unfold coversOK
  rw [Bool.and_eq_true, hgs, hhs]
  refine ⟨?_, ?_⟩
  · unfold allLt
    rw [CFSG.KS.Prim.all_iffP]
    intro i hi
    have hb := allN_spec h1 i hi
    rw [hgi i hi, Bool.or_eq_true]
    cases e : Nat.beq (G i) (pidn n w)
    · rw [e] at hb
      obtain ⟨j, hj, hf⟩ := anyN_spec hb
      refine Or.inr (anyLt_of_exists hj ?_)
      rw [hhi j hj]
      exact CFSG.KS.Prim.eqK_sound hf
    · obtain ⟨hn, hw, -, -⟩ := CFSG.KS.Prim.canon_facts (allN_spec hG i hi)
      refine Or.inl ?_
      rw [← CFSG.KS.Prim.unpack_pidn hn hw]
      exact CFSG.KS.Prim.eqK_sound e
  · unfold allLt
    rw [CFSG.KS.Prim.all_iffP]
    intro j hj
    obtain ⟨i, hi, hf⟩ := anyN_spec (allN_spec h2 j hj)
    refine anyLt_of_exists hi ?_
    rw [hhi j hj, hgi i hi]
    exact CFSG.KS.Prim.eqK_sound hf

end CFSG.KS.SporSch

end
