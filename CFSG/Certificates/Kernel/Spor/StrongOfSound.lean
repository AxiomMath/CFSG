module

public import Certificates.Data.CFSGNative.YGroups.ExactCheck
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

private theorem strongOf_nil (n : Nat) (S : Array (Array Nat)) :
    (CFSG.YGroups.ModelNative.strongOf n S ([] : List (List Int)).toArray).1 = S := by
  simp [CFSG.YGroups.ModelNative.strongOf]

private theorem strongOf_cons (n : Nat) (S : Array (Array Nat)) (wd : List Int)
    (ws : List (List Int)) :
    CFSG.YGroups.ModelNative.strongOf n S (wd :: ws).toArray =
      CFSG.YGroups.ModelNative.strongOf n (S.push (wordA n S (rawInvs n S) wd)) ws.toArray := by
  simp [CFSG.YGroups.ModelNative.strongOf, rawInvs, Array.map_push]

private theorem lenW_eq : ∀ D : List (List Int), CFSG.KS.Mathieu.lenW D = D.length
  | [] => rfl
  | _ :: D => congrArg Nat.succ (lenW_eq D)

private theorem wordA_size (n : Nat) (S Sinv : Array (Array Nat)) (wd : List Int) :
    (wordA n S Sinv wd).size = n := by
  cases wd <;> simp [wordA, idA, compA]

private theorem unpack_size (n w P : Nat) : (unpack n w P).size = n := by
  simp [unpack]

private theorem arr_eq_of_rep {n : Nat} {t u : Array Nat} {g : Equiv.Perm (Fin n)}
    (ht : t.size = n) (hu : u.size = n) (hgt : CFSG.Monster.B.Co2.Rep n t g)
    (hgu : CFSG.Monster.B.Co2.Rep n u g) : t = u := by
  apply Array.ext
  · rw [ht, hu]
  · intro i h1 h2
    have hi : i < n := by rwa [ht] at h1
    rw [← getElem!_pos t i h1, ← getElem!_pos u i h2, hgt.apply hi, hgu.apply hi]

theorem strongOf_bind {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {O : Array (Array Nat)}
    {D : List (List Int)} (hO : O.size = kO ∧ ∀ j < kO, O[j]! = unpack n w (PS j))
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    (CFSG.YGroups.ModelNative.strongOf n O D.toArray).1.size = kS ∧
      ∀ j < kS, (CFSG.YGroups.ModelNative.strongOf n O D.toArray).1[j]! = unpack n w (PS j) := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨hsz, -, -, hlen, hperm, hder, -, -⟩ := hh
  unfold szOK at hsz
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hsz
  have hn24 : n < 16777216 := hsz.1
  have hw : n + 1 < 2 ^ w := by
    have := hsz.2
    have e : Nat.shiftLeft 1 w = 1 <<< w := rfl
    rwa [e, Nat.shiftLeft_eq, Nat.one_mul] at this
  have hlen' : D.length + kO = kS := by
    have := Nat.eq_of_beq_eq_true hlen
    have e : Nat.add (CFSG.KS.Mathieu.lenW D) kO = CFSG.KS.Mathieu.lenW D + kO := rfl
    rwa [e, lenW_eq] at this
  have hrep : ∀ h < kS, CFSG.Monster.B.Co2.Rep n (unpack n w (PS h))
      (CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h))) ∧
      CFSG.Monster.B.Co2.Rep n (unpack n w (PSI h))
        (CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h)))⁻¹ := fun h hh =>
    CFSG.Monster.B.Co2.rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 hperm h hh))
  have key : ∀ (ws : List (List Int)) (S : Array (Array Nat)), kO ≤ S.size →
      S.size + ws.length = kS → (∀ h < S.size, S[h]! = unpack n w (PS h)) →
      (∀ i (hi : i < ws.length), ws[i] = D.getD (S.size - kO + i) []) →
      (CFSG.YGroups.ModelNative.strongOf n S ws.toArray).1.size = kS ∧
        ∀ j < kS, (CFSG.YGroups.ModelNative.strongOf n S ws.toArray).1[j]! =
          unpack n w (PS j) := by
    intro ws
    induction ws with
    | nil =>
      intro S _ hk hSe _
      simp only [List.length_nil, Nat.add_zero] at hk
      rw [strongOf_nil]
      exact ⟨hk, fun j hj => hSe j (by omega)⟩
    | cons wd ws ih =>
      intro S hkO hk hSe hws
      simp only [List.length_cons] at hk
      set k := S.size with hkdef
      have hkS : k < kS := by omega
      have hwd : wd = D.getD (k - kO) [] := by
        have := hws 0 (by simp)
        rwa [List.getElem_cons_zero, Nat.add_zero] at this
      have hX : wordA n S (rawInvs n S) wd = unpack n w (PS k) := by
        have hd := Orb.allN_iff.1 hder k hkS
        rw [Orb.bIf_eq, ite_eq_right (by rw [Orb.blt_dec]; simpa using hkO), Orb.strictB_eq,
          Bool.and_eq_true, Orb.beq_dec, decide_eq_true_iff, Orb.dword_eq hkO, ← hwd] at hd
        obtain ⟨hl, he⟩ := hd
        obtain ⟨hP, hlo⟩ := Orb.prep_wordK
          (gs := fun h => CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h))) (j := k) hn24 hw
          (fun h hh => Orb.prep_of_rep (hrep h (by omega)).1)
          (fun h hh => Orb.prep_of_rep (hrep h (by omega)).2) wd hl
        have hS' : ∀ h < k, CFSG.Monster.B.Co2.Rep n S[h]!
            (CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h))) := fun h hh => by
          rw [hSe h hh]
          exact (hrep h (by omega)).1
        have hSi : ∀ h < k, CFSG.Monster.B.Co2.Rep n (rawInvs n S)[h]!
            (CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h)))⁻¹ := fun h hh => by
          rw [Orb.rawInvs_get hh]
          exact rep_invCand (hS' h hh)
        have hrW := CFSG.Monster.B.Co2.rep_wordA hS' hSi wd hlo
        have hrP : CFSG.Monster.B.Co2.Rep n (unpack n w (PS k))
            (Quiver.SchreierGraph.evalWord
              (fun h : Fin k => CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h)))
              (CFSG.Monster.B.Co2.toLetters k wd)) := by
          rw [he]
          exact Orb.rep_unpack hP
        exact arr_eq_of_rep (wordA_size _ _ _ _) (unpack_size _ _ _) hrW hrP
      rw [strongOf_cons]
      refine ih _ (by simp; omega) (by simp; omega) (fun h hh => ?_) (fun i hi => ?_)
      · simp only [Array.size_push] at hh
        rw [getElem!_pos _ h (by simpa using hh)]
        rcases Nat.lt_or_ge h k with h1 | h1
        · rw [Array.getElem_push_lt h1, ← getElem!_pos S h h1]
          exact hSe h h1
        · have e : h = k := by omega
          subst e
          rw [Array.getElem_push_eq, hX]
      · have := hws (i + 1) (by simp; omega)
        rw [List.getElem_cons_succ] at this
        rw [this, Array.size_push]
        congr 1
        omega
  exact key D O (by omega) (by omega) (fun h hh => hO.2 h (by omega))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hO.1, hi])

end CFSG.KS.Raw

end
