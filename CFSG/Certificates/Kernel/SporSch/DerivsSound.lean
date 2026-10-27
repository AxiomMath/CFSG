
module

public import Certificates.Data.Kernel.SporSch.Derivs
public import Certificates.Data.Kernel.Spor.Text
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.TextJoin
import CFSG.Certificates.Kernel.Spor.HexText
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.Schreier.Co3.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Text

private theorem lenW_eq : ∀ D : List (List Int), CFSG.KS.Mathieu.lenW D = D.length
  | [] => rfl
  | _ :: D => congrArg Nat.succ (lenW_eq D)

private theorem nthD_eq : ∀ (D : List (List Int)) (i : Nat),
    List.rec (motive := fun _ => Nat → List Int) (fun _ => [])
      (fun x _ ih i => Nat.rec (motive := fun _ => List Int) x (fun i' _ => ih i') i) D i =
      D.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: D, i + 1 => nthD_eq D i

theorem derivK_sound {k s : Nat} {D : List (List Int)} (h : derivK k s D = true) :
    CFSG.Sporadic.Schreier.Co3.Native.wordsOK k s D = true := by
  unfold derivK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hlen : D.length + k = s := by
    have := Nat.eq_of_beq_eq_true h1
    rwa [Nat.add_eq, lenW_eq] at this
  unfold CFSG.Sporadic.Schreier.Co3.Native.wordsOK
  rw [Bool.and_eq_true]
  refine ⟨by simpa using hlen, ?_⟩
  unfold CFSG.Monster.B.Co2.Native.allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨j, hj⟩ _
  have hj' := allN_spec h2 j hj
  by_cases hjk : j < k
  · simp [hjk]
  · have hb : Nat.blt j k = false := by
      cases e : Nat.blt j k
      · rfl
      · exact absurd (Nat.blt_eq.mp e) hjk
    rw [hb] at hj'
    change lettersK j (dword D k j) = true at hj'
    have hd : dword D k j = D.getD (j - k) [] := by
      unfold dword
      rw [hb]
      exact nthD_eq D (Nat.sub j k)
    rw [hd] at hj'
    have hw : (wordsArr k s D)[j]! = D.getD (j - k) [] := by
      rw [wordsArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
      simp only [hjk, ↓reduceIte]
    simp only [hjk, decide_false, Bool.false_or]
    rw [hw]
    exact CFSG.KS.Prim.lettersK_sound hj'

open CFSG.KS.HexText CFSG.KS.PackFld

private theorem walk {wd n w lines start cnt : Nat} {F : Nat → Nat} (hwd : 0 < wd) :
    ∀ (A : List Char) (L e t v acc Q : Nat), Q = L * (wd * n + 1) + wd * e + t →
      (e < n ∧ t < wd ∨ e = n ∧ t = 0) →
      run wd n w lines start cnt F A L e t v acc = true →
      A.length + Q = lines * (wd * n + 1) ∧ (∀ k < A.length, (A[k]!).toNat < 128) ∧
      ∀ L', L ≤ L' → L' < lines → (A[L' * (wd * n + 1) + wd * n - Q]!).toNat = 10
  | [], L, e, t, v, acc, Q, hQ, _, h => by
    change nilC lines L e t v acc = true at h
    unfold nilC at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    have e1 := Nat.eq_of_beq_eq_true h1
    have e2 := Nat.eq_of_beq_eq_true h2
    have e3 := Nat.eq_of_beq_eq_true h3
    subst e1 e2 e3
    refine ⟨by simp [hQ], fun k hk => absurd hk (by simp), fun L' h1 h2 => by omega⟩
  | ch :: A, L, e, t, v, acc, Q, hQ, hs, h => by
    change stepC wd n w start cnt F ch A (run wd n w lines start cnt F A) L e t v acc = true at h
    have hle : wd * e + t ≤ wd * n := by
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := Nat.mul_le_mul_left wd (Nat.succ_le_of_lt h1)
        rw [Nat.mul_succ] at this
        omega
      · subst h1 h2
        omega
    cases hb : Nat.blt e n
    · have hen : e = n ∧ t = 0 := by
        rcases hs with ⟨h1, _⟩ | h1
        · exact absurd (Nat.blt_eq.mpr h1) (by rw [hb]; decide)
        · exact h1
      obtain ⟨he, ht0⟩ := hen
      rw [he, ht0] at hQ
      cases hn : Nat.beq (Char.toNat ch) 10
      · rw [stepC_bad1 hb hn] at h
        exact false_ne h
      rw [stepC_nl hb hn] at h
      have hc : Char.toNat ch = 10 := Nat.eq_of_beq_eq_true hn
      have hQ' : Q + 1 = (L + 1) * (wd * n + 1) + wd * 0 + 0 := by
        rw [Nat.succ_mul]
        omega
      obtain ⟨a, b, c⟩ := walk hwd A (L + 1) 0 0 0 0 (Q + 1) hQ'
        (by omega)
        ((bAnd_iff _ _).1 h).2
      refine ⟨by simp; omega, fun k hk => ?_, fun L' h1 h2 => ?_⟩
      · cases k with
        | zero => simp [hc]
        | succ k => simpa using b k (by simpa using hk)
      · rcases Nat.lt_or_ge L L' with hl | hl
        · have hm : L' * (wd * n + 1) + wd * n - Q =
              (L' * (wd * n + 1) + wd * n - (Q + 1)) + 1 := by
            have : (L + 1) * (wd * n + 1) ≤ L' * (wd * n + 1) := Nat.mul_le_mul_right _ hl
            rw [Nat.succ_mul] at this
            omega
          rw [hm]
          simpa using c L' hl h2
        · have : L' = L := by omega
          subst this
          have hm : L' * (wd * n + 1) + wd * n - Q = 0 := by omega
          rw [hm]
          simp [hc]
    · have hen : e < n ∧ t < wd := by
        rcases hs with h1 | ⟨h1, _⟩
        · exact h1
        · exact absurd (Nat.blt_eq.mp hb) (by omega)
      cases hh : Nat.blt (hexV (Char.toNat ch)) 16
      · rw [stepC_bad2 hb hh] at h
        exact false_ne h
      have hasc : ch.toNat < 128 := by
        rcases hexV_dig (Nat.blt_eq.mp hh) with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
      have key : ∀ e' t' v' acc', Q + 1 = L * (wd * n + 1) + wd * e' + t' →
          (e' < n ∧ t' < wd ∨ e' = n ∧ t' = 0) →
          run wd n w lines start cnt F A L e' t' v' acc' = true →
          (ch :: A).length + Q = lines * (wd * n + 1) ∧
            (∀ k < (ch :: A).length, ((ch :: A)[k]!).toNat < 128) ∧
            ∀ L', L ≤ L' → L' < lines →
              ((ch :: A)[L' * (wd * n + 1) + wd * n - Q]!).toNat = 10 := by
        intro e' t' v' acc' hQ' hs' hr
        obtain ⟨a, b, c⟩ := walk hwd A L e' t' v' acc' (Q + 1) hQ' hs' hr
        refine ⟨by simp; omega, fun k hk => ?_, fun L' h1 h2 => ?_⟩
        · cases k with
          | zero => simpa using hasc
          | succ k => simpa using b k (by simpa using hk)
        · have hm : L' * (wd * n + 1) + wd * n - Q =
              (L' * (wd * n + 1) + wd * n - (Q + 1)) + 1 := by
            have : L * (wd * n + 1) ≤ L' * (wd * n + 1) := Nat.mul_le_mul_right _ h1
            have : wd * e + t < wd * n := by
              have := Nat.mul_le_mul_left wd (Nat.succ_le_of_lt hen.1)
              rw [Nat.mul_succ] at this
              omega
            omega
          rw [hm]
          simpa using c L' h1 h2
      cases ht : Nat.beq (Nat.succ t) wd
      · rw [stepC_dig hb hh ht] at h
        have := false_of_beq ht
        exact key e (t + 1) _ acc (by omega) (Or.inl ⟨hen.1, by omega⟩) h
      · have ht' : t + 1 = wd := Nat.eq_of_beq_eq_true ht
        cases hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w)
        · rw [stepC_bad3 hb hh ht hv] at h
          exact false_ne h
        rw [stepC_ent hb hh ht hv] at h
        refine key (e + 1) 0 0 _ (by rw [Nat.mul_succ wd e]; omega) ?_ h
        rcases Nat.lt_or_ge (e + 1) n with h1 | h1
        · exact Or.inl ⟨h1, hwd⟩
        · exact Or.inr ⟨by omega, rfl⟩

private theorem utf8_size_ascii : ∀ cs : List Char,
    (∀ k < cs.length, (cs[k]!).toNat < 128) → cs.utf8Encode.size = cs.length
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c.toNat < 128 := by simpa using h 0 (by simp)
    rw [List.utf8Encode_cons, utf8_single hc, ByteArray.size_append,
      utf8_size_ascii cs (fun k hk => by simpa using h (k + 1) (by simp; omega))]
    simp
    omega

theorem hexBind_layout {cs : List Char} {wd n w lines start cnt : Nat} {F : Nat → Nat}
    (h : CFSG.KS.Text.hexBind cs wd n w lines start cnt F = true) {w' n' : Nat}
    (he : w' * n' = wd * n) :
    layoutOK (String.ofList cs).toUTF8 w' n' lines = true := by
  unfold hexBind at h
  obtain ⟨hwd, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨_, hr⟩ := (bAnd_iff _ _).1 h2
  have hwd' := Nat.blt_eq.mp hwd
  obtain ⟨hlen, hasc, hnl⟩ := walk hwd' cs 0 0 0 0 0 0 (by simp)
    (by omega) hr
  have hb : (String.ofList cs).toUTF8 = cs.utf8Encode := by
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  have hsz : (String.ofList cs).toUTF8.size = cs.length := by
    rw [hb]
    exact utf8_size_ascii cs hasc
  unfold layoutOK
  rw [he, Bool.and_eq_true]
  refine ⟨by rw [hsz]; simpa using hlen, ?_⟩
  unfold CFSG.Monster.B.Co2.Native.allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨L, hL⟩ _
  have hpos : L * (wd * n + 1) + wd * n < cs.length := by
    have : (L + 1) * (wd * n + 1) ≤ lines * (wd * n + 1) := Nat.mul_le_mul_right _ hL
    rw [Nat.succ_mul] at this
    omega
  have hc := hnl L (Nat.zero_le L) hL
  rw [Nat.sub_zero] at hc
  rw [hb]
  dsimp only
  rw [utf8_get cs cs.length (fun k hk => ⟨hk, hasc k hk⟩) _ hpos, hc]
  rfl

end CFSG.KS.SporSch

end
