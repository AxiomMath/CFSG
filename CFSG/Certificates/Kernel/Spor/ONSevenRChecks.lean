module

public import CFSG.Certificates.Kernel.B3S3KSound
import CFSG.Sporadic.Schreier.ONPermArr
public import CFSG.RankThree.Native.ONSevenArrays
public import Certificates.Data.Kernel.ONSevenR

public section

namespace CFSG.KS.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K
  CFSG.KC.BfsPin CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
open CFSG.Monster.B.Co2 (allLt_iff)

section

theorem bIf_true {c a b : Bool} (hc : c = true) (h : Bool.rec (motive := fun _ => Bool) b a c = true) :
    a = true := by
  subst hc
  exact h

theorem bIf_false {c a b : Bool} (hc : c = false)
    (h : Bool.rec (motive := fun _ => Bool) b a c = true) : b = true := by
  subst hc
  exact h

variable {n w : Nat} (hw : szOK n w = true)
include hw

theorem perm_pts {ng N : Nat} {G T E S : Nat → Nat} (hp : ∀ k < ng, permB n w (G k) = true)
    (hk : bfsK n w ng G N T E S = true) : ∀ i < N, permB n w (T i) = true :=
  (bfsK_points (fun y => permB n w y = true) (permB_id hw)
    (fun _ hy k hk' => permB_pcomp hw (hp k hk') hy) hk).2.2.1

omit hw in
theorem ppow_succ (X e : Nat) : ppow n w (mask w) (pidn n w) X (e + 1) =
    pcomp n w (mask w) X (ppow n w (mask w) (pidn n w) X e) := by
  change strictN (ppow n w (mask w) (pidn n w) X e) (fun q => pcomp n w (mask w) X q) = _
  generalize ppow n w (mask w) (pidn n w) X e = y
  cases y <;> rfl

omit hw in
theorem pows_spec {X o : Nat} {P : Nat → Nat} (h : powsK n w X P o = true) :
    permB n w X = true ∧ ∀ e ≤ o, P e = ppow n w (mask w) (pidn n w) X e := by
  unfold powsK at h
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun e he => ?_⟩
  induction e with
  | zero => exact Nat.eq_of_beq_eq_true h2
  | succ e ih =>
    rw [ppow_succ, ← ih (by omega)]
    exact Nat.eq_of_beq_eq_true (allN_spec h3 e (by omega))

theorem powArr_pows {X o : Nat} {P : Nat → Nat} (h : powsK n w X P o = true) {e : Nat}
    (he : e ≤ o) : powArr n (unpack n w X) e = unpack n w (P e) := by
  rw [pow_unpack' hw (pows_spec h).1, (pows_spec h).2 e he]

theorem permB_pows {X o : Nat} {P : Nat → Nat} (h : powsK n w X P o = true) {e : Nat}
    (he : e ≤ o) : permB n w (P e) = true := by
  rw [(pows_spec h).2 e he]
  exact permB_ppow hw (pows_spec h).1 e

theorem qcheck_of {R : Array Nat} {ts lt : Array (Array Nat)} {c : ArrCert} {T PL : Nat → Nat}
    (hR : R.size = n) (hres : onSevenResOK R (onSevenQArrs ++ onSevenLineArrs) = true)
    (he : enumOK n ts onSevenKeys c = true) (hN : c.pts.size = 343)
    (hT : ∀ i < 343, c.pts[i]! = unpack n w (T i)) (hTp : ∀ i < 343, permB n w (T i) = true)
    (hl : BindA n w lt 57 fun j => PL (8 * j + 1)) (hq : qK n w T PL = true) :
    onSevenQCheck R ts lt c = true := by
  unfold qK at hq
  simp only [bAnd_iff] at hq
  obtain ⟨hP, hpow, hcov, hdist, hlin⟩ := hq
  have hPs : ∀ j < 57, powsK n w (PL (8 * j + 1)) (fun e => PL (8 * j + e)) 7 = true :=
    fun j hj => allN_spec hP j hj
  have hpw : ∀ j < 57, ∀ e ≤ 7, powArr n lt[j]! e = unpack n w (PL (8 * j + e)) := by
    intro j hj e hle
    rw [hl.2 j hj]
    exact powArr_pows hw (hPs j hj) hle
  have hpp : ∀ j < 57, ∀ e ≤ 7, permB n w (PL (8 * j + e)) = true :=
    fun j hj e hle => permB_pows hw (hPs j hj) hle
  unfold onSevenQCheck
  rw [hR]
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨hres, he⟩, hN⟩, hl.1⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun j hj => ?_⟩,
    fun j hj => ?_⟩
  · rw [hT k hk, powEq_id hw (hTp k hk)]
    exact allN_spec hpow k hk
  · have h := allN_spec hcov k hk
    rw [hT k hk, eqA_id hw (hTp k hk)]
    revert h
    cases hb : Nat.beq (T k) (pidn n w)
    · intro h
      change CFSG.KC.LQT.P.anyN 57 _ = true at h
      rw [anyNP_eq] at h
      rw [Bool.false_or, ← h]
      apply any_range_congr
      intro j hj
      rw [anyNP_eq]
      apply any_range_congr
      intro e he
      rw [hpw j hj e (by omega), eqA_unpack' hw (hTp k hk) (hpp j hj e (by omega))]
      rfl
    · intro _
      rfl
  · intro j' hj'
    have h := allN_spec (allN_spec hdist j hj) j' hj'
    by_cases ejj : j = j'
    · subst ejj
      simp
    · have hb : Nat.beq j j' = false :=
        Bool.eq_false_iff.2 fun e => ejj (Nat.eq_of_beq_eq_true e)
      have h' := bIf_false hb h
      rw [beq_eq_false_iff_ne.2 ejj, Bool.false_or, allLt_iff]
      intro e he
      have h2 := allN_spec h' e he
      rw [hpw j' hj' e (by omega), hl.2 j hj,
        eqA_unpack' hw (hpp j hj 1 (by omega)) (hpp j' hj' e (by omega))]
      exact h2
  · have h := allN_spec hlin j hj
    simp only [bAnd_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hX := hpp j hj 1 (by omega)
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hl.2 j hj]
      exact validA_of hX
    · rw [hpw j hj 7 (by omega), eqA_id hw (hpp j hj 7 (by omega))]
      exact h1
    · rw [hl.2 j hj, eqA_id hw hX]
      exact h2
    · rw [hl.2 j hj, any_eqA_unpack' hw hN hT hTp hX]
      exact h3

omit hw in
theorem ccheck_of {R x : Array Nat} {cs ts : Array (Array Nat)} {c : ArrCert} {sz : Nat}
    (hres : onSevenResOK R (cs.push x) = true)
    (hcomm : ∀ k < cs.size, peq nPts (pcomp nPts cs[k]! x) (pcomp nPts x cs[k]!) = true)
    (he : enumOK R.size ts onSevenKeys c = true) (hN : c.pts.size = sz) :
    onSevenCCheck R x cs ts c sz = true := by
  unfold onSevenCCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨hres, CFSG.ONSchreier.allBelowN_iff.2 hcomm⟩, he⟩, hN⟩

theorem fcheck_of {R tx : Array Nat} {ts fs tf : Array (Array Nat)} {cC cF : ArrCert}
    {nC ng nfg : Nat} {TC TF G FG PX : Nat → Nat} (hR : R.size = n)
    (hres : onSevenResOK R fs = true) (he : enumOK n tf onSevenKeys cF = true)
    (hNF : cF.pts.size = 343) (hTF : ∀ i < 343, cF.pts[i]! = unpack n w (TF i))
    (hTFp : ∀ i < 343, permB n w (TF i) = true)
    (hNC : cC.pts.size = nC) (hTC : ∀ i < nC, cC.pts[i]! = unpack n w (TC i))
    (hTCp : ∀ i < nC, permB n w (TC i) = true)
    (hts : BindA n w ts ng G) (hGp : ∀ k < ng, permB n w (G k) = true)
    (htf : BindA n w tf nfg FG) (hFp : ∀ l < nfg, permB n w (FG l) = true)
    (hx : tx = unpack n w (PX 1)) (hpx : powsK n w (PX 1) PX 7 = true)
    (hf : fK n nC 343 w ng nfg TC TF G FG PX = true) :
    onSevenFCheck R ts cC fs tf tx cF = true := by
  unfold fK at hf
  simp only [bAnd_iff] at hf
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hX := permB_pows hw hpx (e := 1) (by omega)
  unfold onSevenFCheck
  rw [hR]
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨⟨hres, he⟩, hNF⟩, fun l hl => ?_⟩, fun k hk l hl => ?_⟩, ?_⟩, fun k hk => ?_⟩
  · rw [htf.1] at hl
    rw [htf.2 l hl, any_eqA_unpack' hw hNC hTC hTCp (hFp l hl)]
    exact allN_spec h1 l hl
  · rw [hts.1] at hk
    rw [htf.1] at hl
    rw [hts.2 k hk, htf.2 l hl, conj_unpack' hw (hGp k hk) (hFp l hl),
      any_eqA_unpack' hw hNF hTF hTFp
        (permB_pcomp hw (hGp k hk) (permB_pcomp hw (hFp l hl) (permB_pinvS hw (hGp k hk))))]
    exact allN_spec (allN_spec h2 k hk) l hl
  · rw [hx, any_eqA_unpack' hw hNF hTF hTFp hX]
    exact h3
  · rw [hNC] at hk
    have h := allN_spec h4 k hk
    have hc : (allLt tf.size fun l => commA n cC.pts[k]! tf[l]!) =
        allN nfg (fun l => Nat.beq (pcomp n w (mask w) (TC k) (FG l))
          (pcomp n w (mask w) (FG l) (TC k))) := by
      rw [Bool.eq_iff_iff, allLt_iff, htf.1]
      constructor
      · intro hall
        refine allN_intro fun l hl => ?_
        have := hall l hl
        unfold commA at this
        rwa [hTC k hk, htf.2 l hl, comp_unpack' hw (hTCp k hk) (hFp l hl),
          comp_unpack' hw (hFp l hl) (hTCp k hk),
          eqA_unpack' hw (permB_pcomp hw (hTCp k hk) (hFp l hl))
            (permB_pcomp hw (hFp l hl) (hTCp k hk))] at this
      · intro hall l hl
        unfold commA
        rw [hTC k hk, htf.2 l hl, comp_unpack' hw (hTCp k hk) (hFp l hl),
          comp_unpack' hw (hFp l hl) (hTCp k hk),
          eqA_unpack' hw (permB_pcomp hw (hTCp k hk) (hFp l hl))
            (permB_pcomp hw (hFp l hl) (hTCp k hk))]
        exact allN_spec hall l hl
    rw [hc]
    cases hb : allN nfg (fun l => Nat.beq (pcomp n w (mask w) (TC k) (FG l))
        (pcomp n w (mask w) (FG l) (TC k)))
    · rfl
    · have h := bIf_true hb h
      rw [anyNP_eq] at h
      rw [Bool.not_true, Bool.false_or, ← h]
      apply any_range_congr
      intro e he
      rw [hx, powArr_pows hw hpx (by omega), hTC k hk,
        eqA_unpack' hw (hTCp k hk) (permB_pows hw hpx (by omega))]

end

end CFSG.KS.ONR

end
