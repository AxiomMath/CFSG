module

public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import Certificates.Data.Item434SporGenJ2HSMcL
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Item434

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
open CFSG.KC.B3S3K (cm pw cj)
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

@[expose] def Pk (n w : ℕ) (a : Array ℕ) (p : ℕ) : Prop := a = unpack n w p ∧ permB n w p = true

theorem allLt_eq_allN (m : ℕ) {f g : ℕ → Bool} (h : ∀ i < m, f i = g i) : allLt m f = allN m g :=
  Bool.eq_iff_iff.2 ⟨fun hf => CFSG.KS.Raw.Orb.allN_iff.2 fun i hi =>
      (h i hi) ▸ CFSG.Monster.B.Co2.allLt_iff.1 hf i hi,
    fun hg => CFSG.Monster.B.Co2.allLt_iff.2 fun i hi =>
      (h i hi).symm ▸ CFSG.KS.Raw.Orb.allN_iff.1 hg i hi⟩

theorem allLt_of_allN {m : ℕ} {f g : ℕ → Bool} (h : allN m g = true)
    (hfg : ∀ i < m, g i = true → f i = true) : allLt m f = true :=
  CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => hfg i hi (CFSG.KS.Raw.Orb.allN_iff.1 h i hi)

theorem any_range_of{m : ℕ} {f : ℕ → Bool} (i : ℕ) (hi : i < m) (h : f i = true) :
    (List.range m).any f = true :=
  List.any_eq_true.2 ⟨i, List.mem_range.2 hi, h⟩

theorem powN_eq_powArr (n : ℕ) (t : Array ℕ) :
    ∀ k, powN n t k = CFSG.Monster.B.Mathieu.powArr n t k
  | 0 => rfl
  | k + 1 => by rw [powN, CFSG.Monster.B.Mathieu.powArr, powN_eq_powArr n t k]

section Ops

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem pk_unpack {p : ℕ} (hp : permB n w p = true) : Pk n w (unpack n w p) p := ⟨rfl, hp⟩

theorem pk_id : Pk n w (idA n) (pidn n w) :=
  ⟨CFSG.KC.BfsPin.idA_eq hw, CFSG.KC.B3S3K.permB_id hw⟩

theorem pk_comp {a b : Array ℕ} {p q : ℕ} (ha : Pk n w a p) (hb : Pk n w b q) :
    Pk n w (compA n a b) (cm n w p q) := by
  obtain ⟨rfl, hp⟩ := ha
  obtain ⟨rfl, hq⟩ := hb
  exact ⟨comp_unpack hw hp hq, permB_pcomp hw hp hq⟩

theorem pk_inv {a : Array ℕ} {p : ℕ} (ha : Pk n w a p) :
    Pk n w (invCand n a) (pinvS n w (mask w) p) := by
  obtain ⟨rfl, hp⟩ := ha
  exact ⟨inv_unpack hw hp, permB_pinvS hw hp⟩

theorem pk_powArr {a : Array ℕ} {p : ℕ} (ha : Pk n w a p) (k : ℕ) :
    Pk n w (CFSG.Monster.B.Mathieu.powArr n a k) (pw n w p k) := by
  obtain ⟨rfl, hp⟩ := ha
  exact ⟨pow_unpack hw hp k, permB_ppow hw hp k⟩

theorem pk_powN {a : Array ℕ} {p : ℕ} (ha : Pk n w a p) (k : ℕ) :
    Pk n w (powN n a k) (pw n w p k) := by
  rw [powN_eq_powArr]
  exact pk_powArr hw ha k

theorem pk_conjN {a b : Array ℕ} {p q : ℕ} (ha : Pk n w a p) (hb : Pk n w b q) :
    Pk n w (conjN n a b) (cm n w (cm n w p q) (pinvS n w (mask w) p)) :=
  pk_comp hw (pk_comp hw ha hb) (pk_inv hw ha)

theorem pk_conjA {a b : Array ℕ} {p q : ℕ} (ha : Pk n w a p) (hb : Pk n w b q) :
    Pk n w (CFSG.RankThree.Native.conjA n a b) (cm n w p (cm n w q (pinvS n w (mask w) p))) :=
  pk_comp hw ha (pk_comp hw hb (pk_inv hw ha))

theorem pk_commutatorA {a b : Array ℕ} {p q : ℕ} (ha : Pk n w a p) (hb : Pk n w b q) :
    Pk n w (CFSG.RankThree.Native.commutatorA n a b)
      (cm n w (cm n w p q) (cm n w (pinvS n w (mask w) p) (pinvS n w (mask w) q))) :=
  pk_comp hw (pk_comp hw ha hb) (pk_comp hw (pk_inv hw ha) (pk_inv hw hb))

theorem eqA_pk {a b : Array ℕ} {p q : ℕ} (ha : Pk n w a p) (hb : Pk n w b q) :
    eqA n a b = Nat.beq p q := by
  obtain ⟨rfl, hp⟩ := ha
  obtain ⟨rfl, hq⟩ := hb
  exact eqA_unpack hw hp hq

theorem commN_pk {a b : Array ℕ} {p q : ℕ} (ha : Pk n w a p) (hb : Pk n w b q) :
    commN n a b = Nat.beq (cm n w p q) (cm n w q p) :=
  eqA_pk hw (pk_comp hw ha hb) (pk_comp hw hb ha)

omit hw in
theorem isInvA_pk {a : Array ℕ} {p : ℕ} (ha : Pk n w a p) : isInvA n a (invCand n a) = true := by
  obtain ⟨rfl, hp⟩ := ha
  exact CFSG.KC.B3S3K.validA_of hp

theorem e9Check_pk {a b : Array ℕ} {p q : ℕ} (ha : Pk n w a p) (hb : Pk n w b q) :
    e9Check n a b = (Nat.beq (pw n w p 3) (pidn n w) && Nat.beq (pw n w q 3) (pidn n w) &&
      Nat.beq (cm n w p q) (cm n w q p) && !Nat.beq p (pidn n w) && !Nat.beq q (pidn n w) &&
      !Nat.beq q p && !Nat.beq q (pw n w p 2)) := by
  unfold e9Check
  rw [isInvA_pk ha, isInvA_pk hb, eqA_pk hw (pk_powN hw ha 3) (pk_id hw),
    eqA_pk hw (pk_powN hw hb 3) (pk_id hw), commN_pk hw ha hb, eqA_pk hw ha (pk_id hw),
    eqA_pk hw hb (pk_id hw), eqA_pk hw hb ha, eqA_pk hw hb (pk_powN hw ha 2)]
  simp only [Bool.true_and]

theorem sigCheck_pk {σ : Array (Array ℕ)} {F : ℕ → ℕ} (hσ : ∀ i < σ.size, Pk n w σ[i]! (F i))
    (ords : List ℕ) (ps : List (ℕ × ℕ)) {a b : Array ℕ} {p q : ℕ} (ha : Pk n w a p)
    (hb : Pk n w b q) :
    sigCheck n σ ords ps a b = allN σ.size (fun i =>
      Nat.beq (pw n w (F i) (ords.getD i 0)) (pidn n w) && !(ords.getD i 0 % 3 == 0) &&
        Nat.beq (cm n w (F i) (cm n w (pw n w p (ps.getD i (0, 0)).1) (pw n w q (ps.getD i (0, 0)).2)))
          (cm n w (cm n w (pw n w p (ps.getD i (0, 0)).1) (pw n w q (ps.getD i (0, 0)).2)) (F i)) &&
        !Nat.beq (cm n w (pw n w p (ps.getD i (0, 0)).1) (pw n w q (ps.getD i (0, 0)).2))
          (pidn n w)) := by
  unfold sigCheck
  apply allLt_eq_allN
  intro i hi
  have hP := pk_comp hw (pk_powN hw ha (ps.getD i (0, 0)).1) (pk_powN hw hb (ps.getD i (0, 0)).2)
  unfold pN
  rw [eqA_pk hw (pk_powN hw (hσ i hi) _) (pk_id hw), commN_pk hw (hσ i hi) hP,
    eqA_pk hw hP (pk_id hw)]

end Ops

end CFSG.KC.Item434

end
