module

public import CFSG.Certificates.Kernel.GMS78RuCzJBasic
public import Certificates.Data.GMS78RuCzRigidCheck

public section

namespace CFSG.KC.GMS.CzJ

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.GMS
open CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSporadicStandard.Fin76b.AutETable (mt ix tab ev)

variable {M : Array (Array Nat)} {inv : Array Nat} {c : ArrCert} {RW : Nat → Nat}
  {PAR LAB INV : Nat}

private theorem getD_lt {t : List Nat} (ht : ∀ x ∈ t, x < 2048) (i : Nat) : t.getD i 0 < 2048 := by
  have := fget11_lt (czPack t) i
  rwa [czPack_fget ht] at this

theorem letF_lt (I : TabI M inv c RW PAR LAB INV) {t : List Nat} (ht : ∀ x ∈ t, x < 2048)
    (l : Nat) : letF inv t l < 2048 := by
  unfold letF
  split
  · exact getD_lt ht _
  · exact I.inv_lt _

theorem letF_eq (I : TabI M inv c RW PAR LAB INV) {t : List Nat} (ht : ∀ x ∈ t, x < 2048)
    (l : Nat) : letF inv t l = czLet INV (czPack t) l := by
  show _ = Bool.rec (motive := fun _ => Nat) (fget INV (fget (czPack t) (l / 2) 11) 11)
    (fget (czPack t) (l / 2) 11) (Nat.beq (l % 2) 0)
  rw [czPack_fget ht]
  unfold letF
  cases hb : Nat.beq (l % 2) 0
  · have h : ¬ l % 2 = 0 := Nat.ne_of_beq_eq_false hb
    rw [if_neg h]
    exact I.inv_eq _ (getD_lt ht _)
  · have h : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
    rw [if_pos h]

private theorem foldl_lt (I : TabI M inv c RW PAR LAB INV) (t : List Nat) :
    ∀ (w : List Nat) (acc : Nat), acc < 2048 →
      w.foldl (fun acc i => mt M acc (letF inv t i)) acc < 2048
  | [], _, h => h
  | _ :: w, _, _ => foldl_lt I t w _ (I.mt_lt _ _)

theorem evW_lt (I : TabI M inv c RW PAR LAB INV) (t w : List Nat) : evW M inv t w < 2048 :=
  foldl_lt I t w 0 (by decide)

private theorem foldl_eq (I : TabI M inv c RW PAR LAB INV) {t : List Nat}
    (ht : ∀ x ∈ t, x < 2048) : ∀ (w : List Nat) (acc : Nat), acc < 2048 →
      w.foldl (fun acc i => mt M acc (letF inv t i)) acc =
        List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
          (fun l _ ih acc => strictN (czMt RW acc (czLet INV (czPack t) l)) ih) w acc
  | [], _, _ => rfl
  | l :: w, acc, h => by
    rw [List.foldl_cons]
    show _ = strictN (czMt RW acc (czLet INV (czPack t) l)) _
    rw [strictN_eq', ← letF_eq I ht l]
    have : mt M acc (letF inv t l) = czMt RW acc (letF inv t l) :=
      I.mt_eq _ h _ (letF_lt I ht l)
    rw [← this]
    exact foldl_eq I ht w _ (I.mt_lt _ _)

theorem evW_eq (I : TabI M inv c RW PAR LAB INV) {t : List Nat} (ht : ∀ x ∈ t, x < 2048)
    (w : List Nat) : evW M inv t w = czEv RW INV (czPack t) w :=
  foldl_eq I ht w 0 (by decide)

theorem relsHold_eq (I : TabI M inv c RW PAR LAB INV) {t : List Nat} (ht : ∀ x ∈ t, x < 2048)
    (rs : List (List Nat)) : relsHold M inv rs t = czRels RW INV (czPack t) rs := by
  unfold relsHold czRels
  apply Bool.eq_iff_iff.2
  rw [neAllL_iff, List.all_eq_true]
  simp only [evW_eq I ht, beq_iff_eq, Nat.beq_eq]

theorem homVal_lt (I : TabI M inv c RW PAR LAB INV) (t : List Nat) (f a : Nat) :
    homVal M c t f a < 2048 := by
  cases f with
  | zero => show 0 < 2048; decide
  | succ f =>
    unfold homVal
    split
    · decide
    · exact I.mt_lt _ _

private noncomputable def kHV (RW : Nat → Nat) (PAR LAB T : Nat) (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih a => Bool.rec (motive := fun _ => Nat)
      (czMt RW (fget T (fget LAB a 3) 11) (ih (fget PAR a 11))) 0 (Nat.beq a 0)) f

private theorem homVal_kHV (I : TabI M inv c RW PAR LAB INV) {t : List Nat}
    (ht : ∀ x ∈ t, x < 2048) : ∀ (f a : Nat), a < 2048 →
      homVal M c t f a = kHV RW PAR LAB (czPack t) f a
  | 0, _, _ => rfl
  | f + 1, a, ha => by
    show _ = Bool.rec (motive := fun _ => Nat)
      (czMt RW (fget (czPack t) (fget LAB a 3) 11) (kHV RW PAR LAB (czPack t) f (fget PAR a 11)))
      0 (Nat.beq a 0)
    unfold homVal
    cases hb : Nat.beq a 0
    · have h : ¬ a = 0 := Nat.ne_of_beq_eq_false hb
      rw [if_neg h, I.par_eq a ha, I.lab_eq a ha,
        I.mt_eq _ (getD_lt ht _) _ (homVal_lt I t _ _), homVal_kHV I ht f _ (fget11_lt _ _),
        czPack_fget ht]
      rfl
    · have h : a = 0 := Nat.eq_of_beq_eq_true hb
      rw [if_pos h]

theorem homVal_eq (I : TabI M inv c RW PAR LAB INV) {t : List Nat} (ht : ∀ x ∈ t, x < 2048)
    {a : Nat} (ha : a < 2048) : homVal M c t 2048 a = czHomVal RW PAR LAB (czPack t) a :=
  homVal_kHV I ht 2048 a ha

private theorem ix_tab {n a : Nat} {f : Nat → Nat} (ha : a < n) : ix (tab n f) a = f a := by
  simp [ix, tab, Array.getD, ha]

private theorem ix_tab_ge {n a : Nat} {f : Nat → Nat} (ha : ¬ a < n) : ix (tab n f) a = 0 := by
  simp [ix, tab, Array.getD, ha]

theorem ix_homTab (I : TabI M inv c RW PAR LAB INV) {t : List Nat} (ht : ∀ x ∈ t, x < 2048)
    {a : Nat} (ha : a < 2048) :
    ix (homTab 2048 M c t) a = fget (czHom RW PAR LAB (czPack t)) a 11 := by
  unfold homTab
  rw [ix_tab ha, homVal_eq I ht ha, czHom_fget _ I.par_lt a ha]

theorem ix_homTab_lt (I : TabI M inv c RW PAR LAB INV) (t : List Nat) (a : Nat) :
    ix (homTab 2048 M c t) a < 2048 := by
  unfold homTab
  by_cases ha : a < 2048
  · rw [ix_tab ha]; exact homVal_lt I t _ _
  · rw [ix_tab_ge ha]; decide

theorem czEvs_evW (I : TabI M inv c RW PAR LAB INV) {t : List Nat} (ht : ∀ x ∈ t, x < 2048)
    (ws : List (List Nat)) : czEvs RW INV (czPack t) ws = czPack (ws.map (evW M inv t)) := by
  have : czEv RW INV (czPack t) = evW M inv t := funext fun w => (evW_eq I ht w).symm
  rw [czEvs_eq, this]

end CFSG.KC.GMS.CzJ

end
