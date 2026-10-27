module

public import Certificates.Data.Kernel.PGrp
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Check
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack

public section

namespace CFSG.KC.PGrp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord)
open CFSG.Monster.B.Co2 (permOfArr eqA_iff)

section Words

variable {n w : ℕ} (hw : szOK n w = true)
include hw

private theorem posWord_go {gs : Array (Array ℕ)} {ng : ℕ} {G : ℕ → ℕ}
    (hg : ∀ l < ng, gs[l]! = unpack n w (G l)) (hp : ∀ l < ng, permB n w (G l) = true) :
    ∀ wd : List ℕ, (∀ l ∈ wd, l < ng) → ∀ (A : ℕ), PP n w A →
      wd.foldl (fun acc l => compA n acc gs[l]!) (unpack n w A) =
          unpack n w (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
            (fun l _ ih acc => strictN (pcomp n w (mask w) acc (G l)) ih) wd A) ∧
        PP n w (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
            (fun l _ ih acc => strictN (pcomp n w (mask w) acc (G l)) ih) wd A)
  | [], _, A, hA => ⟨rfl, hA⟩
  | l :: wd, hl, A, hA => by
    have hl0 : l < ng := hl l List.mem_cons_self
    have hGl := pp_of_permB hw (hp l hl0)
    have e : strictN (pcomp n w (mask w) A (G l))
        (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
          (fun l _ ih acc => strictN (pcomp n w (mask w) acc (G l)) ih) wd) =
        List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
          (fun l _ ih acc => strictN (pcomp n w (mask w) acc (G l)) ih) wd
          (pcomp n w (mask w) A (G l)) :=
      PF.strictN_eqP _ _
    change (wd.foldl (fun acc l => compA n acc gs[l]!) (compA n (unpack n w A) gs[l]!)) =
        unpack n w (strictN (pcomp n w (mask w) A (G l)) _) ∧
      PP n w (strictN (pcomp n w (mask w) A (G l)) _)
    rw [e, hg l hl0, compA_PP hA hGl]
    exact posWord_go hg hp wd (fun k hk => hl k (List.mem_cons_of_mem l hk)) _ (hA.mul hGl)

theorem posWord_unpack {gs : Array (Array ℕ)} {ng : ℕ} {G : ℕ → ℕ}
    (hg : ∀ l < ng, gs[l]! = unpack n w (G l)) (hp : ∀ l < ng, permB n w (G l) = true)
    {wd : List ℕ} (hl : ∀ l ∈ wd, l < ng) :
    posWord n gs wd = unpack n w (posWordK n w G wd) ∧ permB n w (posWordK n w G wd) = true := by
  have h := posWord_go hw hg hp wd hl (pidn n w) (PP.id hw)
  rw [← idA_eq hw] at h
  exact ⟨h.1, permB_of_pp h.2⟩

end Words

theorem keyK_pcomp {n w : ℕ} (hn : n < 2 ^ 32) (p q : ℕ) :
    ∀ {ps : List ℕ}, (∀ x ∈ ps, x < n) →
      BfsPin.keyK n w ps (pcomp n w (mask w) p q) = keyCK n w ps p q
  | [], _ => rfl
  | x :: ps, hps => by
    change Nat.add (pg w (mask w) (pcomp n w (mask w) p q) x)
        (Nat.mul n (BfsPin.keyK n w ps (pcomp n w (mask w) p q))) =
      Nat.add (pg w (mask w) p (pg w (mask w) q x)) (Nat.mul n (keyCK n w ps p q))
    rw [PF.pg_pcomp hn (hps x List.mem_cons_self),
      keyK_pcomp hn p q fun y hy => hps y (List.mem_cons_of_mem x hy)]

theorem eqA_iff_keyA {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (h : enumOK n gs ps c = true) {a b : Array ℕ}
    (ha : validA n a = true) (hb : validA n b = true)
    (hma : permOfArr n a ∈ Subgroup.closure (permsA n gs))
    (hmb : permOfArr n b ∈ Subgroup.closure (permsA n gs)) :
    eqA n a b = Nat.beq (keyA n ps a) (keyA n ps b) := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps h
  have hc : arrCertOK (leftA n gs) gs.size (validA n) (keyA n ps) (idA n) c = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.2
  apply Bool.eq_iff_iff.2
  rw [eqA_iff (rep_of_validA ha) (rep_of_validA hb)]
  constructor
  · intro e
    rw [keyA_eq hps ha hb e]
    exact Nat.beq_refl _
  · intro e
    have e' := Nat.eq_of_beq_eq_true e
    obtain ⟨i, hi, hia⟩ := (hmem _).1 hma
    obtain ⟨j, hj, hjb⟩ := (hmem _).1 hmb
    have ki : keyA n ps c.pts[i]! = keyA n ps a := keyA_eq hps (hval i hi) ha hia
    have kj : keyA n ps c.pts[j]! = keyA n ps b := keyA_eq hps (hval j hj) hb hjb
    have hij : i = j := arrCertOK_keys_inj hc hi hj (by rw [ki, kj, e'])
    subst hij
    rw [← hia, hjb]

theorem beq_iff_keyK {n w : ℕ} (hw : szOK n w = true) {gs : Array (Array ℕ)} {ps : List ℕ}
    {c : ArrCert} (hps : ∀ p ∈ ps, p < n) (h : enumOK n gs ps c = true) {P Q : ℕ}
    (hP : permB n w P = true) (hQ : permB n w Q = true)
    (hmP : permOfArr n (unpack n w P) ∈ Subgroup.closure (permsA n gs))
    (hmQ : permOfArr n (unpack n w Q) ∈ Subgroup.closure (permsA n gs)) :
    Nat.beq P Q = Nat.beq (BfsPin.keyK n w ps P) (BfsPin.keyK n w ps Q) := by
  rw [← eqA_unpack' hw hP hQ, eqA_iff_keyA hps h (validA_unpack hP) (validA_unpack hQ) hmP hmQ,
    keyA_unpack hps, keyA_unpack hps]
  rfl

end CFSG.KC.PGrp

end
