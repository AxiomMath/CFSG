module

public import CFSG.Certificates.Kernel.PGrpSound

public section

namespace CFSG.KC.PGrp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Monster.B.Co2 (permOfArr rep_compA rep_idA)

variable {n w : ℕ} (hw : szOK n w = true) {gs : Array (Array ℕ)}
include hw

theorem permOfArr_pcomp {P Q : ℕ} (hP : permB n w P = true) (hQ : permB n w Q = true) :
    permOfArr n (unpack n w (pcomp n w (mask w) P Q)) =
      permOfArr n (unpack n w P) * permOfArr n (unpack n w Q) := by
  rw [← comp_unpack' hw hP hQ]
  exact permOfArr_eq_of_rep (rep_compA (rep_of_validA (validA_unpack hP))
    (rep_of_validA (validA_unpack hQ)))

theorem mem_mul {P Q : ℕ} (hP : permB n w P = true) (hQ : permB n w Q = true)
    (hmP : permOfArr n (unpack n w P) ∈ Subgroup.closure (permsA n gs))
    (hmQ : permOfArr n (unpack n w Q) ∈ Subgroup.closure (permsA n gs)) :
    permOfArr n (unpack n w (pcomp n w (mask w) P Q)) ∈ Subgroup.closure (permsA n gs) := by
  rw [permOfArr_pcomp hw hP hQ]
  exact Subgroup.mul_mem _ hmP hmQ

theorem mem_id : permOfArr n (unpack n w (pidn n w)) ∈ Subgroup.closure (permsA n gs) := by
  rw [← idA_eq hw, permOfArr_eq_of_rep rep_idA]
  exact Subgroup.one_mem _

theorem permB_pcomp {P Q : ℕ} (hP : permB n w P = true) (hQ : permB n w Q = true) :
    permB n w (pcomp n w (mask w) P Q) = true :=
  permB_of_pp ((pp_of_permB hw hP).mul (pp_of_permB hw hQ))

theorem eqA_keyCK {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (h : enumOK n gs ps c = true) {P Q R S : ℕ} (hP : permB n w P = true)
    (hQ : permB n w Q = true) (hR : permB n w R = true) (hS : permB n w S = true)
    (hmP : permOfArr n (unpack n w P) ∈ Subgroup.closure (permsA n gs))
    (hmQ : permOfArr n (unpack n w Q) ∈ Subgroup.closure (permsA n gs))
    (hmR : permOfArr n (unpack n w R) ∈ Subgroup.closure (permsA n gs))
    (hmS : permOfArr n (unpack n w S) ∈ Subgroup.closure (permsA n gs)) :
    eqA n (compA n (unpack n w P) (unpack n w Q)) (compA n (unpack n w R) (unpack n w S)) =
      Nat.beq (keyCK n w ps P Q) (keyCK n w ps R S) := by
  have hn := (pp_of_permB hw hP).lt32
  rw [comp_unpack' hw hP hQ, comp_unpack' hw hR hS,
    eqA_unpack' hw (permB_pcomp hw hP hQ) (permB_pcomp hw hR hS),
    beq_iff_keyK hw hps h (permB_pcomp hw hP hQ) (permB_pcomp hw hR hS)
      (mem_mul hw hP hQ hmP hmQ) (mem_mul hw hR hS hmR hmS),
    keyK_pcomp hn P Q hps, keyK_pcomp hn R S hps]

theorem eqA_keyCK_keyK {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (h : enumOK n gs ps c = true) {P Q R : ℕ} (hP : permB n w P = true)
    (hQ : permB n w Q = true) (hR : permB n w R = true)
    (hmP : permOfArr n (unpack n w P) ∈ Subgroup.closure (permsA n gs))
    (hmQ : permOfArr n (unpack n w Q) ∈ Subgroup.closure (permsA n gs))
    (hmR : permOfArr n (unpack n w R) ∈ Subgroup.closure (permsA n gs)) :
    eqA n (compA n (unpack n w P) (unpack n w Q)) (unpack n w R) =
      Nat.beq (keyCK n w ps P Q) (BfsPin.keyK n w ps R) := by
  have hn := (pp_of_permB hw hP).lt32
  rw [comp_unpack' hw hP hQ, eqA_unpack' hw (permB_pcomp hw hP hQ) hR,
    beq_iff_keyK hw hps h (permB_pcomp hw hP hQ) hR (mem_mul hw hP hQ hmP hmQ) hmR,
    keyK_pcomp hn P Q hps]

theorem mem_of_pt {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (h : enumOK n gs ps c = true) {N : ℕ} {T : ℕ → ℕ} (hN : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack n w (T i)) {i : ℕ} (hi : i < N) :
    permOfArr n (unpack n w (T i)) ∈ Subgroup.closure (permsA n gs) :=
  ((enumOK_spec hps h).1 _).2 ⟨i, by rw [hN]; exact hi, by rw [hT i hi]⟩

theorem mem_of_memK {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (h : enumOK n gs ps c = true) {N : ℕ} {T : ℕ → ℕ} (hN : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack n w (T i)) {P : ℕ} (hm : memK N T P = true) :
    permOfArr n (unpack n w P) ∈ Subgroup.closure (permsA n gs) := by
  rw [memK, anyNP_eq, List.any_eq_true] at hm
  obtain ⟨i, hi, e⟩ := hm
  rw [Nat.eq_of_beq_eq_true e]
  exact mem_of_pt hw hps h hN hT (List.mem_range.1 hi)

end CFSG.KC.PGrp

end
