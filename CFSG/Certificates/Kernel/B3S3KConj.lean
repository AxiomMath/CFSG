module

public import CFSG.Certificates.Kernel.B3S3KSound
public import Certificates.Data.Kernel.B3S3KCR
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.PinvSSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.KC.B3S3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native

variable {n w : ℕ} (hw : szOK n w = true)
include hw

omit hw in
theorem prep_pinvB {H : ℕ} {h : Equiv.Perm (Fin n)} (hw2 : n < 2 ^ w) (hH : PRep n w H h) :
    PRep n w (pinvS n w (mask w) H) h⁻¹ := by
  have hI : CFSG.KS.PinvS.InjK n w H :=
    ⟨fun i hi => by rw [hH ⟨i, hi⟩]; exact (h ⟨i, hi⟩).2, fun a ha b hb e => by
      rw [hH ⟨a, ha⟩, hH ⟨b, hb⟩] at e
      exact congrArg Fin.val (h.injective (Fin.ext e))⟩
  intro x
  have e := CFSG.KS.PinvS.pg_pinvS hw2 hI (h⁻¹ x).2
  rw [hH (h⁻¹ x)] at e
  simpa using e

omit hw in
theorem prep_ppowB {P : ℕ} {g : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw2 : n + 1 < 2 ^ w) (hP : PRep n w P g) :
    ∀ e, PRep n w (ppow n w (mask w) (pidn n w) P e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact prep_pidn hn hw2
  | e + 1 => by
    have he : ppow n w (mask w) (pidn n w) P (e + 1) =
        pcomp n w (mask w) P (ppow n w (mask w) (pidn n w) P e) := strictN_eq _ _
    rw [he, pow_succ']
    exact prep_pcomp (by omega) hP (prep_ppowB hn hw2 hP e)

omit hw in
theorem exists_prepB {P : ℕ} (hP : permB n w P = true) : ∃ g, PRep n w P g :=
  ⟨_, prep_of_rep (rep_of_validA (CFSG.KC.B3S3K.validA_of hP))⟩

theorem beq_prep {A B : ℕ} {g h : Equiv.Perm (Fin n)} (hA : permB n w A = true)
    (hB : permB n w B = true) (gA : PRep n w A g) (gB : PRep n w B h) :
    Nat.beq A B = decide (g = h) := by
  have hw2 := (szOK_facts' hw).2
  have h0 : 0 < w := Nat.pos_of_ne_zero fun e => by
    subst e
    omega
  by_cases e : g = h
  · rw [decide_eq_true e]
    have hAB : A = B := CFSG.KS.PF.eq_of_fields h0 (permOK_facts hA).1 (permOK_facts hB).1
      fun i hi => (gA ⟨i, hi⟩).trans
        ((congrArg (fun f : Equiv.Perm (Fin n) => ((f ⟨i, hi⟩ : Fin n) : ℕ)) e).trans
          (gB ⟨i, hi⟩).symm)
    rw [hAB]
    exact Nat.beq_refl B
  · rw [decide_eq_false e]
    cases hb : Nat.beq A B
    · rfl
    · exfalso
      apply e
      have hAB := Nat.eq_of_beq_eq_true hb
      subst hAB
      exact Equiv.ext fun x => Fin.ext ((gA x).symm.trans (gB x))

omit hw in
theorem convAt_congrR {N : ℕ} {T : ℕ → ℕ} {qs rs : List ℕ} {WJ WR WR' : ℕ → ℕ} {i : ℕ}
    (h : WR' i = WR i) : convAt n w N T qs rs WJ WR' i = convAt n w N T qs rs WJ WR i := by
  unfold convAt
  rw [h]

theorem convAt_conj {N : ℕ} {T : ℕ → ℕ} {qs rs : List ℕ} {WJ WR WR' : ℕ → ℕ} {i a gI : ℕ}
    (hTp : ∀ i < N, permB n w (T i) = true) (hi : i < N) (ha : a < N) (hg : gI < N)
    (hj : WJ i < N) (hja : WJ a < N)
    (h1 : Nat.beq (cm n w (T i) (T gI)) (cm n w (T gI) (T a)) = true)
    (h2 : Nat.beq (cm n w (T (WJ i)) (T gI)) (cm n w (T gI) (T (WJ a))) = true)
    (hr : WR' i = WR a) (h : convAt n w N T qs rs WJ WR a = true) :
    convAt n w N T qs rs WJ WR' i = true := by
  obtain ⟨hn24, hw2⟩ := szOK_facts' hw
  have hn : n < 2 ^ 32 := by omega
  have hw' : n < 2 ^ w := by omega
  have pI := hTp i hi
  have pA := hTp a ha
  have pG := hTp gI hg
  have pJ := hTp _ hj
  have pJa := hTp _ hja
  obtain ⟨t, ht⟩ := exists_prepB pI
  obtain ⟨u, hu⟩ := exists_prepB pA
  obtain ⟨g, hgg⟩ := exists_prepB pG
  obtain ⟨s', hs'⟩ := exists_prepB pJ
  obtain ⟨s, hs⟩ := exists_prepB pJa
  unfold cm at h1 h2
  rw [beq_prep hw (permB_pcomp hw pI pG) (permB_pcomp hw pG pA) (prep_pcomp hn ht hgg)
    (prep_pcomp hn hgg hu)] at h1
  rw [beq_prep hw (permB_pcomp hw pJ pG) (permB_pcomp hw pG pJa) (prep_pcomp hn hs' hgg)
    (prep_pcomp hn hgg hs)] at h2
  have et : t = g * u * g⁻¹ := eq_mul_inv_of_mul_eq (of_decide_eq_true h1)
  have es : s' = g * s * g⁻¹ := eq_mul_inv_of_mul_eq (of_decide_eq_true h2)
  subst et es
  have pid := permB_id hw
  have hid := prep_pidn hn24 hw2
  have hcj : ∀ x : Equiv.Perm (Fin n), decide (g * x * g⁻¹ = 1) = decide (x = 1) := fun x => by
    simp only [conj_eq_one_iff]
  have hqi : ∀ q, Nat.beq (ppow n w (mask w) (pidn n w) (T i) q) (pidn n w) = decide (u ^ q = 1) :=
    fun q => by
      rw [beq_prep hw (permB_ppow hw pI q) pid (prep_ppowB hn24 hw2 ht q) hid, conj_pow, hcj]
  have hqa : ∀ q, Nat.beq (ppow n w (mask w) (pidn n w) (T a) q) (pidn n w) = decide (u ^ q = 1) :=
    fun q => beq_prep hw (permB_ppow hw pA q) pid (prep_ppowB hn24 hw2 hu q) hid
  have hii : Nat.beq (T i) (pidn n w) = decide (u = 1) := by
    rw [beq_prep hw pI pid ht hid, hcj]
  have hia : Nat.beq (T a) (pidn n w) = decide (u = 1) := beq_prep hw pA pid hu hid
  have pZi := permB_pcomp hw pI (permB_pcomp hw pJ (permB_pcomp hw pI (permB_pinvS hw pJ)))
  have pZa := permB_pcomp hw pA (permB_pcomp hw pJa (permB_pcomp hw pA (permB_pinvS hw pJa)))
  have gZi := prep_pcomp hn ht (prep_pcomp hn hs' (prep_pcomp hn ht (prep_pinvB hw' hs')))
  have gZa := prep_pcomp hn hu (prep_pcomp hn hs (prep_pcomp hn hu (prep_pinvB hw' hs)))
  have ez : g * u * g⁻¹ * (g * s * g⁻¹ * (g * u * g⁻¹ * (g * s * g⁻¹)⁻¹)) =
      g * (u * (s * (u * s⁻¹))) * g⁻¹ := by group
  rw [ez] at gZi
  have hzi : ∀ e, Nat.beq (ppow n w (mask w) (pidn n w) (pcomp n w (mask w) (T i)
      (pcomp n w (mask w) (T (WJ i)) (pcomp n w (mask w) (T i) (pinvS n w (mask w) (T (WJ i))))))
        e) (pidn n w) = decide ((u * (s * (u * s⁻¹))) ^ e = 1) := fun e => by
    rw [beq_prep hw (permB_ppow hw pZi e) pid (prep_ppowB hn24 hw2 gZi e) hid, conj_pow, hcj]
  have hza : ∀ e, Nat.beq (ppow n w (mask w) (pidn n w) (pcomp n w (mask w) (T a)
      (pcomp n w (mask w) (T (WJ a)) (pcomp n w (mask w) (T a) (pinvS n w (mask w) (T (WJ a))))))
        e) (pidn n w) = decide ((u * (s * (u * s⁻¹))) ^ e = 1) := fun e =>
    beq_prep hw (permB_ppow hw pZa e) pid (prep_ppowB hn24 hw2 gZa e) hid
  have hzi3 : ∀ e, Nat.beq (ppow n w (mask w) (pidn n w) (ppow n w (mask w) (pidn n w)
      (pcomp n w (mask w) (T i) (pcomp n w (mask w) (T (WJ i))
        (pcomp n w (mask w) (T i) (pinvS n w (mask w) (T (WJ i)))))) e) 3) (pidn n w) =
      decide (((u * (s * (u * s⁻¹))) ^ e) ^ 3 = 1) := fun e => by
    rw [beq_prep hw (permB_ppow hw (permB_ppow hw pZi e) 3) pid
      (prep_ppowB hn24 hw2 (prep_ppowB hn24 hw2 gZi e) 3) hid, conj_pow, conj_pow, hcj]
  have hza3 : ∀ e, Nat.beq (ppow n w (mask w) (pidn n w) (ppow n w (mask w) (pidn n w)
      (pcomp n w (mask w) (T a) (pcomp n w (mask w) (T (WJ a))
        (pcomp n w (mask w) (T a) (pinvS n w (mask w) (T (WJ a)))))) e) 3) (pidn n w) =
      decide (((u * (s * (u * s⁻¹))) ^ e) ^ 3 = 1) := fun e =>
    beq_prep hw (permB_ppow hw (permB_ppow hw pZa e) 3) pid
      (prep_ppowB hn24 hw2 (prep_ppowB hn24 hw2 gZa e) 3) hid
  have hbi : Nat.blt (WJ i) N = true := by
    rw [Nat.blt_eq]
    exact hj
  have hba : Nat.blt (WJ a) N = true := by
    rw [Nat.blt_eq]
    exact hja
  unfold convAt zOK pw cj cm at h ⊢
  rw [hr]
  simp only [hqa, hia, hza, hza3, hba] at h
  simp only [hqi, hii, hzi, hzi3, hbi]
  exact h

theorem convAt_of_convCR {N : ℕ} {T : ℕ → ℕ} {qs rs : List ℕ} {WJ WR CR CG : ℕ → ℕ}
    (hTp : ∀ i < N, permB n w (T i) = true)
    (h : allN N (convCR n w N T qs rs WJ WR CR CG) = true) :
    allN N (convAt n w N T qs rs WJ fun i => WR (CR i)) = true := by
  rw [Orb.allN_iff] at h ⊢
  intro i hi
  have hc := h i hi
  unfold convCR at hc
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hcr, hcc⟩, hc3⟩, hc4⟩ := hc
  have hcc' : CR (CR i) = CR i := Nat.eq_of_beq_eq_true hcc
  by_cases he : CR i = i
  · have hb : Nat.beq (CR i) i = true := by
      rw [he]
      exact Nat.beq_refl i
    rw [hb, Bool.not_true, Bool.false_or] at hc3
    rw [convAt_congrR (WR := WR) (WR' := fun i => WR (CR i)) (i := i) (congrArg WR he)]
    exact hc3
  · have hb : Nat.beq (CR i) i = false := by
      cases hb' : Nat.beq (CR i) i
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb') he
    rw [hb, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at hc4
    obtain ⟨⟨⟨⟨hg, hj⟩, hja⟩, h1⟩, h2⟩ := hc4
    have ha := h (CR i) hcr
    unfold convCR at ha
    have hb2 : Nat.beq (CR (CR i)) (CR i) = true := hcc
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, hb2, Bool.not_true,
      Bool.false_or] at ha
    exact convAt_conj hw hTp hi hcr hg hj hja h1 h2 rfl ha.1.2

end CFSG.KC.B3S3K

end
