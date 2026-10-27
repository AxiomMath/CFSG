module

public import Certificates.Data.Kernel.U43Alpha.Defs
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace CFSG.KS.U43Alpha

open CFSG.KC.Enum CFSG.KC.U43Alpha CFSG.KS.Raw.Orb

@[expose] noncomputable def szOf (SZ i : ℕ) : ℕ := fld(SZ, Nat.mul (nat_lit 8) i, nat_lit 255)

theorem cntRec_eq (P : ℕ → Bool) (n : ℕ) :
    Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun q ih => Bool.rec (motive := fun _ => ℕ) ih (Nat.succ ih) (P q)) n =
      ((Finset.range n).filter fun q => P q = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => ℕ) _ (Nat.succ _) (P n) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    have hn : n ∉ (Finset.range n).filter fun q => P q = true := by simp
    cases h : P n with
    | false => simp
    | true => rw [if_pos rfl, Finset.card_insert_of_notMem hn]

theorem cntFix_eq (f : ℕ → ℕ) (n : ℕ) :
    cntFix f n = ((Finset.range n).filter fun q => f q = q).card := by
  rw [cntFix, cntRec_eq]
  simp only [Nat.beq_eq]

theorem cntLab_eq (L n i : ℕ) :
    cntLab L n i = ((Finset.range n).filter fun q => labOf L q = i).card := by
  rw [cntLab, cntRec_eq]
  simp only [Nat.beq_eq]

theorem cntSz_eq (SZ nb s : ℕ) :
    cntSz SZ nb s = ((Finset.range nb).filter fun i => szOf SZ i = s).card := by
  rw [cntSz, cntRec_eq]
  simp only [Nat.beq_eq, szOf]
  rfl

section OrbPart

variable {n k L R RO nb SZ : ℕ} {S : ℕ → ℕ}

theorem rowOK_spec {p : ℕ} (h : rowOK n S k L R RO nb p = true) :
    labOf L p < nb ∧ (∀ j < k, labOf L (pg 10 1023 (S j) p) = labOf L p) ∧
      (Nat.shiftRight (rowOf R p) 14 = 0 → fld(RO, Nat.mul 10 (labOf L p), 1023) = p) ∧
      (Nat.shiftRight (rowOf R p) 14 ≠ 0 → ∃ par < n, ∃ j < k, pg 10 1023 (S j) par = p ∧
        labOf L par = labOf L p ∧
        Nat.shiftRight (rowOf R par) 14 + 1 = Nat.shiftRight (rowOf R p) 14) := by
  unfold rowOK at h
  rw [strictB_eq, strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, allN_iff]
    at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.blt_eq.mp h1, fun j hj => Nat.beq_eq.mp (h3 j hj), fun hd => ?_, fun hd => ?_⟩
  · have hb : Nat.beq (Nat.shiftRight (rowOf R p) 14) 0 = true := Nat.beq_eq.mpr hd
    rw [hb] at h2
    change (Nat.beq _ p && Nat.beq _ p) = true at h2
    rw [Bool.and_eq_true] at h2
    exact Nat.beq_eq.mp h2.2
  · have hb : Nat.beq (Nat.shiftRight (rowOf R p) 14) 0 = false := by
      cases e : Nat.beq (Nat.shiftRight (rowOf R p) 14) 0
      · rfl
      · exact absurd (Nat.beq_eq.mp e) hd
    rw [hb] at h2
    change strictB _ _ = true at h2
    rw [strictB_eq, strictB_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h2
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h2
    obtain ⟨hj, hpar, hpg, hlab, hdep⟩ := h2
    exact ⟨_, hpar, _, hj, hpg, hlab, hdep⟩

theorem orbPart_row (h : orbPart n S k L R RO nb SZ = true) {p : ℕ} (hp : p < n) :
    rowOK n S k L R RO nb p = true := by
  unfold orbPart at h
  rw [bAnd_eq, Bool.and_eq_true, allN_iff] at h
  exact h.1 p hp

theorem orbPart_lab_lt (h : orbPart n S k L R RO nb SZ = true) {p : ℕ} (hp : p < n) :
    labOf L p < nb :=
  (rowOK_spec (orbPart_row h hp)).1

theorem orbPart_inv (h : orbPart n S k L R RO nb SZ = true) {p : ℕ} (hp : p < n) {j : ℕ}
    (hj : j < k) : labOf L (pg 10 1023 (S j) p) = labOf L p :=
  (rowOK_spec (orbPart_row h hp)).2.1 j hj

theorem orbPart_card (h : orbPart n S k L R RO nb SZ = true) {i : ℕ} (hi : i < nb) :
    ((Finset.range n).filter fun q => labOf L q = i).card = szOf SZ i := by
  unfold orbPart at h
  rw [bAnd_eq, Bool.and_eq_true, allN_iff, allN_iff] at h
  rw [← cntLab_eq]
  exact Nat.beq_eq.mp (h.2 i hi)

theorem orbPart_conn (h : orbPart n S k L R RO nb SZ = true) (Q : ℕ → Prop)
    (hQ : ∀ x < n, ∀ j < k, (Q (pg 10 1023 (S j) x) ↔ Q x)) {p q : ℕ} (hp : p < n) (hq : q < n)
    (hl : labOf L p = labOf L q) (hQp : Q p) : Q q := by
  have key : ∀ d, ∀ x < n, Nat.shiftRight (rowOf R x) 14 = d →
      (Q x ↔ Q (fld(RO, Nat.mul 10 (labOf L x), 1023))) := by
    intro d
    induction d with
    | zero =>
      intro x hx hd
      rw [(rowOK_spec (orbPart_row h hx)).2.2.1 hd]
    | succ d ih =>
      intro x hx hd
      obtain ⟨par, hpar, j, hj, hpg, hlab, hdep⟩ :=
        (rowOK_spec (orbPart_row h hx)).2.2.2 (by omega)
      have e := ih par hpar (by omega)
      rw [hlab] at e
      rw [← e, ← hQ par hpar j hj, hpg]
  have kp := key _ p hp rfl
  have kq := key _ q hq rfl
  rw [hl] at kp
  exact kq.2 (kp.1 hQp)

end OrbPart

theorem sumMask_testBit (SZ : ℕ) : ∀ (nb : ℕ) (I : Finset ℕ), I ⊆ Finset.range nb →
    (sumMask SZ nb).testBit (∑ i ∈ I, szOf SZ i) = true := by
  intro nb
  induction nb with
  | zero =>
    intro I hI
    rw [Finset.range_zero, Finset.subset_empty] at hI
    subst hI
    rw [Finset.sum_empty]
    change (1 : ℕ).testBit 0 = true
    exact Nat.testBit_one_zero
  | succ nb ih =>
    intro I hI
    have e : sumMask SZ (nb + 1) = sumMask SZ nb ||| (sumMask SZ nb <<< szOf SZ nb) := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true]
    by_cases hm : nb ∈ I
    · right
      have hs : I = insert nb (I.erase nb) := (Finset.insert_erase hm).symm
      have hsub : I.erase nb ⊆ Finset.range nb := by
        intro x hx
        have hx' := hI (Finset.mem_of_mem_erase hx)
        rw [Finset.mem_range] at hx' ⊢
        have := Finset.ne_of_mem_erase hx
        omega
      rw [hs, Finset.sum_insert (Finset.notMem_erase nb I), Nat.testBit_shiftLeft]
      simp only [ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and,
        Nat.add_sub_cancel_left]
      exact ih _ hsub
    · left
      apply ih
      intro x hx
      have hx' := hI hx
      rw [Finset.mem_range] at hx' ⊢
      have : x ≠ nb := fun e => hm (e ▸ hx)
      omega

theorem fld_one_eq_zero {M t : ℕ} (h : Nat.land (Nat.shiftRight M t) 1 = 0) :
    M.testBit t = false := by
  have h' : M >>> t &&& 1 = 0 := h
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at h'
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp [h']

theorem noFixSum_sound {SZ nb : ℕ} (h : noFixSum SZ nb = true) (I : Finset ℕ)
    (hI : I ⊆ Finset.range nb) : (∑ i ∈ I, szOf SZ i) ≠ 20 ∧ (∑ i ∈ I, szOf SZ i) ≠ 40 ∧
      (∑ i ∈ I, szOf SZ i) ≠ 92 := by
  unfold noFixSum at h
  rw [strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h20, h40, h92⟩ := h
  have hb := sumMask_testBit SZ nb I hI
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [e, fld_one_eq_zero (Nat.beq_eq.mp h20)] at hb
    exact Bool.false_ne_true hb
  · rw [e, fld_one_eq_zero (Nat.beq_eq.mp h40)] at hb
    exact Bool.false_ne_true hb
  · rw [e, fld_one_eq_zero (Nat.beq_eq.mp h92)] at hb
    exact Bool.false_ne_true hb

end CFSG.KS.U43Alpha

end
