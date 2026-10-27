module

public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.Spec.DceCore

public section

namespace CFSG.KC.Th.Spec.DceClass

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Th.Spec.Dce

variable {M : Subgroup Mat24ˣ} {LT LC LI TL VL NL : ℕ} {G : Type*} [Group G] {x : ℕ → G}
  {φ : M →* G}

private theorem mEl_mul {A B : ℕ} (hA : InM M A) (hB : InM M B) :
    mEl M (mul24 A B) = mEl M A * mEl M B :=
  mEl_eq _ (mul24_lt _ _) (by
    rw [Subgroup.coe_mul, Units.val_mul, mEl_val hA, mEl_val hB, toMat_mul24])

private theorem mEl_invR {A B : ℕ} (hA : InM M A) (hB : InM M B) (h : mul24 A B = ident24) :
    mEl M B = (mEl M A)⁻¹ := by
  have e := mEl_mul hA hB
  rw [h, mEl_eq 1 ident24_lt (by rw [toMat_ident24]; rfl)] at e
  exact eq_inv_of_mul_eq_one_right e.symm

private theorem cls_conj (hC : MCtx M LT LC LI TL VL NL x φ) {CB P Q adv : ℕ → ℕ} {Cs : List ℕ}
    {n : ℕ} (h0 : InM M (mat CB 0))
    (h : CFSG.Certificates.DceLoop.cntRun (fun k J => andB (Nat.blt (P J) k)
        (andB (isN TL VL NL (Q J)) (Nat.beq (mat CB k)
          (mul24 (mul24 (let24 LT (byte LI (Q J))) (mat CB (P J))) (let24 LT (Q J))))))
      adv 65535 16 Cs 2 = n + 1) :
    ∀ k < n, InM M (mat CB k) ∧ ∃ m : M, mEl M (mat CB k) = m⁻¹ * mEl M (mat CB 0) * m := by
  have hi := CFSG.Certificates.DceLoop.cntRun_spec (a := 1) h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨h0, 1, by rw [inv_one, one_mul, mul_one]⟩
    obtain ⟨J, hJ⟩ := hi k hk0 hk
    obtain ⟨e1, r⟩ := andB_iff.1 hJ
    obtain ⟨e2, e3⟩ := andB_iff.1 r
    have hp : P J < k := Nat.blt_eq.mp e1
    have he : mat CB k = mul24 (mul24 (let24 LT (byte LI (Q J))) (mat CB (P J))) (let24 LT (Q J)) :=
      Nat.eq_of_beq_eq_true e3
    obtain ⟨hpM, m', hm'⟩ := ih _ hp (by omega)
    have hg : InM M (let24 LT (Q J)) := hC.inM_letter e2
    have hgi : InM M (let24 LT (byte LI (Q J))) := hC.inM_letter (hC.hL.isN_inv e2)
    have hinv := mEl_invR hg hgi (hC.hL.nval _ e2).2
    rw [he]
    refine ⟨InM_mul (InM_mul hgi hpM) hg, m' * mEl M (let24 LT (Q J)), ?_⟩
    rw [mEl_mul (InM_mul hgi hpM) hg, mEl_mul hgi hpM, hinv, hm']
    simp only [mul_inv_rev, mul_assoc]

private theorem runClass_eq (CB : ℕ → ℕ) (LT LI TL VL NL : ℕ) (Cs : List ℕ) (S : ℕ) :
    DceS.runClass CB LT LI TL VL NL Cs S = CFSG.Certificates.DceLoop.cntRun
      (fun k J => andB (Nat.blt (bits J 0 10) k) (andB (isN TL VL NL (bits J 10 4))
        (Nat.beq (mat CB k) (mul24 (mul24 (let24 LT (byte LI (bits J 10 4)))
          (mat CB (bits J 0 10))) (let24 LT (bits J 10 4))))))
      (fun _ => 14) 65535 16 Cs S := rfl

private theorem runClass2_eq (CB : ℕ → ℕ) (LT LI TL VL NL : ℕ) (Cs : List ℕ) (S : ℕ) :
    OutS.runClass2 CB LT LI TL VL NL Cs S = CFSG.Certificates.DceLoop.cntRun
      (fun k J => andB (Nat.blt (BigS.bitsN J 0 17) k) (andB (isN TL VL NL (BigS.bitsN J 17 4))
        (Nat.beq (mat CB k) (mul24 (mul24 (let24 LT (byte LI (BigS.bitsN J 17 4)))
          (mat CB (BigS.bitsN J 0 17))) (let24 LT (BigS.bitsN J 17 4))))))
      (fun _ => 21) 65535 16 Cs S := rfl

theorem runClass_conj (hC : MCtx M LT LC LI TL VL NL x φ) {CB : ℕ → ℕ} {Cs : List ℕ} {n : ℕ}
    (h0 : InM M (mat CB 0)) (h : DceS.runClass CB LT LI TL VL NL Cs 2 = n + 1) :
    ∀ k < n, InM M (mat CB k) ∧ ∃ m : M, mEl M (mat CB k) = m⁻¹ * mEl M (mat CB 0) * m := by
  rw [runClass_eq] at h
  exact cls_conj hC h0 h

theorem runClass2_conj (hC : MCtx M LT LC LI TL VL NL x φ) {CB : ℕ → ℕ} {Cs : List ℕ} {n : ℕ}
    (h0 : InM M (mat CB 0)) (h : OutS.runClass2 CB LT LI TL VL NL Cs 2 = n + 1) :
    ∀ k < n, InM M (mat CB k) ∧ ∃ m : M, mEl M (mat CB k) = m⁻¹ * mEl M (mat CB 0) * m := by
  rw [runClass2_eq] at h
  exact cls_conj hC h0 h

private theorem natRec_add_eq_sum (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
    rw [natRec_add_eq_sum F k, Finset.sum_range_succ, Nat.add_comm]

private theorem sumBelow_eq_sum64 (m : ℕ) (f : ℕ → ℕ) : ∀ hi, CFSG.KC.Loop.sumBelow m hi f =
    ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m)
  | 0 => by simp [CFSG.KC.Loop.sumBelow]
  | hi + 1 => by
    have e : CFSG.KC.Loop.sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0
        (fun l ih2 => Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (CFSG.KC.Loop.sumBelow m hi f) := rfl
    have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
      change hi <<< 6 + l = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e, natRec_add_eq_sum, sumBelow_eq_sum64 m f hi, Nat.mul_succ, Finset.sum_range_add]
    simp only [e2]
    exact Nat.add_comm _ _

private theorem sumBelow_eq_sum {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    CFSG.KC.Loop.sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  rw [sumBelow_eq_sum64]
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [hd, Finset.sum_range_add]
  have h2 : ∑ l ∈ Finset.range d,
      Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hb : Nat.blt (m + l) m = false := by
      cases e : Nat.blt (m + l) m
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [hb]
  rw [h2, Nat.add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hb : Nat.blt i m = true := Nat.blt_eq.mpr (Finset.mem_range.1 hi)
  rw [hb]

private theorem countGen (r : ℕ → Bool) (E : ℕ → ℕ) {lo n hi : ℕ} (hn : n ≤ 64 * hi) :
    CFSG.KC.Loop.sumBelow n hi (fun i => Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (nat_lit 1)
      (r (E (Nat.add lo i)))) =
      ((Finset.range n).filter fun i => r (E (lo + i)) = true).card := by
  rw [sumBelow_eq_sum _ hn, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  change Bool.rec (motive := fun _ => ℕ) 0 1 (r (E (lo + i))) = _
  cases r (E (lo + i)) <;> rfl

theorem countA_eq (EB : ℕ → ℕ) {lo n hi : ℕ} (hn : n ≤ 64 * hi) :
    OutS.countA EB lo n hi =
      ((Finset.range n).filter fun i => OutS.invRank 6 (mat EB (lo + i)) = true).card :=
  countGen (OutS.invRank (nat_lit 6)) (mat EB) hn

private theorem coreInner {t : ℕ} {B : ℕ → ℕ} {m : ℕ}
    (h : Nat.rec (motive := fun _ => Bool) true (fun j acc2 => andB acc2
      (Bool.rec (motive := fun _ => Bool) true false (Nat.beq t (B j)))) m = true) :
    ∀ j < m, t ≠ B j := fun j hj =>
  Nat.ne_of_beq_eq_false ((CFSG.Certificates.DceLoop.bnot_iff _).1
    ((allB_iff (fun j => Bool.rec (motive := fun _ => Bool) true false (Nat.beq t (B j))) m).1
      h j hj))

theorem coreOK_spec {EB : ℕ → ℕ} {LT LI g m : ℕ} (h : OutS.coreOK EB LT LI g m = true) :
    ∀ k < m, mat EB k = ident24 ∨
      ∀ j < m, mul24 (mul24 (let24 LT (byte LI g)) (mat EB k)) (let24 LT g) ≠ mat EB j := by
  intro k hk
  have h1 := (allB_iff (fun k => orB (Nat.beq (mat EB k) ident24)
    (Nat.rec (motive := fun _ => Bool) true (fun j acc2 => andB acc2
      (Bool.rec (motive := fun _ => Bool) true false
        (Nat.beq (mul24 (mul24 (let24 LT (byte LI g)) (mat EB k)) (let24 LT g)) (mat EB j)))) m))
    m).1 h k hk
  rcases orB_iff.1 h1 with e | e
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · exact Or.inr (coreInner (t := mul24 (mul24 (let24 LT (byte LI g)) (mat EB k)) (let24 LT g))
      (B := mat EB) e)

end CFSG.KC.Th.Spec.DceClass

end
