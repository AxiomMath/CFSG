module

public import CFSG.Certificates.Kernel.Th.Spec.DceFacts
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Loop CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw

set_option exponentiation.threshold 700

theorem aliveD_iff (AL D : ℕ) : aliveD AL D = true ↔ AL.testBit D = true := aliveG_iff AL D

theorem slotOK_spec {FB OB : ℕ → ℕ} {sh wd osh owd om NB sel NF AL D w x tau : ℕ}
    (hs : DceS.slotOK FB OB sh wd osh owd om NB sel NF AL D w x tau = true) :
    x >>> 1 < NF ∧
      ((rD (rec FB sh wd (x >>> 1)) = D ∧ rJ (rec FB sh wd (x >>> 1)) = w + 1 ∧
          AL.testBit (rDp (rec FB sh wd (x >>> 1))) = true) ∨
        (rDp (rec FB sh wd (x >>> 1)) = D ∧ 0 < rJ (rec FB sh wd (x >>> 1)) ∧
          AL.testBit (rD (rec FB sh wd (x >>> 1))) = true ∧
          actOK NB sel (pt OB osh owd om w) (rPi (rec FB sh wd (x >>> 1)))
            (pt OB osh owd om (rJ (rec FB sh wd (x >>> 1)) - 1)) tau = true)) := by
  unfold DceS.slotOK at hs
  beta_reduce at hs
  obtain ⟨e1, e2⟩ := andB_iff.1 hs
  refine ⟨Nat.blt_eq.mp e1, ?_⟩
  revert e2
  cases Nat.beq (Nat.land x 1) 1
  · intro e2
    obtain ⟨f1, r⟩ := andB_iff.1 e2
    obtain ⟨f2, f3⟩ := andB_iff.1 r
    exact Or.inl ⟨Nat.eq_of_beq_eq_true f1, Nat.eq_of_beq_eq_true f2, (aliveD_iff _ _).1 f3⟩
  · intro e2
    obtain ⟨f1, r⟩ := andB_iff.1 e2
    obtain ⟨f2, r⟩ := andB_iff.1 r
    obtain ⟨f3, f4⟩ := andB_iff.1 r
    exact Or.inr ⟨Nat.eq_of_beq_eq_true f1, Nat.blt_eq.mp f2, (aliveD_iff _ _).1 f3, f4⟩

@[expose] noncomputable def covStepT (slot : ℕ → ℕ → ℕ → ℕ → Bool) (tb NO AL : ℕ)
    (ih2 : ℕ → ℕ → ℕ) (J S : ℕ) : ℕ :=
  (fun D w => (fun nxt =>
      Bool.rec (motive := fun _ => ℕ) 0
        (Bool.rec (motive := fun _ => ℕ)
          (strictN nxt (ih2 J))
          ((fun x => (fun tbb => strictN (Bool.rec (motive := fun _ => ℕ) 0 nxt
                (slot D w x (bits J 21 tbb)))
              (ih2 (Nat.shiftRight J (Nat.add 21 tbb))))
            (Bool.rec (motive := fun _ => ℕ) 0 tb (Nat.beq (Nat.land x 1) 1)))
            (bits J 0 21))
          (aliveD AL D))
        (Nat.blt 0 S))
      (Bool.rec (motive := fun _ => ℕ) (Nat.add S 1)
        (Nat.add 1 (Nat.shiftLeft (Nat.succ D) 20))
        (orB (notB (aliveD AL D)) (Nat.beq (Nat.succ w) NO))))
    (Nat.shiftRight (Nat.sub S 1) 20) (Nat.land (Nat.sub S 1) M20)

@[expose] noncomputable def covInT (slot : ℕ → ℕ → ℕ → ℕ → Bool) (tb NO AL n J S : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih2 J S => covStepT slot tb NO AL ih2 J S) n J S

theorem runCover_eq (FB OB : ℕ → ℕ) (sh wd osh owd om NB sel NF NO AL : ℕ) (Cs : List ℕ) (S : ℕ) :
    DceS.runCover FB OB sh wd osh owd om NB sel NF NO AL Cs S =
      List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
        (fun C _ ih S => strictN (covInT (fun D w x h =>
          DceS.slotOK FB OB sh wd osh owd om NB sel NF AL D w x h) (tauBits NB) NO AL
            (Nat.land C 65535) (Nat.shiftRight C 16) S) ih) Cs S := rfl

theorem covInT_inv {slot : ℕ → ℕ → ℕ → ℕ → Bool} {tb NO AL : ℕ} (hNO : NO < 2 ^ 20)
    (hNO0 : 0 < NO) : ∀ (n J S : ℕ), CovInv slot NO AL S →
      CovInv slot NO AL (covInT slot tb NO AL n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change CovInv slot NO AL (covStepT slot tb NO AL (covInT slot tb NO AL n) J S)
    have ih := covInT_inv (slot := slot) (tb := tb) (AL := AL) hNO hNO0 n
    rcases h with rfl | ⟨D, w, rfl, hw, hw0, hprev, hcur⟩
    · exact Or.inl rfl
    obtain ⟨eD, ew⟩ := covDec (D := D) (Nat.lt_trans hw hNO)
    have ew' : Nat.land (Nat.sub (1 + 2 ^ 20 * D + w) 1) M20 = w := ew
    have hpos : Nat.blt 0 (1 + 2 ^ 20 * D + w) = true := by
      rw [Nat.blt_eq]
      omega
    have hnext := covNext_inv (slot := slot) hNO0 hw hw0 hprev hcur
    unfold covStepT
    simp only []
    rw [eD, ew', hpos]
    dsimp only
    cases ha : aliveD AL D
    · have ha' : aliveG AL D = false := ha
      rw [ha'] at hnext
      dsimp only at hnext ⊢
      rw [strictN_eq]
      exact ih _ _ (hnext (fun hal => absurd ((aliveG_iff AL D).2 hal) (by rw [ha']; decide)))
    · have ha' : aliveG AL D = true := ha
      rw [ha'] at hnext
      dsimp only at hnext ⊢
      rw [strictN_eq]
      apply ih
      cases hs : slot D w (bits J 0 21)
          (bits J 21 (Bool.rec (motive := fun _ => ℕ) 0 tb (Nat.beq (Nat.land (bits J 0 21) 1) 1)))
      · exact Or.inl rfl
      · dsimp only
        exact hnext (fun _ => ⟨_, _, hs⟩)

theorem coverRunT_inv {slot : ℕ → ℕ → ℕ → ℕ → Bool} {tb NO AL : ℕ} (hNO : NO < 2 ^ 20)
    (hNO0 : 0 < NO) : ∀ (Cs : List ℕ) (S : ℕ), CovInv slot NO AL S → CovInv slot NO AL
      (List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
        (fun C _ ih S => strictN (covInT slot tb NO AL (Nat.land C 65535) (Nat.shiftRight C 16) S)
          ih) Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change CovInv slot NO AL (strictN (covInT slot tb NO AL (Nat.land C 65535)
      (Nat.shiftRight C 16) S) (fun S => List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
        (fun C _ ih S => strictN (covInT slot tb NO AL (Nat.land C 65535) (Nat.shiftRight C 16) S)
          ih) Cs S))
    rw [strictN_eq]
    exact coverRunT_inv hNO hNO0 Cs _ (covInT_inv hNO hNO0 _ _ _ h)

theorem runCover_spec {FB OB : ℕ → ℕ} {sh wd osh owd om NB sel NF NO AL ND : ℕ} {Cs : List ℕ}
    (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO)
    (h : DceS.runCover FB OB sh wd osh owd om NB sel NF NO AL Cs 1 = 1 + ND * 2 ^ 20) :
    ∀ D < ND, AL.testBit D = true → ∀ w < NO, ∃ x tau,
      DceS.slotOK FB OB sh wd osh owd om NB sel NF AL D w x tau = true := by
  have h1 : CovInv (fun D w x h => DceS.slotOK FB OB sh wd osh owd om NB sel NF AL D w x h)
      NO AL 1 := Or.inr ⟨0, 0, rfl, hNO0, Or.inl rfl,
    fun D' hD' => absurd hD' (Nat.not_lt_zero _), fun w' hw' => absurd hw' (Nat.not_lt_zero _)⟩
  rw [runCover_eq] at h
  have hi := coverRunT_inv (tb := tauBits NB) hNO hNO0 Cs 1 h1
  rw [h, show 1 + ND * 2 ^ 20 = 1 + 2 ^ 20 * ND + 0 by ring] at hi
  intro D hD hal w hw
  rcases hi with h0 | ⟨D1, w1, he, hw1, -, hprev, -⟩
  · omega
  obtain ⟨d1, -⟩ := covDec (D := ND) (w := 0) (by norm_num)
  obtain ⟨d3, -⟩ := covDec (D := D1) (Nat.lt_trans hw1 hNO)
  rw [he] at d1
  rw [d1] at d3
  subst d3
  exact hprev D hD hal w hw

theorem runSorted_eq (get : ℕ → ℕ) (qb m : ℕ) (Cs : List ℕ) (S : ℕ) :
    DceS.runSorted get qb m Cs S = sortRun get qb m Cs S := rfl

theorem runStab_eq (FB EB : ℕ → ℕ) (sh wd NF D SG : ℕ) (Cs : List ℕ) (S : ℕ) :
    DceS.runStab FB EB sh wd NF D SG Cs S = cntRun
      (fun k J => andB (Nat.blt (bits J 0 17) k)
        (Nat.beq (mat EB k) (mul24 (mat EB (bits J 0 17))
          (DceS.stabGen FB sh wd NF D SG (bits J 17 5))))) (fun _ => 22) 65535 16 Cs S := rfl

theorem stabGen_spec (FB : ℕ → ℕ) (sh wd NF D SG s : ℕ) :
    DceS.stabGen FB sh wd NF D SG s = 0 ∨ ∃ g < NF, rD (rec FB sh wd g) = D ∧
      rJ (rec FB sh wd g) = 0 ∧ rDp (rec FB sh wd g) = D ∧
      DceS.stabGen FB sh wd NF D SG s = rPi (rec FB sh wd g) := by
  unfold DceS.stabGen
  beta_reduce
  generalize bits SG (Nat.add 5 (Nat.mul 20 s)) 20 = g
  cases hc : andB (Nat.blt s (Nat.land SG 31)) (andB (Nat.blt g NF)
      (andB (Nat.beq (rD (rec FB sh wd g)) D) (andB (Nat.beq (rJ (rec FB sh wd g)) 0)
        (Nat.beq (rDp (rec FB sh wd g)) D))))
  · exact Or.inl rfl
  · obtain ⟨-, r⟩ := andB_iff.1 hc
    obtain ⟨f1, r⟩ := andB_iff.1 r
    obtain ⟨f2, r⟩ := andB_iff.1 r
    obtain ⟨f3, f4⟩ := andB_iff.1 r
    exact Or.inr ⟨g, Nat.blt_eq.mp f1, Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3,
      Nat.eq_of_beq_eq_true f4, rfl⟩

section Stab

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {φ : M →* G} {HB GB FB : ℕ → ℕ}
  {ND NO sh wd NF : ℕ} {el : Bool} {N : Subgroup G} {u : G} (w : ℕ → G)
  (hfacts : ∀ i < NF, FOK N el φ HB GB u w ND NO (rec FB sh wd i))
include hfacts

theorem stab_sem {EB : ℕ → ℕ} {D SG m Y1 : ℕ} {Cs Ce : List ℕ}
    (h1 : DceS.stabStart EB = true) (h2 : DceS.runStab FB EB sh wd NF D SG Cs 2 = m + 1)
    (h3 : DceS.runSorted (mat EB) 17 m Ce 1 = Y1) (h4 : sortedCount Y1 = m) :
    ∃ E : ℕ → M, (∀ k < m, ∀ k' < m, E k = E k' → k = k') ∧
      ∀ k < m, w D * φ (E k) * (w D)⁻¹ ∈ N := by
  obtain ⟨hpos, hinj⟩ := sortRun_spec (runSorted_eq _ _ _ _ _ ▸ h3) h4
  have h0 : mat EB 0 = ident24 := Nat.eq_of_beq_eq_true h1
  rw [runStab_eq] at h2
  have hi := cntRun_spec (a := 1) h2
  have key : ∀ k < m, InM M (mat EB k) ∧ w D * rc φ (mat EB k) * (w D)⁻¹ ∈ N := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [h0]
        refine ⟨InM_one, ?_⟩
        rw [rc_one φ, mul_one, mul_inv_cancel]
        exact N.one_mem
      obtain ⟨J, hJ⟩ := hi k hk0 hk
      obtain ⟨e1, e2⟩ := andB_iff.1 hJ
      have hp : bits J 0 17 < k := Nat.blt_eq.mp e1
      have he : mat EB k = mul24 (mat EB (bits J 0 17))
          (DceS.stabGen FB sh wd NF D SG (bits J 17 5)) := Nat.eq_of_beq_eq_true e2
      obtain ⟨mp, np⟩ := ih _ hp (by omega)
      rcases stabGen_spec FB sh wd NF D SG (bits J 17 5) with h0' | ⟨g, hg, gD, gJ, gDp, hgv⟩
      · rw [h0', mul24_zero_right] at he
        have := hpos k hk
        rw [he] at this
        exact absurd this (Nat.lt_irrefl 0)
      · obtain ⟨-, gm', -, ν, hνN, -, hFM⟩ := hfacts g hg
        rw [hgv] at he
        rw [he]
        refine ⟨InM_mul mp gm', ?_⟩
        rw [rc_mul φ mp gm']
        unfold FMeq at hFM
        rw [gD, gJ, gDp, uv, ite_eq_left rfl, mul_one] at hFM
        have e3 : w D * (rc φ (mat EB (bits J 0 17)) * rc φ (rPi (rec FB sh wd g))) * (w D)⁻¹ =
            (w D * rc φ (mat EB (bits J 0 17)) * (w D)⁻¹) *
              (w D * rc φ (rPi (rec FB sh wd g)) * (w D)⁻¹) := by group
        have e4 : w D * rc φ (rPi (rec FB sh wd g)) * (w D)⁻¹ = ν⁻¹ := by
          calc w D * rc φ (rPi (rec FB sh wd g)) * (w D)⁻¹
              = ν⁻¹ * (ν * (w D * rc φ (rPi (rec FB sh wd g)))) * (w D)⁻¹ := by group
            _ = ν⁻¹ * w D * (w D)⁻¹ := by rw [← hFM]
            _ = ν⁻¹ := by group
        rw [e3, e4]
        exact N.mul_mem np (N.inv_mem hνN)
  refine ⟨fun k => mEl M (mat EB k), fun k hk k' hk' he => ?_, fun k hk => (key k hk).2⟩
  have he' : mEl M (mat EB k) = mEl M (mat EB k') := he
  have e2 : (((mEl M (mat EB k) : M) : Mat24ˣ) : Mat24) =
      (((mEl M (mat EB k') : M) : Mat24ˣ) : Mat24) := by rw [he']
  rw [mEl_val (key k hk).1, mEl_val (key k' hk').1] at e2
  exact hinj k hk k' hk' (eq_of_toMat_eq (mat_lt _ _) (mat_lt _ _) e2)

end Stab

theorem pt_lt {OB : ℕ → ℕ} {osh owd om NB : ℕ}
    (hom : om = Nat.sub (Nat.shiftLeft 1 (Nat.mul 24 NB)) 1) (w : ℕ) :
    pt OB osh owd om w < 2 ^ (24 * NB) := by
  unfold pt
  have e : om = 2 ^ (24 * NB) - 1 := by
    rw [hom]
    change (1 <<< (24 * NB)) - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  change rec OB osh owd w &&& om < 2 ^ (24 * NB)
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem MCtx.trivial {M : Subgroup Mat24ˣ} {LT LC LI TL VL NL : ℕ} (hL : LetOK LT LC LI TL VL NL)
    (hM : ∀ c, isN TL VL NL c = true → Lm LT LI TL VL NL c ∈ M) :
    MCtx M LT LC LI TL VL NL (fun _ => (1 : PUnit)) (1 : M →* PUnit) :=
  ⟨hL, hM, fun _ _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩

theorem relsNorm_mono {RR : ℕ → ℕ} : ∀ {n m : ℕ}, n ≤ m → CFSG.KC.relsNorm RR m = true →
    CFSG.KC.relsNorm RR n = true
  | n, m, hnm, h => by
    induction m with
    | zero =>
      have : n = 0 := by omega
      subst this
      exact h
    | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hnm) with h1 | h1
      · have h' : CFSG.KC.andB (CFSG.KC.relsNorm RR m) (Nat.blt (Nat.shiftRight (RR m) 12)
          (Nat.shiftLeft 1 (Nat.mul 8 (Nat.land (Nat.shiftRight (RR m) 2) 1023)))) = true := h
        exact ih (by omega) (andBK_iff.1 h').1
      · rw [h1]
        exact h

theorem tab_ep {HB TB OB RR FA : ℕ → ℕ} {Ct : List ℕ}
    {LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA : ℕ}
    (hT : runT HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA Ct 1 =
      nT + 1) : ∀ e < nT, ∃ ep < nT, tPsi HB TB e = tSig HB TB ep := by
  rw [runT_eq] at hT
  have hi := cntRun_spec (a := 0) hT
  intro e he
  obtain ⟨J, ht⟩ := hi e (Nat.zero_le _) he
  obtain ⟨-, -, hep, -⟩ := tOK_spec ht
  exact hep

end CFSG.KC.Th.Spec.Dce

end
