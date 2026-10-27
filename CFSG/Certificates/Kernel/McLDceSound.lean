module

public import CFSG.Certificates.Kernel.McL.Dce
public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.McLDceFacts
import CFSG.Certificates.Kernel.DceLoops
import CFSG.Certificates.Kernel.Co1DceLemmas
import Mathlib.Tactic.Group
import Mathlib.Data.Nat.Cast.Order.Ring

namespace CFSG.Certificates.McLD

open CFSG.KC CFSG.KC.McL.Mat CFSG.Certificates.LCE

set_option exponentiation.threshold 700

noncomputable def covStepM (FB OB : ℕ → ℕ) (NF NO AL : ℕ) (ih2 : ℕ → ℕ → ℕ) (J S : ℕ) : ℕ :=
  (fun D w => (fun nxt =>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (Bool.rec (motive := fun _ => Nat)
          (Loop.strictN nxt (ih2 J))
          (Loop.strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) nxt
              (McL.Dce.slotOK FB OB NF AL D w (McL.Dce.bits J (nat_lit 0) (nat_lit 21))))
            (ih2 (Nat.shiftRight J (nat_lit 21))))
          (McL.Dce.aliveD AL D))
        (Nat.blt (nat_lit 0) S))
      (Bool.rec (motive := fun _ => Nat) (Nat.add S (nat_lit 1))
        (Nat.add (nat_lit 1) (Nat.shiftLeft (Nat.succ D) (nat_lit 20)))
        (Th.orB (McL.Dce.notB (McL.Dce.aliveD AL D)) (Nat.beq (Nat.succ w) NO))))
    (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 20))
    (Nat.land (Nat.sub S (nat_lit 1)) McL.Dce.M20)

noncomputable def covInM (FB OB : ℕ → ℕ) (NF NO AL n J S : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih2 J S => covStepM FB OB NF NO AL ih2 J S) n J S

theorem runCover_eq (FB OB : ℕ → ℕ) (NF NO AL : ℕ) (Cs : List ℕ) (S : ℕ) :
    McL.Dce.runCover FB OB NF NO AL Cs S = List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
      (fun C _ ih S => Loop.strictN (covInM FB OB NF NO AL (Nat.land C (nat_lit 65535))
        (Nat.shiftRight C (nat_lit 16)) S) ih) Cs S := rfl

noncomputable def slotM (FB OB : ℕ → ℕ) (NF AL : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  fun D w x _ => McL.Dce.slotOK FB OB NF AL D w x

theorem covInM_inv {FB OB : ℕ → ℕ} {NF NO AL : ℕ} (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO) :
    ∀ (n J S : ℕ), DceLoop.CovInv (slotM FB OB NF AL) NO AL S →
      DceLoop.CovInv (slotM FB OB NF AL) NO AL (covInM FB OB NF NO AL n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change DceLoop.CovInv (slotM FB OB NF AL) NO AL
      (covStepM FB OB NF NO AL (covInM FB OB NF NO AL n) J S)
    have ih := covInM_inv (FB := FB) (OB := OB) (NF := NF) (AL := AL) hNO hNO0 n
    rcases h with rfl | ⟨D, w, rfl, hw, hw0, hprev, hcur⟩
    · exact Or.inl rfl
    obtain ⟨eD, ew⟩ := DceLoop.covDec (D := D) (Nat.lt_trans hw hNO)
    have ew' : Nat.land (Nat.sub (1 + 2 ^ 20 * D + w) (nat_lit 1)) McL.Dce.M20 = w := ew
    have hpos : Nat.blt (nat_lit 0) (1 + 2 ^ 20 * D + w) = true := by
      rw [Nat.blt_eq]
      exact Nat.lt_of_lt_of_le Nat.one_pos
        (Nat.le_add_right_of_le (Nat.le_add_right 1 (2 ^ 20 * D)))
    have hnext := DceLoop.covNext_inv (slot := slotM FB OB NF AL) hNO0 hw hw0 hprev hcur
    unfold covStepM
    simp only []
    rw [eD, ew', hpos]
    dsimp only
    cases ha : McL.Dce.aliveD AL D
    · have ha' : DceLoop.aliveG AL D = false := ha
      rw [ha'] at hnext
      dsimp only at hnext ⊢
      rw [strictN_eq]
      exact ih _ _ (hnext (fun hal => absurd ((DceLoop.aliveG_iff AL D).2 hal) (by rw [ha']; decide)))
    · have ha' : DceLoop.aliveG AL D = true := ha
      rw [ha'] at hnext
      dsimp only at hnext ⊢
      rw [strictN_eq]
      apply ih
      cases hs : McL.Dce.slotOK FB OB NF AL D w (McL.Dce.bits J (nat_lit 0) (nat_lit 21))
      · exact Or.inl rfl
      · dsimp only
        exact hnext (fun _ => ⟨_, 0, hs⟩)

theorem runCover_inv {FB OB : ℕ → ℕ} {NF NO AL : ℕ} (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO) :
    ∀ (Cs : List ℕ) (S : ℕ), DceLoop.CovInv (slotM FB OB NF AL) NO AL S →
      DceLoop.CovInv (slotM FB OB NF AL) NO AL (McL.Dce.runCover FB OB NF NO AL Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    rw [runCover_eq]
    change DceLoop.CovInv (slotM FB OB NF AL) NO AL (Loop.strictN (covInM FB OB NF NO AL
      (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S)
        (McL.Dce.runCover FB OB NF NO AL Cs))
    rw [strictN_eq]
    exact runCover_inv hNO hNO0 Cs _ (covInM_inv hNO hNO0 _ _ _ h)

theorem runCover_spec {FB OB : ℕ → ℕ} {NF NO AL ND : ℕ} {Cs : List ℕ} (hNO : NO < 2 ^ 20)
    (hNO0 : 0 < NO)
    (h : Nat.beq (McL.Dce.runCover FB OB NF NO AL Cs 1) (1 + ND * 2 ^ 20) = true) :
    ∀ D < ND, AL.testBit D = true → ∀ w < NO, ∃ x, McL.Dce.slotOK FB OB NF AL D w x = true := by
  have h1 : DceLoop.CovInv (slotM FB OB NF AL) NO AL 1 := Or.inr ⟨0, 0, rfl, hNO0, Or.inl rfl,
    fun D' hD' => absurd hD' (Nat.not_lt_zero _), fun w' hw' => absurd hw' (Nat.not_lt_zero _)⟩
  have hi := runCover_inv hNO hNO0 Cs 1 h1
  rw [Nat.eq_of_beq_eq_true h, show 1 + ND * 2 ^ 20 = 1 + 2 ^ 20 * ND + 0 by ring] at hi
  intro D hD hal w hw
  rcases hi with h0 | ⟨D1, w1, he, hw1, -, hprev, -⟩
  · omega
  obtain ⟨d1, -⟩ := DceLoop.covDec (D := ND) (w := 0) (by norm_num)
  obtain ⟨d3, -⟩ := DceLoop.covDec (D := D1) (Nat.lt_trans hw1 hNO)
  rw [he] at d1
  rw [d1] at d3
  subst d3
  obtain ⟨x, _, hx⟩ := hprev D hD hal w hw
  exact ⟨x, hx⟩

theorem slotOK_spec {FB OB : ℕ → ℕ} {NF AL D w x : ℕ}
    (h : McL.Dce.slotOK FB OB NF AL D w x = true) : ∃ g < NF,
    (McL.Dce.rD (fR FB g) = D ∧ McL.Dce.rJ (fR FB g) = w + 1 ∧
        McL.Dce.aliveD AL (McL.Dce.rDp (fR FB g)) = true) ∨
      (McL.Dce.rDp (fR FB g) = D ∧ 0 < McL.Dce.rJ (fR FB g) ∧
        McL.Dce.aliveD AL (McL.Dce.rD (fR FB g)) = true ∧
        vecmul (McL.Dce.pt OB w) (McL.Dce.rPi (fR FB g)) =
          McL.Dce.pt OB (McL.Dce.rJ (fR FB g) - 1)) := by
  unfold McL.Dce.slotOK at h
  beta_reduce at h
  rw [andB_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨_, h1, ?_⟩
  cases hb : Nat.beq (Nat.land x 1) 1
  · simp only [hb, andB_iff, Nat.beq_eq] at h2
    exact Or.inl h2
  · simp only [hb, andB_iff, Nat.beq_eq, Nat.blt_eq] at h2
    exact Or.inr h2

theorem sumOK_eq (AL MD ND NORD SUM : ℕ) :
    McL.Dce.sumOK AL MD ND NORD SUM = DceLoop.sumG AL MD ND NORD SUM := rfl

theorem mDG_eq (MD D : ℕ) : McL.Dce.bits MD (20 * D) 20 = DceLoop.mDG MD D := rfl

theorem stabGen_spec {FB : ℕ → ℕ} {NF D SG s : ℕ} : McL.Dce.stabGen FB NF D SG s = 0 ∨
    ∃ g < NF, McL.Dce.rD (fR FB g) = D ∧ McL.Dce.rJ (fR FB g) = 0 ∧ McL.Dce.rDp (fR FB g) = D ∧
      McL.Dce.stabGen FB NF D SG s = McL.Dce.rPi (fR FB g) := by
  have e : McL.Dce.stabGen FB NF D SG s = Bool.rec (motive := fun _ => ℕ) 0
      (McL.Dce.rPi (fR FB (McL.Dce.bits SG (5 + 20 * s) 20)))
      (Th.andB (Nat.blt s (Nat.land SG 31)) (Th.andB (Nat.blt (McL.Dce.bits SG (5 + 20 * s) 20) NF)
        (Th.andB (Nat.beq (McL.Dce.rD (fR FB (McL.Dce.bits SG (5 + 20 * s) 20))) D)
          (Th.andB (Nat.beq (McL.Dce.rJ (fR FB (McL.Dce.bits SG (5 + 20 * s) 20))) 0)
            (Nat.beq (McL.Dce.rDp (fR FB (McL.Dce.bits SG (5 + 20 * s) 20))) D))))) := rfl
  rw [e]
  generalize McL.Dce.bits SG (5 + 20 * s) 20 = g
  cases hc : Th.andB (Nat.blt s (Nat.land SG 31)) (Th.andB (Nat.blt g NF)
      (Th.andB (Nat.beq (McL.Dce.rD (fR FB g)) D) (Th.andB (Nat.beq (McL.Dce.rJ (fR FB g)) 0)
        (Nat.beq (McL.Dce.rDp (fR FB g)) D))))
  · exact Or.inl rfl
  · simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at hc
    exact Or.inr ⟨g, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, rfl⟩

section Hold

variable {G : Type*} [Group G] {gen : ℕ → G} {LT LI TL NL : ℕ} (φ : Mg LT TL NL →* G)
  {FB HB GB TB OB : ℕ → ℕ} {ND NO nT NF AL : ℕ}

theorem stabD_of (hφN : ∀ m, φ m ∈ Nsub gen) {w : ℕ → G}
    (hF : ∀ h < NF, FOK φ gen HB GB ND NO w (fR FB h)) {EB : ℕ → ℕ} {D SG qb m Y1 : ℕ}
    {Cs Ce : List ℕ} (h1 : McL.Dce.stabStart EB = true)
    (h2 : Nat.beq (McL.Dce.runStab FB EB NF D SG Cs 2) (m + 1) = true)
    (h3 : Nat.beq (McL.Dce.runSorted (McL.Dce.mat EB) qb m Ce 1) Y1 = true)
    (h4 : Nat.beq (McL.Dce.sortedCount Y1) m = true) :
    ∃ E : ℕ → Mg LT TL NL, (∀ k < m, ∀ k' < m, E k = E k' → k = k') ∧
      ∀ k < m, w D * φ (E k) * (w D)⁻¹ ∈ Nsub gen := by
  obtain ⟨hpos, hinj⟩ := runSorted_spec h3 h4
  have e : McL.Dce.runStab FB EB NF D SG Cs 2 = DceLoop.cntRun (fun k J => Th.andB
      (Nat.blt (McL.Dce.bits J 0 17) k) (Nat.beq (McL.Dce.mat EB k)
        (mul25 (McL.Dce.mat EB (McL.Dce.bits J 0 17)) (McL.Dce.stabGen FB NF D SG (McL.Dce.bits J 17 5)))))
      (fun _ => 22) 65535 16 Cs (1 + 1) := rfl
  rw [e] at h2
  have hok := DceLoop.cntRun_spec (Nat.eq_of_beq_eq_true h2)
  have h0 : McL.Dce.mat EB 0 = ident := Nat.eq_of_beq_eq_true h1
  have key : ∀ k < m, InM LT TL NL (McL.Dce.mat EB k) ∧
      w D * rc φ (McL.Dce.mat EB k) * (w D)⁻¹ ∈ Nsub gen := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [h0, rc_ident, mul_one, mul_inv_cancel]
        exact ⟨InM_ident, (Nsub gen).one_mem⟩
      obtain ⟨J, hJ⟩ := hok k hk1 hk
      simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at hJ
      obtain ⟨hp, hE⟩ := hJ
      generalize McL.Dce.bits J 0 17 = p at hp hE
      obtain ⟨hp1, hp2⟩ := ih p hp (by omega)
      rcases stabGen_spec (FB := FB) (NF := NF) (D := D) (SG := SG) (s := McL.Dce.bits J 17 5) with
        hz | ⟨g, hg, hd1, hd2, hd3, hsg⟩
      · rw [hz, mul25_zero_r] at hE
        exact absurd hE (Nat.ne_of_gt (hpos k hk))
      rw [hsg] at hE
      obtain ⟨-, hRP, -, hFM⟩ := hF g hg
      unfold FM tvJ at hFM
      rw [hd1, hd2, hd3, ite_eq_left rfl] at hFM
      rw [hE]
      refine ⟨InM_mul hp1 hRP, ?_⟩
      rw [rc_mul φ hp1 hRP]
      have hn := rc_mem φ hφN (McL.Dce.rN (fR FB g))
      generalize rc φ (McL.Dce.rPi (fR FB g)) = πv at hFM ⊢
      generalize rc φ (McL.Dce.rN (fR FB g)) = nv at hFM hn
      generalize rc φ (McL.Dce.mat EB p) = ev at hp2 ⊢
      have k1 : w D * (ev * πv) * (w D)⁻¹ =
          (w D * ev * (w D)⁻¹) * (nv⁻¹ * (nv * w D * πv) * (w D)⁻¹) := by group
      rw [k1, ← hFM]
      refine (Nsub gen).mul_mem hp2 ?_
      have k2 : nv⁻¹ * (w D * 1) * (w D)⁻¹ = nv⁻¹ := by group
      rw [k2]
      exact (Nsub gen).inv_mem hn
  refine ⟨fun k => mE LT TL NL (McL.Dce.mat EB k), fun k hk k' hk' he => ?_, fun k hk => ?_⟩
  · beta_reduce at he
    have a1 := mE_val (key k hk).1
    have a2 := mE_val (key k' hk').1
    rw [he] at a1
    exact hinj k hk k' hk' (eq_of_toMat_eq (mat_lt _ _) (mat_lt _ _) (a1.symm.trans a2))
  · beta_reduce
    rw [← rc_mE φ (key k hk).1]
    exact (key k hk).2

theorem cover_of
    (hG : ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
      mul25 (gL HB GB j) (gH HB GB j) = ident)
    (hφN : ∀ m, φ m ∈ Nsub gen) {w : ℕ → G}
    (hF : ∀ h < NF, FOK φ gen HB GB ND NO w (fR FB h)) (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO)
    {Cc : List ℕ} (hcov : Nat.beq (McL.Dce.runCover FB OB NF NO AL Cc 1) (1 + ND * 2 ^ 20) = true) :
    ∀ D ∈ (Finset.range ND).filter (fun D => AL.testBit D = true), ∀ j < NO,
      (∃ D' ∈ (Finset.range ND).filter (fun D => AL.testBit D = true), ∃ π : Mg LT TL NL,
        w D * ((φ (gE LT TL NL HB GB j))⁻¹ * gen TL * φ (gE LT TL NL HB GB j)) * (w D' * φ π)⁻¹ ∈
          Nsub gen) ∨
      (∃ D' ∈ (Finset.range ND).filter (fun D => AL.testBit D = true), ∃ j' < NO,
        ∃ π : Mg LT TL NL, actV (toVec (McL.Dce.pt OB j)) (π : Mat25ˣ) = toVec (McL.Dce.pt OB j') ∧
        w D' * ((φ (gE LT TL NL HB GB j'))⁻¹ * gen TL * φ (gE LT TL NL HB GB j')) * (w D * φ π)⁻¹ ∈
          Nsub gen) := by
  intro D hD j hj
  rw [Finset.mem_filter, Finset.mem_range] at hD
  obtain ⟨x, hx⟩ := runCover_spec hNO hNO0 hcov D hD.1 hD.2 j hj
  obtain ⟨g, hg, hfb⟩ := slotOK_spec hx
  obtain ⟨hr, hRP, -, hFM⟩ := hF g hg
  obtain ⟨hD1, hD2, hJ, -, -⟩ := recOK_spec hr
  have hn := rc_mem φ hφN (McL.Dce.rN (fR FB g))
  generalize fR FB g = R at hfb hRP hFM hD1 hD2 hJ hn
  have hgj : ∀ j < NO, φ (gE LT TL NL HB GB j) = rc φ (gL HB GB j) := fun j hj =>
    (rc_mE φ (hG j hj).1).symm
  have hπ : φ (mE LT TL NL (McL.Dce.rPi R)) = rc φ (McL.Dce.rPi R) := (rc_mE φ hRP).symm
  unfold FM tvJ at hFM
  rcases hfb with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, e4⟩
  · left
    refine ⟨McL.Dce.rDp R, ?_, mE LT TL NL (McL.Dce.rPi R), ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hD2, (DceLoop.aliveG_iff _ _).1 e3⟩
    · rw [e1, e2, ite_eq_right (by omega), Nat.add_sub_cancel] at hFM
      rw [hgj j hj, hπ, hFM]
      have k : rc φ (McL.Dce.rN R) * w (McL.Dce.rDp R) * rc φ (McL.Dce.rPi R) *
          (w (McL.Dce.rDp R) * rc φ (McL.Dce.rPi R))⁻¹ = rc φ (McL.Dce.rN R) := by group
      rw [k]
      exact hn
  · right
    refine ⟨McL.Dce.rD R, ?_, McL.Dce.rJ R - 1, by omega, mE LT TL NL (McL.Dce.rPi R), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hD1, (DceLoop.aliveG_iff _ _).1 e3⟩
    · rw [← toVec_vecmul_actV (mE_val hRP), e4]
    · rw [e1, ite_eq_right (by omega)] at hFM
      rw [hgj _ (by omega), hπ, hFM]
      have k : rc φ (McL.Dce.rN R) * w D * rc φ (McL.Dce.rPi R) *
          (w D * rc φ (McL.Dce.rPi R))⁻¹ = rc φ (McL.Dce.rN R) := by group
      rw [k]
      exact hn

noncomputable def tGo (FB HB GB TB : ℕ → ℕ) (LT TL NL nT NF Wd n k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ)
    (fun _ S A => Nat.lor S (Nat.shiftLeft A 640))
    (fun k ih J S A => (fun c =>
        Bool.rec (motive := fun _ => ℕ)
          (ih J (McL.Dce.mkSt (McL.Dce.sD S) (mul25 (McL.Dce.sPi S) (McL.Dce.let25 LT c))) A)
          ((fun h => (fun R dir => Bool.rec (motive := fun _ => ℕ) McL.Dce.bad
              (Loop.strictN (McL.Dce.stepL HB GB TB TL nT c R dir (McL.Dce.bits J 21 17) S)
                (fun S2 => ih (Nat.shiftRight J 38) S2
                  (mul25 A (Bool.rec (motive := fun _ => ℕ) (McL.Dce.rN R) (McL.Dce.rNI R)
                    (Nat.beq dir 1)))))
              (Th.andB (Nat.blt h NF) (Nat.beq c TL)))
            (McL.Dce.rec FB 6 McL.Dce.RW h) (Nat.land J 1))
            (McL.Dce.bits J 1 20))
          (McL.Dce.notB (McL.Dce.isN TL NL c)))
      (McL.Dce.byte Wd (Nat.sub n (Nat.succ k)))) k

theorem tGo_succ (FB HB GB TB : ℕ → ℕ) (LT TL NL nT NF Wd n k J S A : ℕ) :
    tGo FB HB GB TB LT TL NL nT NF Wd n (k + 1) J S A =
      Bool.rec (motive := fun _ => ℕ)
        (tGo FB HB GB TB LT TL NL nT NF Wd n k J (McL.Dce.mkSt (McL.Dce.sD S)
          (mul25 (McL.Dce.sPi S) (McL.Dce.let25 LT (McL.Dce.byte Wd (n - (k + 1)))))) A)
        (Bool.rec (motive := fun _ => ℕ) McL.Dce.bad
          (Loop.strictN (McL.Dce.stepL HB GB TB TL nT (McL.Dce.byte Wd (n - (k + 1)))
              (fR FB (McL.Dce.bits J 1 20)) (Nat.land J 1) (McL.Dce.bits J 21 17) S)
            (fun S2 => tGo FB HB GB TB LT TL NL nT NF Wd n k (Nat.shiftRight J 38) S2
              (mul25 A (mR (fR FB (McL.Dce.bits J 1 20)) (Nat.land J 1)))))
          (Th.andB (Nat.blt (McL.Dce.bits J 1 20) NF) (Nat.beq (McL.Dce.byte Wd (n - (k + 1))) TL)))
        (McL.Dce.notB (McL.Dce.isN TL NL (McL.Dce.byte Wd (n - (k + 1))))) := rfl

def TInv (w : ℕ → G) (Wd q S A : ℕ) : Prop :=
  S < 2 ^ 640 ∧ (McL.Dce.sPi S = 0 ∨ InM LT TL NL (McL.Dce.sPi S) ∧ InM LT TL NL A ∧
    Ev φ w S A = wv gen Wd q)

def TEnd (Wd n R : ℕ) : Prop :=
  McL.Dce.sD (Nat.land R (Nat.sub (Nat.shiftLeft 1 640) 1)) = 0 →
    mul25 (Nat.shiftRight R 640) (McL.Dce.sPi (Nat.land R (Nat.sub (Nat.shiftLeft 1 640) 1))) = ident →
      wv gen Wd n = 1

theorem dec_lo {S A : ℕ} (hS : S < 2 ^ 640) :
    Nat.land (Nat.lor S (Nat.shiftLeft A 640)) (Nat.sub (Nat.shiftLeft 1 640) 1) = S := by
  rw [Co1D.lor_shl hS]
  change (S + A * 2 ^ 640) &&& (1 <<< 640 - 1) = S
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hS]

theorem dec_hi {S A : ℕ} (hS : S < 2 ^ 640) : Nat.shiftRight (Nat.lor S (Nat.shiftLeft A 640)) 640 = A := by
  rw [Co1D.lor_shl hS]
  change (S + A * 2 ^ 640) >>> 640 = A
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 640), Nat.div_eq_of_lt hS,
    Nat.zero_add]

theorem ev_step {a m x p l y q : G} (h : x * p * l = m * y * q) : a * m * (y * q) = a * (x * p) * l := by
  calc a * m * (y * q) = a * (m * y * q) := by group
    _ = a * (x * p * l) := by rw [h]
    _ = a * (x * p) * l := by group

theorem tGo_spec (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    (hφ : ∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c)
    (hG : ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
      mul25 (gL HB GB j) (gH HB GB j) = ident)
    (hS : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) ∧
      gen TL * rc φ (McL.Dce.tSig HB TB e) * gen TL = rc φ (tPsi HB TB e))
    (ht : gen TL * gen TL = 1) {w : ℕ → G} (hw0 : w 0 = 1)
    (hF : ∀ h < NF, FOK φ gen HB GB ND NO w (fR FB h)) (Wd n : ℕ) :
    ∀ k, k ≤ n → ∀ J S A, TInv φ (gen := gen) w Wd (n - k) S A →
      TEnd (gen := gen) Wd n (tGo FB HB GB TB LT TL NL nT NF Wd n k J S A) := by
  have hS2 : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) :=
    fun e he => ⟨(hS e he).1, (hS e he).2.1⟩
  have hT255 : TL ≠ 255 := by omega
  intro k
  induction k with
  | zero =>
    intro _ J S A hinv
    obtain ⟨hSlt, hI⟩ := hinv
    unfold TEnd
    intro h1 h2
    have e : tGo FB HB GB TB LT TL NL nT NF Wd n 0 J S A = Nat.lor S (Nat.shiftLeft A 640) := rfl
    rw [e, dec_lo hSlt] at h1 h2
    rw [dec_hi hSlt] at h2
    rcases hI with h0 | ⟨hP, hA, hEv⟩
    · rw [h0, mul25_zero_r] at h2
      exact absurd h2.symm ident_ne_zero
    · rw [Nat.sub_zero] at hEv
      rw [← hEv]
      unfold Ev
      rw [h1, hw0, one_mul, ← rc_mul φ hA hP, h2, rc_ident]
  | succ k ih =>
    intro hk J S A hinv
    have hq : n - k = n - (k + 1) + 1 := by omega
    have ih' := ih (by omega)
    obtain ⟨hSlt, hI⟩ := hinv
    rw [tGo_succ]
    cases hN : McL.Dce.isN TL NL (McL.Dce.byte Wd (n - (k + 1)))
    · dsimp only [McL.Dce.notB]
      cases hg : Th.andB (Nat.blt (McL.Dce.bits J 1 20) NF)
          (Nat.beq (McL.Dce.byte Wd (n - (k + 1))) TL)
      · dsimp only
        unfold TEnd
        intro h1
        exact absurd h1 (by decide +kernel)
      · dsimp only
        rw [strictN_eq]
        apply ih'
        rw [hq]
        rw [andB_iff, Nat.blt_eq] at hg
        obtain ⟨hr, hRP, hRN, hFM⟩ := hF _ hg.1
        obtain ⟨-, -, hJ, hPF, hNN⟩ := recOK_spec hr
        unfold TInv
        rcases @stepL_cases HB GB TB TL nT (McL.Dce.byte Wd (n - (k + 1)))
            (fR FB (McL.Dce.bits J 1 20)) (Nat.land J 1) (McL.Dce.bits J 21 17) S with e1 | e1
        · rw [e1]
          exact ⟨by change 255 < 2 ^ 640; norm_num, Or.inl sPi_bad⟩
        · refine ⟨LStep_lt e1, ?_⟩
          rcases hI with h0 | ⟨hP, hA, hEv⟩
          · exact Or.inl (step_zero hS2 e1 h0)
          · obtain ⟨hP', hiff⟩ := step_mean hG hS ht hT255 (w := w) e1 hJ hPF hNN hRP hRN hP
            have hm := mR_inM (dir := Nat.land J 1) hRN hNN
            refine Or.inr ⟨hP', InM_mul hA hm, ?_⟩
            have hsr := hiff.2 hFM
            unfold SR at hsr
            rw [wv_succ, ← hEv]
            unfold Ev
            rw [rc_mul φ hA hm]
            exact ev_step hsr
    · dsimp only [McL.Dce.notB]
      apply ih'
      rw [hq]
      have hc := isN_iff.1 hN
      have h3 : McL.Dce.byte Wd (n - (k + 1)) < 3 := by omega
      have hL := InM_letter hTL hNL hlet h3
      unfold TInv
      refine ⟨mkSt_lt (sD_lt _) (mul25_lt _ _), ?_⟩
      rcases hI with h0 | ⟨hP, hA, hEv⟩
      · left
        rw [sPi_mkSt (sD_lt _), h0, mul25_zero_left]
      · right
        refine ⟨by rw [sPi_mkSt (sD_lt _)]; exact InM_mul hP hL, hA, ?_⟩
        rw [wv_succ, ← hEv]
        unfold Ev lv
        rw [sD_mkSt (sD_lt _), sPi_mkSt (sD_lt _), rc_mul φ hP hL, rc_letter φ hφ hTL hNL hlet h3,
          ite_eq_right (by omega)]
        group

theorem trace_one (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    (hφ : ∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c)
    (hG : ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
      mul25 (gL HB GB j) (gH HB GB j) = ident)
    (hS : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) ∧
      gen TL * rc φ (McL.Dce.tSig HB TB e) * gen TL = rc φ (tPsi HB TB e))
    (ht : gen TL * gen TL = 1) {w : ℕ → G} (hw0 : w 0 = 1)
    (hF : ∀ h < NF, FOK φ gen HB GB ND NO w (fR FB h)) {Wd n J : ℕ}
    (h : McL.Dce.traceOK FB HB GB TB LT TL NL nT NF Wd n J = true) : wv gen Wd n = 1 := by
  have e : McL.Dce.traceOK FB HB GB TB LT TL NL nT NF Wd n J = Th.andB
      (Nat.beq (McL.Dce.sD (Nat.land (tGo FB HB GB TB LT TL NL nT NF Wd n n J (McL.Dce.mkSt 0 ident)
        ident) (Nat.sub (Nat.shiftLeft 1 640) 1))) 0)
      (Nat.beq (mul25 (Nat.shiftRight (tGo FB HB GB TB LT TL NL nT NF Wd n n J
        (McL.Dce.mkSt 0 ident) ident) 640) (McL.Dce.sPi (Nat.land (tGo FB HB GB TB LT TL NL nT NF
          Wd n n J (McL.Dce.mkSt 0 ident) ident) (Nat.sub (Nat.shiftLeft 1 640) 1)))) ident) := rfl
  rw [e, andB_iff, Nat.beq_eq, Nat.beq_eq] at h
  have hI : TInv φ (gen := gen) w Wd (n - n) (McL.Dce.mkSt 0 ident) ident := by
    unfold TInv
    refine ⟨mkSt_lt (by norm_num) ident_lt, Or.inr ⟨?_, InM_ident, ?_⟩⟩
    · rw [sPi_mkSt (D := 0) (by norm_num)]
      exact InM_ident
    · unfold Ev
      rw [sD_mkSt (D := 0) (by norm_num), sPi_mkSt (D := 0) (by norm_num), hw0, rc_ident,
        Nat.sub_self, wv_zero]
      group
  exact tGo_spec φ hTL hNL hlet hφ hG hS ht hw0 hF Wd n n le_rfl J _ _ hI h.1 h.2

end Hold

end CFSG.Certificates.McLD

public section

namespace CFSG.Certificates.McLD

open CFSG.KC CFSG.KC.McL.Mat CFSG.Certificates.LCE

@[expose] noncomputable def ival {G : Type*} [Group G] (gen : ℕ → G) (W n : ℕ) : G :=
  ((List.range n).map fun i => if wLet W i = 255 then 1 else gen (wLet W i)).prod

theorem dce_sound {G : Type*} [Group G] (gen : ℕ → G)
    {FB HB GB TB OB WD RR NRN : ℕ → ℕ}
    {LT LI TL NL ND NO NF nH nT nW NR nRN I0 AL MD NORD SUM WH qT qO hT : ℕ}
    {h0 h1 g0 g1 p0 p1 s0 sT o0 sO f0 f1 c0 c1 : ℕ} {Ch Cg Ct Cts Cos Cf Cc : List ℕ}
    (hTL : TL = 3) (hNL : NL = 4) (hND : ND ≤ 256) (hNO : NO < 65535) (hnH : nH < 2 ^ 20)
    (hnT : nT < 2 ^ 17) (hNF : NF < 2 ^ 20) (hnW : nW < 2 ^ 16)
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch h0) h1 = true) (hh0 : h0 = 1)
    (hh1 : h1 = nH + 1)
    (hgom : Nat.beq (McL.Dce.runGom HB GB OB I0 nH Cg g0) g1 = true) (hg0 : g0 = 1)
    (hg1 : g1 = NO + 1)
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct p0) p1 = true)
    (hp0 : p0 = 1) (hp1 : p1 = nT + 1)
    (hTS : Nat.beq (McL.Dce.runSorted (McL.Dce.tSig HB TB) qT nT Cts s0) sT = true)
    (hs0 : s0 = 1) (hTSn : Nat.beq (McL.Dce.sortedCount sT) nT = true)
    (hOS : Nat.beq (McL.Dce.runSorted (McL.Dce.pt OB) qO NO Cos o0) sO = true)
    (ho0 : o0 = 1) (hOSn : Nat.beq (McL.Dce.sortedCount sO) NO = true)
    (hfacts : Nat.beq (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW Cf f0) f1 = true)
    (hf0 : f0 = McL.Dce.mkS 0 1) (hf1 : f1 = McL.Dce.mkS NF ND)
    (hcov : Nat.beq (McL.Dce.runCover FB OB NF NO AL Cc c0) c1 = true) (hc0 : c0 = 1)
    (hc1 : c1 = 1 + ND * 2 ^ 20)
    (hstab : ∀ D < ND, McL.Dce.aliveD AL D = true → D ≠ 0 →
      ∃ (EB : ℕ → ℕ) (D' SG qb m X0 X1 Y0 Y1 : ℕ) (Cs Ce : List ℕ),
        McL.Dce.stabStart EB = true ∧ Nat.beq (McL.Dce.runStab FB EB NF D' SG Cs X0) X1 = true ∧
        Nat.beq (McL.Dce.runSorted (McL.Dce.mat EB) qb m Ce Y0) Y1 = true ∧
        Nat.beq (McL.Dce.sortedCount Y1) m = true ∧ D' = D ∧ X0 = 2 ∧ X1 = m + 1 ∧ Y0 = 1 ∧
        McL.Dce.bits MD (20 * D) 20 = m)
    (hlet : McL.Dce.lettersOK LT LI TL NL = true) (hrels : McL.Dce.relsOK RR NL NR = true)
    (hRRc : relsNorm RR NR = true)
    (hwords : McL.Dce.wordsOK WD RR LI NL NR WH nW = true)
    (htsq : McL.Dce.tsqOK RR TL NR hT = true)
    (hnrel : McL.Dce.nRelsHold LT NRN TL NL nRN = true)
    (hI0 : I0 < NO) (hT5 : nT * NO = NORD) (hsum : McL.Dce.sumOK AL MD ND NORD SUM = true)
    (hRR : ∀ r < NR, ival gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1)
    (hNRN : ∀ r < nRN, bval gen (LceS.wWord (NRN r)) (LceS.wLen (NRN r)) = 1)
    (hN : ∀ (H : Type) [Group H] (z : ℕ → H),
      (∀ r < nRN, bval z (LceS.wWord (NRN r)) (LceS.wLen (NRN r)) = 1) →
        Nat.card (Subgroup.closure (z '' {i | i < 3})) ≠ 0 ∧
          Nat.card (Subgroup.closure (z '' {i | i < 3})) ≤ NORD) :
    Nat.card (Subgroup.closure (gen '' {c | c < NL})) ≠ 0 ∧
      Nat.card (Subgroup.closure (gen '' {c | c < NL})) ≤ NORD * SUM ∧
      ∀ Wd n J, McL.Dce.traceOK FB HB GB TB LT TL NL nT NF Wd n J = true → ival gen Wd n = 1 := by
  subst hh0 hh1 hg0 hg1 hp0 hp1 hs0 ho0 hf0 hf1 hc0 hc1
  have hsum' : DceLoop.sumG AL MD ND NORD SUM = true := by rw [← sumOK_eq]; exact hsum
  obtain ⟨hA0, hAL, hmD, hSUM⟩ := DceLoop.sumG_spec hsum'
  have hND0 : 0 < ND := by
    rcases Nat.eq_zero_or_pos ND with h | h
    · subst h
      have h1 : AL = 0 := by
        rw [pow_zero] at hAL
        omega
      rw [h1, Nat.zero_testBit] at hA0
      exact absurd hA0 Bool.false_ne_true
    · exact h
  have hRR' : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1 := hRR
  have hM := card_Mg hNL hlet hnrel hN
  have hMe := card_Mg_eq hTL hNL hlet hhdr hgom hpsi hTS hTSn hOS hOSn hI0 hT5 hM
  obtain ⟨φ, hφ, hφN, hNφ⟩ := model_hom gen hNL hlet hnrel hNRN hN hMe.ge
  have ht := tsq_gen hTL htsq hRR'
  have hH := hdr_mem hTL hNL hlet hhdr
  have hG := hG_of hTL hNL hlet hhdr hgom
  have hS := hS_of φ hTL hNL hlet hφ hhdr hpsi htsq hRRc hRR'
  have hW := fun w hw => (words_one φ hφ hTL hNL hlet htsq hRRc hRR' hwords w hw).2
  obtain ⟨w, hw0, hF⟩ := facts_hold φ hTL hNL hlet hφ hH hG hS ht hND hND0 hW hNF hfacts
  have hNO20 : NO < 2 ^ 20 := Nat.lt_trans hNO (by norm_num)
  have hNO0 : 0 < NO := by omega
  have hyp : DceTw.Hyp (Nsub gen) (gen TL) (Mg LT TL NL) φ NORD (Fin 25 → ZMod 2) actV
      (toVec (McL.Dce.pt OB I0)) (fun j => toVec (McL.Dce.pt OB j)) (gE LT TL NL HB GB) NO I0
      (sigE LT TL NL HB TB) nT w ((Finset.range ND).filter (fun D => AL.testBit D = true))
      (DceLoop.mDG MD) :=
    { φN := hφN
      Nφ := hNφ
      orb := orb_hyp hTL hNL hlet hhdr hgom hpsi hTS hTSn hOS hOSn hI0 hT5 hM
      psi := psi_hyp φ hφ hTL hNL hlet hhdr hpsi htsq hRRc hRR'
      usq := usq_hyp φ hTL htsq hRR'
      zero_mem := Finset.mem_filter.2 ⟨Finset.mem_range.2 hND0, hA0⟩
      w_zero := hw0
      cover := cover_of φ hG hφN hF hNO20 hNO0 hcov
      mD_dvd := fun D hD hD0 => by
        rw [Finset.mem_filter, Finset.mem_range] at hD
        exact (hmD D hD.1 hD.2 hD0).2
      stabD := fun D hD hD0 => by
        rw [Finset.mem_filter, Finset.mem_range] at hD
        obtain ⟨EB, D', SG, qb, m, X0, X1, Y0, Y1, Cs, Ce, h1, h2, h3, h4, rfl, rfl, rfl, rfl, h9⟩ :=
          hstab D hD.1 ((DceLoop.aliveG_iff _ _).2 hD.2) hD0
        right
        have hm : DceLoop.mDG MD D' = m := by rw [← mDG_eq]; exact h9
        rw [hm]
        exact stabD_of φ hφN hF h1 h2 h3 h4 }
  obtain ⟨hfin, hcard⟩ := DceTw.dceTw_bound hyp (gen '' {c | c < NL}) (gens_hX hTL hNL)
  have hset : ((Finset.range ND).filter (fun D => AL.testBit D = true)).erase 0 =
      DceLoop.aliveSet AL ND := by
    ext D
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, DceLoop.aliveSet]
    tauto
  rw [hset, ← hSUM] at hcard
  refine ⟨(Nat.card_pos_iff.2 ⟨inferInstance, hfin⟩).ne', hcard, fun Wd n J hJ => ?_⟩
  exact trace_one φ hTL hNL hlet hφ hG hS ht hw0 hF hJ

end CFSG.Certificates.McLD

end
