module

public import CFSG.Certificates.Kernel.DceSPPerm
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.DSP

open CFSG.KC.Loop CFSG.KC.HNA.DceS CFSG.Certificates.DceLoop

@[expose] noncomputable def rval {G : Type*} [Group G] (x : ℕ → G) (e : ℕ) : G :=
  ((List.range (bits e 2 10)).map fun i => x (byte (Nat.shiftRight e 12) i)).prod

@[expose] def nOnly (TL VL NL e : ℕ) : Prop :=
  ∀ i < bits e 2 10, isN TL VL NL (byte (Nat.shiftRight e 12) i) = true

theorem runHdr_eq (HB : ℕ → ℕ) (LT TL VL NL : ℕ) (Cs : List ℕ) (S : ℕ) :
    runHdr HB LT TL VL NL Cs S = cntRun (fun k J => hdrOK HB LT TL VL NL k (bits J 0 43))
      (fun _ => 43) 255 8 Cs S := rfl

theorem runT_eq (TB OB RR : ℕ → ℕ) (LT TL VL NL NR nT I0 : ℕ) (Cs : List ℕ) (S : ℕ) :
    runT TB OB RR LT TL VL NL NR nT I0 Cs S = cntRun
      (fun k J => tOK TB OB RR LT TL VL NL NR nT I0 k (bits J 0 59)) (fun _ => 59) 65535 16 Cs S := rfl

theorem runStab_eq (FB EB : ℕ → ℕ) (sh wd NF D SG : ℕ) (Cs : List ℕ) (S : ℕ) :
    runStab FB EB sh wd NF D SG Cs S = cntRun
      (fun k J => andB (Nat.blt (bits J 0 19) k)
        (Nat.beq (mat EB k) (mulP (mat EB (bits J 0 19)) (stabGen FB sh wd NF D SG (bits J 19 5)))))
      (fun _ => 24) 65535 16 Cs S := rfl

theorem runSorted_eq (get : ℕ → ℕ) (qb m : ℕ) (Cs : List ℕ) (S : ℕ) :
    runSorted get qb m Cs S = sortRun get qb m Cs S := rfl

theorem runFacts_eq (FB HB GB TB WD : ℕ → ℕ) (sh wd LT TL VL NL ND NO nH nT nW W Wi : ℕ)
    (Cs : List ℕ) (S : ℕ) :
    runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi Cs S =
      factsG (factG (recOK ND NO) (treeOK HB GB) (axiomOK HB nH)
        (fun i Jf R => walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi i Jf R)
        (rec FB sh wd)) Cs S := rfl

theorem walkGo_eq (FB HB GB TB : ℕ → ℕ) (sh wd LT TL VL NL nT W Wi i Ri ft fd Wd n k J S : ℕ) :
    walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi i Ri ft fd Wd n k J S =
      walkG (isN TL VL NL) (isUL TL VL) (fun S c => mkSt (sD S) (mulP (sPi S) (letP LT c)))
        (fun c R dir e S => stepL HB GB TB TL VL nT W Wi c R dir e S) (rec FB sh wd) bad
        i Ri ft fd Wd n k J S := rfl

@[expose] noncomputable def gomInner (ok : ℕ → Bool) (n S : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun _ ih2 S => strictN (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.succ S)
        (andB (Nat.blt (nat_lit 0) S) (ok (Nat.sub S (nat_lit 1))))) ih2) n S

@[expose] noncomputable def gomRun (ok : ℕ → Bool) (Cs : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => strictN (gomInner ok C S) ih) Cs

theorem runGom_eq (HB GB OB : ℕ → ℕ) (I0 nH : ℕ) (Cs : List ℕ) (S : ℕ) :
    runGom HB GB OB I0 nH Cs S = gomRun (fun j => gomOK HB GB OB I0 nH j) Cs S := rfl

theorem gomInner_ok (ok : ℕ → Bool) : ∀ (n S : ℕ), (∀ k, k + 1 < S → ok k = true) →
    ∀ k, k + 1 < gomInner ok n S → ok k = true
  | 0, _, h => h
  | n + 1, S, h => by
    change ∀ k, k + 1 < strictN (Bool.rec (motive := fun _ => ℕ) 0 (Nat.succ S)
      (andB (Nat.blt 0 S) (ok (Nat.sub S 1)))) (gomInner ok n) → ok k = true
    rw [strictN_eq]
    apply gomInner_ok ok n
    cases hc : andB (Nat.blt 0 S) (ok (Nat.sub S 1))
    · intro k hk
      exact absurd hk (Nat.not_lt_zero _)
    · obtain ⟨c1, c2⟩ := andL_iff.1 hc
      have hS := Nat.blt_eq.mp c1
      intro k hk
      change k + 1 < S + 1 at hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact h k hk
      · have e : k = Nat.sub S 1 := by
          change k = S - 1
          omega
        rw [e]
        exact c2

theorem gomRun_ok (ok : ℕ → Bool) : ∀ (Cs : List ℕ) (S : ℕ), (∀ k, k + 1 < S → ok k = true) →
    ∀ k, k + 1 < gomRun ok Cs S → ok k = true
  | [], _, h => h
  | C :: Cs, S, h => by
    change ∀ k, k + 1 < strictN (gomInner ok C S) (gomRun ok Cs) → ok k = true
    rw [strictN_eq]
    exact gomRun_ok ok Cs _ (gomInner_ok ok C S h)

theorem gomRun_spec {ok : ℕ → Bool} {Cs : List ℕ} {n : ℕ} (h : gomRun ok Cs 1 = n + 1) :
    ∀ k < n, ok k = true := by
  have hi := gomRun_ok ok Cs 1 (fun k hk => absurd hk (by omega))
  rw [h] at hi
  exact fun k hk => hi k (by omega)

@[expose] noncomputable def covStepP (slot : ℕ → ℕ → ℕ → Bool) (NO AL : ℕ) (ih : ℕ → ℕ → ℕ)
    (J S : ℕ) : ℕ :=
  (fun D w => (fun nxt =>
      Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
        (Bool.rec (motive := fun _ => ℕ)
          (strictN nxt (ih J))
          (strictN (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) nxt
              (slot D w (bitsG J (nat_lit 0) (nat_lit 21))))
            (ih (Nat.shiftRight J (nat_lit 21))))
          (aliveG AL D))
        (Nat.blt (nat_lit 0) S))
      (Bool.rec (motive := fun _ => ℕ) (Nat.add S (nat_lit 1))
        (Nat.add (nat_lit 1) (Nat.shiftLeft (Nat.succ D) (nat_lit 20)))
        (Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.succ w) NO) true
          (Bool.rec (motive := fun _ => Bool) true false (aliveG AL D)))))
    (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 20))
    (Nat.land (Nat.sub S (nat_lit 1)) (nat_lit 1048575))

@[expose] noncomputable def coverRunP (slot : ℕ → ℕ → ℕ → Bool) (NO AL : ℕ) (Cs : List ℕ) :
    ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => covStepP slot NO AL ih2 J S)
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

theorem runCover_eq (FB OB : ℕ → ℕ) (sh wd NF NO AL : ℕ) (Cs : List ℕ) (S : ℕ) :
    runCover FB OB sh wd NF NO AL Cs S =
      coverRunP (fun D w x => slotOK FB OB sh wd NF AL D w x) NO AL Cs S := rfl

@[expose] def slot4 (slot : ℕ → ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → Bool := fun D w x _ => slot D w x

theorem covInnerP_inv {slot : ℕ → ℕ → ℕ → Bool} {NO AL : ℕ} (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO) :
    ∀ (n J S : ℕ), CovInv (slot4 slot) NO AL S → CovInv (slot4 slot) NO AL
      (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => covStepP slot NO AL ih2 J S) n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change CovInv (slot4 slot) NO AL (covStepP slot NO AL (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
      (fun _ S => S) (fun _ ih2 J S => covStepP slot NO AL ih2 J S) n) J S)
    have ih := covInnerP_inv (slot := slot) (AL := AL) hNO hNO0 n
    rcases h with rfl | ⟨D, w, rfl, hw, hw0, hprev, hcur⟩
    · exact Or.inl rfl
    obtain ⟨eD, ew⟩ := covDec (D := D) (Nat.lt_trans hw hNO)
    have h1 : 0 < 1 + 2 ^ 20 * D + w := by omega
    have hpos : Nat.blt (nat_lit 0) (1 + 2 ^ 20 * D + w) = true := by
      rw [Nat.blt_eq]
      exact h1
    have hnext := covNext_inv (slot := slot4 slot) hNO0 hw hw0 hprev hcur
    unfold covStepP
    simp only []
    rw [eD, ew, hpos]
    dsimp only
    cases ha : aliveG AL D
    · rw [ha] at hnext
      dsimp only at hnext ⊢
      rw [strictN_eq]
      exact ih _ _ (hnext (fun hal => absurd ((aliveG_iff AL D).2 hal) (by rw [ha]; decide)))
    · rw [ha] at hnext
      dsimp only at hnext ⊢
      rw [strictN_eq]
      apply ih
      cases hs : slot D w (bitsG J (nat_lit 0) (nat_lit 21))
      · exact Or.inl rfl
      · dsimp only
        exact hnext (fun _ => ⟨_, 0, hs⟩)

theorem coverRunP_inv {slot : ℕ → ℕ → ℕ → Bool} {NO AL : ℕ} (hNO : NO < 2 ^ 20)
    (hNO0 : 0 < NO) : ∀ (Cs : List ℕ) (S : ℕ), CovInv (slot4 slot) NO AL S →
      CovInv (slot4 slot) NO AL (coverRunP slot NO AL Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change CovInv (slot4 slot) NO AL (strictN (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => covStepP slot NO AL ih2 J S)
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) (coverRunP slot NO AL Cs))
    rw [strictN_eq]
    exact coverRunP_inv hNO hNO0 Cs _ (covInnerP_inv hNO hNO0 _ _ _ h)

theorem coverRunP_spec {slot : ℕ → ℕ → ℕ → Bool} {NO AL ND : ℕ} {Cs : List ℕ}
    (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO)
    (h : coverRunP slot NO AL Cs 1 = Nat.add (nat_lit 1) (Nat.shiftLeft ND (nat_lit 20))) :
    ∀ D < ND, AL.testBit D = true → ∀ w < NO, ∃ x, slot D w x = true := by
  have h1 : CovInv (slot4 slot) NO AL 1 := Or.inr ⟨0, 0, rfl, hNO0, Or.inl rfl,
    fun D' hD' => absurd hD' (Nat.not_lt_zero _), fun w' hw' => absurd hw' (Nat.not_lt_zero _)⟩
  have hi := coverRunP_inv hNO hNO0 Cs 1 h1
  rw [h] at hi
  have e : Nat.add (nat_lit 1) (Nat.shiftLeft ND (nat_lit 20)) = 1 + 2 ^ 20 * ND + 0 := by
    change 1 + ND <<< 20 = _
    rw [Nat.shiftLeft_eq]
    ring
  rw [e] at hi
  rcases hi with h0 | ⟨D, w, he, hw, -, hprev, -⟩
  · omega
  obtain ⟨d1, d2⟩ := covDec (D := ND) (w := 0) (by norm_num)
  obtain ⟨d3, d4⟩ := covDec (D := D) (Nat.lt_trans hw hNO)
  rw [he] at d1 d2
  rw [d1] at d3
  subst d3
  intro D' hD' hA w' hw'
  obtain ⟨x, _, hx⟩ := hprev D' hD' hA w' hw'
  exact ⟨x, hx⟩

@[expose] noncomputable def mDP (MD D : ℕ) : ℕ := bitsG MD (Nat.mul (nat_lit 24) D) (nat_lit 24)

@[expose] noncomputable def sumAccP (AL MD NORD : ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 2)
    (fun D acc => (fun m => Bool.rec (motive := fun _ => ℕ) acc
        (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.add acc (Nat.div NORD m))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt (nat_lit 0) m)
            (Nat.beq (Nat.mod NORD m) (nat_lit 0)))))
        (andB (aliveD AL D) (notB (Nat.beq D (nat_lit 0)))))
      (bits MD (Nat.mul (nat_lit 24) D) (nat_lit 24))) k

theorem sumOK_eq (AL MD ND NORD SUM : ℕ) : sumOK AL MD ND NORD SUM =
    andB (aliveD AL 0) (andB (Nat.blt AL (Nat.shiftLeft 1 ND))
      ((fun r => andB (Nat.blt 0 r) (Nat.beq (Nat.sub r 1) SUM)) (sumAccP AL MD NORD ND))) := rfl

theorem aliveD_iff (AL D : ℕ) : aliveD AL D = true ↔ AL.testBit D = true := aliveG_iff AL D

theorem sumAccP_spec (AL MD NORD : ℕ) : ∀ k, sumAccP AL MD NORD k = 0 ∨
    ((∀ D < k, AL.testBit D = true → D ≠ 0 → 0 < mDP MD D ∧ mDP MD D ∣ NORD) ∧
      sumAccP AL MD NORD k = 2 + ∑ D ∈ aliveSet AL k, NORD / mDP MD D)
  | 0 => Or.inr ⟨fun D hD => absurd hD (Nat.not_lt_zero _), by simp [aliveSet, sumAccP]⟩
  | k + 1 => by
    have hs : aliveSet AL (k + 1) = if AL.testBit k = true ∧ k ≠ 0 then
        insert k (aliveSet AL k) else aliveSet AL k := by
      unfold aliveSet
      rw [Finset.range_add_one, Finset.filter_insert]
    have e : sumAccP AL MD NORD (k + 1) = Bool.rec (motive := fun _ => ℕ) (sumAccP AL MD NORD k)
        (Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
          (Nat.add (sumAccP AL MD NORD k) (Nat.div NORD (mDP MD k)))
          (andB (Nat.blt (nat_lit 0) (sumAccP AL MD NORD k)) (andB (Nat.blt (nat_lit 0) (mDP MD k))
            (Nat.beq (Nat.mod NORD (mDP MD k)) (nat_lit 0)))))
        (andB (aliveD AL k) (notB (Nat.beq k (nat_lit 0)))) := rfl
    rw [e]
    have hval : andB (aliveD AL k) (notB (Nat.beq k (nat_lit 0))) = true ↔
        AL.testBit k = true ∧ k ≠ 0 := by
      rw [andL_iff, notL_eq, aliveD_iff]
      refine and_congr_right fun _ => ⟨fun e2 e3 => ?_, fun e2 => ?_⟩
      · rw [e3] at e2
        exact absurd e2 (by decide)
      · cases e4 : Nat.beq k 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e4) e2
    rcases sumAccP_spec AL MD NORD k with h0 | ⟨hd, he⟩
    · left
      rw [h0]
      cases andB (aliveD AL k) (notB (Nat.beq k (nat_lit 0)))
      · rfl
      · rfl
    · rw [he]
      by_cases hc : AL.testBit k = true ∧ k ≠ 0
      · rw [hval.2 hc]
        dsimp only
        have hm2 : andB (Nat.blt (nat_lit 0) (2 + ∑ D ∈ aliveSet AL k, NORD / mDP MD D))
            (andB (Nat.blt (nat_lit 0) (mDP MD k)) (Nat.beq (Nat.mod NORD (mDP MD k)) (nat_lit 0))) =
              true ↔ 0 < mDP MD k ∧ NORD % mDP MD k = 0 := by
          rw [andL_iff, andL_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq]
          exact ⟨fun h => h.2, fun h => ⟨Nat.lt_of_lt_of_le Nat.zero_lt_two (Nat.le_add_right _ _), h⟩⟩
        by_cases hm : 0 < mDP MD k ∧ NORD % mDP MD k = 0
        · rw [hm2.2 hm]
          dsimp only
          right
          refine ⟨fun D hD hA hD0 => ?_, ?_⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hD with hD | rfl
            · exact hd D hD hA hD0
            · exact ⟨hm.1, Nat.dvd_of_mod_eq_zero hm.2⟩
          · rw [hs, ite_eq_left hc, Finset.sum_insert (by simp [aliveSet])]
            change 2 + _ + NORD / mDP MD k = _
            ring
        · have hf : andB (Nat.blt (nat_lit 0) (2 + ∑ D ∈ aliveSet AL k, NORD / mDP MD D))
              (andB (Nat.blt (nat_lit 0) (mDP MD k)) (Nat.beq (Nat.mod NORD (mDP MD k)) (nat_lit 0))) =
                false := Bool.eq_false_iff.2 fun e => hm (hm2.1 e)
          rw [hf]
          left
          rfl
      · have hf : andB (aliveD AL k) (notB (Nat.beq k (nat_lit 0))) = false :=
          Bool.eq_false_iff.2 fun e => hc (hval.1 e)
        rw [hf]
        dsimp only
        right
        refine ⟨fun D hD hA hD0 => ?_, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hD with hD | rfl
          · exact hd D hD hA hD0
          · exact absurd ⟨hA, hD0⟩ hc
        · rw [hs, ite_eq_right hc]

theorem sumOK_spec {AL MD ND NORD SUM : ℕ} (h : sumOK AL MD ND NORD SUM = true) :
    AL.testBit 0 = true ∧ AL < 2 ^ ND ∧
      (∀ D < ND, AL.testBit D = true → D ≠ 0 → 0 < mDP MD D ∧ mDP MD D ∣ NORD) ∧
      SUM = 1 + ∑ D ∈ aliveSet AL ND, NORD / mDP MD D := by
  rw [sumOK_eq, andL_iff, andL_iff, aliveD_iff, Nat.blt_eq] at h
  obtain ⟨h0, hA, hr⟩ := h
  refine ⟨h0, by change AL < 1 <<< ND at hA; rw [Nat.shiftLeft_eq, Nat.one_mul] at hA; exact hA, ?_⟩
  rcases sumAccP_spec AL MD NORD ND with hz | ⟨hd, he⟩
  · simp only [] at hr
    rw [hz] at hr
    exact absurd hr Bool.false_ne_true
  · simp only [] at hr
    rw [he, andL_iff, Nat.beq_eq] at hr
    refine ⟨hd, ?_⟩
    have := hr.2
    change 2 + _ - 1 = SUM at this
    omega

end CFSG.Certificates.DSP

end
