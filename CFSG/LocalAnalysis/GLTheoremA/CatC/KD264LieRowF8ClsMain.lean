module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ClsSp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ClsLn
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer

@[expose] def KD264F8ClsAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    overEight d.1 → P d.1 →
    ¬ (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
    ¬ (∃ n : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA n q ∧ 3 ∣ n + 1) →
    ¬ (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q) →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      KD264F8Hyp (TauCeti.CFSGIndex.lie d).Group A →
      KD264F8FamLn d.1 ∨ KD264F8FamSp d.1 ∨ KD264F8FamOm d.1

@[expose] def KD264F8IsLin (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .A n q

@[expose] def KD264F8IsUni (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .twistedA n q

@[expose] def KD264F8IsSym (e : TauCeti.LieTypeIndex) : Prop :=
  (∃ (n : ℕ) (q : TauCeti.PrimePower), e = .B n q) ∨ (∃ (n : ℕ) (q : TauCeti.PrimePower), e = .C n q)

@[expose] def KD264F8IsOrthPlus (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .D n q

@[expose] def KD264F8IsOrthMinus (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .twistedD n q ∧ 5 ≤ n

@[expose] def KD264F8IsExc (e : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, e = .E6 q) ∨ (∃ q : TauCeti.PrimePower, e = .E7 q) ∨
    (∃ q : TauCeti.PrimePower, e = .E8 q) ∨ (∃ q : TauCeti.PrimePower, e = .F4 q)

@[expose] def KD264F8ClsUni : Prop := KD264F8ClsAt KD264F8IsUni

@[expose] def KD264F8ClsOrthPlus : Prop := KD264F8ClsAt KD264F8IsOrthPlus

@[expose] def KD264F8ClsOrthMinus : Prop := KD264F8ClsAt KD264F8IsOrthMinus

@[expose] def KD264F8ClsExc : Prop := KD264F8ClsAt KD264F8IsExc

theorem primePower_p_eq_two_of_card_eight (q : TauCeti.PrimePower) (hq : q.card = 8) : q.p = 2 := by
  have hdvd : q.p ∣ 2 ^ 3 := by
    have h8 : q.card = 2 ^ 3 := by rw [hq]; norm_num
    rw [← h8, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)

theorem KD264F8ClsLin_holds : KD264F8ClsAt KD264F8IsLin := by
  intro d _hfin _hns hk2 _hk3 hov hP _ _ _ A hA
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨n, q, rfl⟩ := hP
  have hq : q.card = 8 := hov
  have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hd1
  have hr : 1 ≤ n ∧ (n = 1 → 4 ≤ q.card) :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
  have hn1 : n ≠ 1 := by
    rintro rfl
    apply hk2
    show k2Lie 3 (TauCeti.LieTypeIndex.A 1 q)
    refine ⟨rfl, ?_⟩
    rw [hq]
    norm_num
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : (TauCeti.CFSGIndex.lie ⟨.A n q, hd1⟩).Group ≃*
      projectiveSL (n + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd1).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) _)
  have hcardK : Nat.card (GaloisField q.p q.exponent) = 8 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
    exact hq
  obtain ⟨hAab, hout, hnot⟩ := F8Trans.hyp_transport e A hA
  obtain ⟨-, h3, h4, -⟩ := hA
  have hp := pRank_map_mulEquiv (p := 3) (MulAut.congr e) A
  have hb := F8Ln.linear_rank_bounds (by omega) hcardK _ hAab (by rw [hp]; exact h3)
    (by rw [hp]; exact h4) hout hnot
  exact Or.inl ⟨n, q, rfl, by omega, by omega, hq⟩

theorem KD264F8ClsSym_holds : KD264F8ClsAt KD264F8IsSym := by
  intro d _hfin _hns hk2 _hk3 hov hP _ _ _ A hA
  obtain ⟨d1, hd1⟩ := d
  have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hd1
  rcases hP with ⟨n, q, rfl⟩ | ⟨n, q, rfl⟩
  · have hq : q.card = 8 := hov
    have hp2 := primePower_p_eq_two_of_card_eight q hq
    have hr : 2 ≤ n ∧ ¬ (n = 2 ∧ q.card = 2) :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
    have hn2 : n ≠ 2 := by
      rintro rfl
      exact hk2 ⟨rfl, hq⟩
    have hn3 : 3 ≤ n := by omega
    haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
      (⟨TauCeti.LieTypeIndex.B n q, hd1⟩ : TauCeti.ValidLieTypeIndex)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hd1 hp2 hn3
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
        (⟨TauCeti.LieTypeIndex.B n q, hd1⟩ : TauCeti.ValidLieTypeIndex)) = 8 := by
      rw [TauCeti.ValidLieTypeIndex.card_fixedField,
        TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
        show TauCeti.ValidLieTypeIndex.characteristic
            (⟨TauCeti.LieTypeIndex.B n q, hd1⟩ : TauCeti.ValidLieTypeIndex) = q.p from
          TauCeti.LieTypeIndex.characteristic_B n q,
        show TauCeti.ValidLieTypeIndex.fieldExponent
            (⟨TauCeti.LieTypeIndex.B n q, hd1⟩ : TauCeti.ValidLieTypeIndex) = q.exponent from
          TauCeti.LieTypeIndex.fieldExponent_B n q,
        ← TauCeti.PrimePower.card_def]
      exact hq
    obtain ⟨hAab, hout, hnot⟩ := F8Trans.hyp_transport e A hA
    obtain ⟨-, -, h4, -⟩ := hA
    have hp := pRank_map_mulEquiv (p := 3) (MulAut.congr e) A
    have hb := F8Sp.sp_rank_bound hn3 hcardK _ hAab (by rw [hp]; exact h4) hout hnot
    have hn : n = 3 := by omega
    subst hn
    exact Or.inr (Or.inl (Or.inl ⟨q, rfl, hq⟩))
  · exfalso
    have hq : q.card = 8 := hov
    have hp2 := primePower_p_eq_two_of_card_eight q hq
    have hr : 3 ≤ n ∧ q.p ≠ 2 := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
    exact hr.2 hp2

theorem KD264F8ClsRest {d : TauCeti.ValidLieTypeIndex} (hk2 : ¬ k2Lie 3 d.1) (hov : overEight d.1)
    (hTri : ¬ (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q))
    (hTwE6 : ¬ (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q))
    (hn : ¬ KD264F8IsLin d.1) (hn' : ¬ KD264F8IsUni d.1) (hn'' : ¬ KD264F8IsSym d.1)
    (hn3 : ¬ KD264F8IsOrthPlus d.1) (hn4 : ¬ KD264F8IsOrthMinus d.1) (hn5 : ¬ KD264F8IsExc d.1)
    (hn44 : ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedD 4 q) : False := by
  obtain ⟨d1, hd1⟩ := d
  cases d1 with
  | A n q => exact hn ⟨n, q, rfl⟩
  | twistedA n q => exact hn' ⟨n, q, rfl⟩
  | B n q => exact hn'' (Or.inl ⟨n, q, rfl⟩)
  | C n q => exact hn'' (Or.inr ⟨n, q, rfl⟩)
  | D n q => exact hn3 ⟨n, q, rfl⟩
  | twistedD n q =>
    have h4n := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hd1).1
    by_cases hn4' : n = 4
    · subst hn4'
      exact hn44 ⟨q, rfl⟩
    · exact hn4 ⟨n, q, rfl, by omega⟩
  | E6 q => exact hn5 (Or.inl ⟨q, rfl⟩)
  | E7 q => exact hn5 (Or.inr (Or.inl ⟨q, rfl⟩))
  | E8 q => exact hn5 (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))
  | F4 q => exact hn5 (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)))
  | G2 q => exact hk2 ⟨rfl, (hov : q.card = 8)⟩
  | twistedE6 q => exact hTwE6 ⟨q, rfl⟩
  | trialityD4 q => exact hTri ⟨q, rfl⟩
  | suzuki k => exact hov
  | reeG2 k => exact hov
  | reeF4 k =>
    cases k with
    | zero => exact hov
    | succ k =>
      cases k with
      | zero => exact hk2 (Or.inl ⟨rfl, rfl⟩)
      | succ k => exact hov
  | tits => exact hov

theorem kd264F8Cls_of_pieces (hU : KD264F8ClsUni) (hDp : KD264F8ClsOrthPlus)
    (hDm : KD264F8ClsOrthMinus) (hE : KD264F8ClsExc) : KD264F8Cls := by
  intro d _hfin hns hk2 hk3 hov hTri hTwA hTwE6 A hA
  by_cases hL : KD264F8IsLin d.1
  · exact KD264F8ClsLin_holds d hns hk2 hk3 hov hL hTri hTwA hTwE6 A hA
  by_cases hUn : KD264F8IsUni d.1
  · exact hU d hns hk2 hk3 hov hUn hTri hTwA hTwE6 A hA
  by_cases hS : KD264F8IsSym d.1
  · exact KD264F8ClsSym_holds d hns hk2 hk3 hov hS hTri hTwA hTwE6 A hA
  by_cases hOp : KD264F8IsOrthPlus d.1
  · exact hDp d hns hk2 hk3 hov hOp hTri hTwA hTwE6 A hA
  by_cases hOm : KD264F8IsOrthMinus d.1
  · exact hDm d hns hk2 hk3 hov hOm hTri hTwA hTwE6 A hA
  by_cases hEx : KD264F8IsExc d.1
  · exact hE d hns hk2 hk3 hov hEx hTri hTwA hTwE6 A hA
  by_cases hO4 : ∃ q : TauCeti.PrimePower, d.1 = .twistedD 4 q
  · obtain ⟨q, hq⟩ := hO4
    exact Or.inr (Or.inr ⟨q, hq, by rw [hq] at hov; exact hov⟩)
  exact (KD264F8ClsRest hk2 hov hTri hTwE6 hL hUn hS hOp hOm hEx hO4).elim

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
