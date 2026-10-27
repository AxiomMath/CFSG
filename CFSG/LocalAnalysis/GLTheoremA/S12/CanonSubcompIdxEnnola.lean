module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AExtU33
public import CFSG.CGT.Timmesfeld75.MultPrime
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.Assembly.LowTwoRank
open CFSG.StandardType (markTag markRank markChar markDeg GGLabelRigidInput GGHasLabel GGLabelIso)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel hasLabel_isQuasisimple)

private lemma ennolaIdx_u33_label_odd
    (hRig : GGLabelRigidInput) {X : Type} [Group X] [Finite X] {lab : GLALabel}
    (hX : HasLabel X (· = lab)) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3)
    (φ : X ⧸ Subgroup.center X ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) :
    (canonLabel lab).n = 1 := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    (Y10GInnLin.ggHasLabel_of_hasLabel hX).2.1
  have hperf : commutator X = ⊤ := hX.1
  have h33 : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 3 1 :=
    CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hq φ
  obtain ⟨hlab, -, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hX
  have hhas' : GGHasLabel (⟨.G2der, 0, 1⟩ : GLALabel) (X ⧸ Subgroup.center X) :=
    CFSG.LocalAnalysis.GLTheoremA.T173A.ext_u33_label hperf h33
  have hiso : GGLabelIso lab ⟨.G2der, 0, 1⟩ :=
    hRig lab ⟨.G2der, 0, 1⟩ (X ⧸ Subgroup.center X) hlab ⟨le_rfl, rfl, rfl⟩ hhas hhas'
  rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso]
  rfl

theorem canonLabel_n_odd_of_idxOver
    (hRig : GGLabelRigidInput) {X : Type} [Group X] [Finite X] {lab : GLALabel}
    (hX : HasLabel X (· = lab)) {d : LieTypeIndex} (hd : d.characteristic = 2) {m : ℕ}
    (hm : KD264Lie.fieldSize d = 2 ^ m) {i : CFSGIndex}
    (φ : X ⧸ Subgroup.center X ≃* i.Group) {j : ℕ} (hj : Odd j)
    (h : KD264Lie.IdxOver d.characteristic (KD264Lie.fieldSize d ^ j) i) :
    ∃ k : ℕ, Odd k ∧ (canonLabel lab).n = k * m := by
  have hQ : KD264Lie.fieldSize d ^ j = 2 ^ (m * j) := by rw [hm, ← pow_mul]
  cases i with
  | cyclic _ _ => simp only [KD264Lie.IdxOver] at h
  | sporadic _ => simp only [KD264Lie.IdxOver] at h
  | lie e =>
    simp only [KD264Lie.IdxOver] at h
    rcases h with ⟨hch, hfs, -⟩ | ⟨-, hQ2, hsmall⟩ | ⟨hd3, -, -⟩
    · have hD := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.two_pow_canonLabel_n_of_lie
        hRig hX e (hch.trans hd) φ
      rw [hfs, hm, ← pow_mul, Nat.mul_comm m j] at hD
      exact ⟨j, hj, Nat.pow_right_injective le_rfl hD⟩
    · have hpoweq : 2 ^ (m * j) = 2 ^ 1 := by rw [← hQ, hQ2]; norm_num
      have hmj : m * j = 1 := Nat.pow_right_injective le_rfl hpoweq
      have hm1 : m = 1 := Nat.dvd_one.mp ⟨j, hmj.symm⟩
      rcases hsmall with ⟨q, hqA, hq7⟩ | ⟨q, hqT, hq3⟩
      · obtain ⟨d', hv'⟩ := e
        dsimp only at hqA
        subst hqA
        obtain ⟨e2⟩ :=
          CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
            (n := 1) q hv' (by rw [Nat.card_zmod, hq7])
        obtain ⟨e7⟩ :=
          CFSG.HardMathSupport.Solomon.Coordinator.nonempty_psl2_seven_equiv_projectiveSL_three_two
        let ePSL :=
          CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
            2 (ZMod 7)
        let eProj := CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 3 (ZMod 2)
        have hcard : Nat.card (ZMod 2) = 2 ^ 1 := by
          rw [Nat.card_zmod]; norm_num
        have hcan := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig X lab 3 1 (ZMod 2)
          (by norm_num) hcard hX
          ⟨φ.trans (e2.symm.trans (ePSL.symm.trans (e7.trans eProj)))⟩
        refine ⟨1, by norm_num, ?_⟩
        rw [hm1, hcan]
      · obtain ⟨d', hv'⟩ := e
        dsimp only at hqT
        subst hqT
        have hcan := ennolaIdx_u33_label_odd hRig hX hv' hq3 φ
        refine ⟨1, by norm_num, ?_⟩
        rw [hm1, hcan]
    · exact absurd (hd3.symm.trans hd) (by norm_num)
  | alternating n hn =>
    simp only [KD264Lie.IdxOver] at h
    rcases h with ⟨hn5, hcase5⟩ | ⟨hn6, hcase6⟩ | ⟨hn8, hd8, hQ8⟩
    · subst hn5
      rcases hcase5 with ⟨-, hQ4⟩ | ⟨hd5, -⟩
      · have hpoweq : 2 ^ (m * j) = 2 ^ 2 := by rw [← hQ, hQ4]; norm_num
        have hmj : m * j = 2 := Nat.pow_right_injective le_rfl hpoweq
        have hj1 : j = 1 := by
          obtain ⟨k, rfl⟩ := hj
          have hmk : m * (2 * k + 1) = 2 := by simpa using hmj
          have hdiv : (2 * k + 1) ∣ 2 := ⟨m, by rw [mul_comm]; exact hmk.symm⟩
          have := (Nat.dvd_prime Nat.prime_two).1 hdiv
          omega
        have hm2 : m = 2 := by
          rw [hj1, mul_one] at hmj
          exact hmj
        have hE : Nat.card (GaloisField 2 2) = 2 ^ 2 :=
          CFSG.StandardType.ChevTwo.card_galoisField_two (by norm_num)
        obtain ⟨ψ⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
          (GaloisField 2 2) (Or.inl (by rw [hE]; norm_num))
        have hcan := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig X lab 2 2
          (GaloisField 2 2) le_rfl hE hX ⟨φ.trans ψ.symm⟩
        refine ⟨1, by norm_num, ?_⟩
        rw [hm2, hcan]
      · exact absurd (hd5.symm.trans hd) (by norm_num)
    · subst hn6
      rcases hcase6 with ⟨-, hQ2⟩ | ⟨hd3, -⟩
      · have hpoweq : 2 ^ (m * j) = 2 ^ 1 := by rw [← hQ, hQ2]; norm_num
        have hmj : m * j = 1 := Nat.pow_right_injective le_rfl hpoweq
        have hm1 : m = 1 := Nat.dvd_one.mp ⟨j, hmj.symm⟩
        have hcan := Y10GSympLabel.canonLabel_eq_of_quot_alternating hRig hX φ
        refine ⟨1, by norm_num, ?_⟩
        rw [hm1, hcan]
      · exact absurd (hd3.symm.trans hd) (by norm_num)
    · subst hn8
      have hpoweq : 2 ^ (m * j) = 2 ^ 1 := by rw [← hQ, hQ8]; norm_num
      have hmj : m * j = 1 := Nat.pow_right_injective le_rfl hpoweq
      have hm1 : m = 1 := Nat.dvd_one.mp ⟨j, hmj.symm⟩
      have hE : Nat.card (GaloisField 2 1) = 2 ^ 1 :=
        CFSG.StandardType.ChevTwo.card_galoisField_two (by norm_num)
      have hcard2 : Nat.card (GaloisField 2 1) = 2 := by rw [hE, pow_one]
      obtain ⟨e8⟩ :=
        CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_four_mulEquiv_alternating_eight
          (k := GaloisField 2 1) hcard2
      have hcan := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig X lab 4 1
        (GaloisField 2 1) (by norm_num) hE hX
        ⟨φ.trans (e8.symm.trans
          (CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 4 (GaloisField 2 1)))⟩
      refine ⟨1, by norm_num, ?_⟩
      rw [hm1, hcan]

end CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp

end
