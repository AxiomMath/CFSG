module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNeg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem ordE6_four_eq : ordE6 (2 ^ 2) = 2 ^ 72 * 6037136330665109101306875 := by
  norm_num [ordE6]

theorem not_dvd_ordE6_of_twD5 {m : ℕ} (hm : 1 ≤ m) (hm1 : m ≠ 1) :
    ¬ ordTwistedD 5 (2 ^ m) ∣ ordE6 (2 ^ 2) := by
  intro hdvd
  have hQ2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hQe : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  rcases Nat.lt_or_ge m 4 with hlt | hge
  · rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
    · have h41 : 41 ∣ ordTwistedD 5 (2 ^ 2) := by
        unfold ordTwistedD
        decide +kernel
      have h2 := h41.trans hdvd
      rw [ordE6_four_eq] at h2
      norm_num at h2
    · have h331 : 331 ∣ ordTwistedD 5 (2 ^ 3) := by
        unfold ordTwistedD
        decide +kernel
      have h2 := h331.trans hdvd
      rw [ordE6_four_eq] at h2
      norm_num at h2
  · have hg : Nat.gcd 4 ((2 ^ m) ^ 5 + 1) = 1 := by
      have h5e : 2 ∣ (2 ^ m) ^ 5 := dvd_pow hQe (by norm_num)
      obtain ⟨k, hk⟩ := h5e
      have h1 : Nat.Coprime 2 ((2 ^ m) ^ 5 + 1) := Nat.coprime_two_left.mpr ⟨k, by omega⟩
      simpa using Nat.Coprime.pow_left 2 h1
    have h1 : 2 ^ (20 * m) ∣ ordTwistedD 5 (2 ^ m) := by
      unfold ordTwistedD
      rw [hg, Nat.div_one]
      refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
      rw [show 5 * (5 - 1) = 20 by norm_num, ← pow_mul, mul_comm m 20]
    have h2 := h1.trans hdvd
    rw [ordE6_four_eq] at h2
    have hcop : Nat.Coprime (2 ^ (20 * m)) 6037136330665109101306875 :=
      Nat.Coprime.pow_left _ (by norm_num)
    have h3 := hcop.dvd_of_dvd_mul_right h2
    have h4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h3
    omega

section Core

theorem e6_twD5_one {S : Type} [Group S] [Finite S] {J : Subgroup S} {labJ : GLALabel}
    (hcen : Subgroup.center S = ⊥)
    (hlabK : HasLabel S (fun l : GLALabel => l = ⟨.E6, 0, 2⟩))
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) (hbad : labJ.tag = .twD ∧ labJ.rank = 5) :
    labJ.n = 1 := by
  by_contra hne
  obtain ⟨labS, hΛS, R, _, I, F, θ, -, -, hP, hM⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel hlabK
  have hP' : labS = ⟨.E6, 0, 2⟩ := hP
  subst hP'
  obtain ⟨labJ', hΛJ, R', _, I', F', θ', -, -, hP2, hM'⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel hlabJ
  have hP2' : labJ' = labJ := hP2
  subst hP2'
  obtain ⟨t', r', n'⟩ := labJ'
  obtain ⟨h1, h5⟩ := hbad
  simp only at h1 h5 hne
  subst h1 h5
  have hE6 : LieModel R .E6 0 2 2 := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] using hM
  have hD5 : LieModel R' .POmegaMinus 5 2 n' := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] using hM'
  have hcS : Nat.card S = ordE6 (2 ^ 2) := by
    have h1 : Nat.card R = ordE6 (2 ^ 2) := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hE6
    rw [← h1, ← Nat.card_congr θ.toEquiv]
    exact Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.toEquiv
  have hcJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedD 5 (2 ^ n') := by
    rw [Nat.card_congr θ'.toEquiv]
    exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hD5
  have hdvd : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card S := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
    have h2' : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥J := ⟨_, by rw [this, mul_comm]⟩
    exact h2'.trans (Subgroup.card_subgroup_dvd_card J)
  rw [hcJ, hcS] at hdvd
  exact not_dvd_ordE6_of_twD5 hΛJ.1 hne hdvd

end Core

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def I14NegPieceDOne : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
    HasLabel ↥J (fun l : GLALabel => l = labJ) → α ^ p = 1 →
    GLAPComponent p (fixSubgroup α) J →
    labK = ⟨.E6, 0, 2⟩ → labJ = ⟨.twD, 5, 1⟩ → False

theorem canonLabel_e6_two : canonLabel (⟨.E6, 0, 2⟩ : GLALabel) = ⟨.E6, 0, 2⟩ := by
  simp [canonLabel]

theorem canonLabel_twD5 {labJ : GLALabel} (hbad : labJ.tag = .twD ∧ labJ.rank = 5) :
    canonLabel labJ = labJ := by
  obtain ⟨t', r', n'⟩ := labJ
  obtain ⟨h1, h5⟩ := hbad
  simp only at h1 h5
  subst h1 h5
  simp [canonLabel]

section Reductions

theorem i14NegPieceD_of_one (h : I14NegPieceDOne) : I14NegPieceD := by
  intro S _ _ p α J labK labJ hp hp2 hcen hlabK hlabJ hα hJ hKE hbad
  subst hKE
  have hn := Y10GNegBC.e6_twD5_one (J := J) hcen hlabK hlabJ hbad
  obtain ⟨t', r', n'⟩ := labJ
  obtain ⟨h1, h5⟩ := hbad
  simp only at h1 h5 hn
  subst h1 h5 hn
  exact h S p α J _ _ hp hp2 hcen hlabK hlabJ hα hJ rfl rfl

end Reductions

end CFSG.LocalAnalysis.GLTheoremA.Y10F
