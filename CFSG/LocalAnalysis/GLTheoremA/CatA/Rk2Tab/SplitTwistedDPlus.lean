module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.OmegaMinusTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.PRankSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwisted
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Multiplier
open scoped MatrixGroups Pointwise

theorem rk2_split_low_twD_add {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twD) (hℓ : 4 ≤ lab.rank) (hn : 1 ≤ lab.n)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  classical
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  obtain ⟨t, ℓ, n⟩ := lab
  simp only at htag hℓ hn hpq
  subst htag
  simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
  have ht : CFSG.StandardType.markTag (⟨.twD, ℓ, n⟩ : GLALabel) = .POmegaMinus := by
    simp [CFSG.StandardType.markTag, show ℓ ≠ 2 by omega, show ℓ ≠ 3 by omega]
  have hrk : CFSG.StandardType.markRank (⟨.twD, ℓ, n⟩ : GLALabel) = ℓ := by
    simp [CFSG.StandardType.markRank, show ℓ ≠ 2 by omega, show ℓ ≠ 3 by omega]
  have hch : CFSG.StandardType.markChar (⟨.twD, ℓ, n⟩ : GLALabel) = 2 := by
    simp [CFSG.StandardType.markChar]
  have hdg : CFSG.StandardType.markDeg (⟨.twD, ℓ, n⟩ : GLALabel) = n := by
    simp [CFSG.StandardType.markDeg, show ℓ ≠ 2 by omega]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, b, c, hirr, ⟨θ⟩⟩ :=
    hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcard
  have hmult1 : Nat.card (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)))) = 1 := by
    have hSC : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)))
        .POmegaMinus ℓ 2 n :=
      ⟨⟨Nat.prime_two, hn, hℓ⟩, F, hfield, hfinite, hcard, b, c, hirr, ⟨MulEquiv.refl _⟩⟩
    exact card_griessHopfMultiplier_pomegaMinus_eq_one hn hSC
  haveI : Finite (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)))) :=
    Nat.finite_of_card_ne_zero (by rw [hmult1]; norm_num)
  have hZcardK : Nat.card (Subgroup.center K) = 1 := by
    have hdvdZ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ θ
    rw [hmult1] at hdvdZ
    exact Nat.dvd_one.mp hdvdZ
  have hZbot : Subgroup.center K = ⊥ := Subgroup.card_eq_one.mp hZcardK
  have hz : CFSG.Open.pRank p (Subgroup.center K) = 0 := by
    rw [hZbot]
    exact pRank_eq_zero_of_not_dvd_card hp (by
      rw [Subgroup.card_bot]
      exact fun h => hp.ne_one (Nat.dvd_one.mp h))
  have hwit := rk2SplitTwDOmegaTorus_holds (F := F) (ℓ := ℓ) (p := p) hℓ hp hp2
    (by rw [hcard]; exact hpq) b c hirr
  have hwit' : ∃ E X : Subgroup (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c))),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ (ℓ - 1) ∧
        E ≤ Subgroup.normalizer
          (X : Set (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)))) := hwit
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ := hwit'
  have eK : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
  have eiso : StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)) ≃* K :=
    (eK.symm.trans θ).symm
  have hkereiso : eiso.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff eiso.toMonoidHom).mpr eiso.injective
  have hk : ℓ - 1 ≤ CFSG.Open.twoLocalPrimeRank p K :=
    le_twoLocalPrimeRank_of_map eiso.toMonoidHom hp hp2 hX2
      (by rw [Ne, Subgroup.map_eq_bot_iff_of_injective X eiso.injective]; exact hX)
      hE hEcard (by rw [hkereiso]; simp) hXE
  rw [hz]
  omega

theorem rk2_split_low_twD {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twD) (hℓ : 4 ≤ lab.rank)
    (hpq : p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1) :
    lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  rcases hpq with h | h
  · exact rk2_split_low_twD_add hK hp hp2 htag hℓ (by
      rcases Nat.eq_zero_or_pos lab.n with h0 | h0
      ·
        exfalso
        have hlab : CFSG.Assembly.LargeEvenInLambda2 lab :=
          (quasisimple_markedModel_of_isLabel hK).2.1
        have h1 : 1 ≤ lab.n := by
          rcases lab with ⟨t, l, n⟩
          simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
          exact hlab.1
        omega
      · exact h0) h
  · exact rk2_split_low_twD_sub_ge hK hp hp2 htag hℓ h

end CFSG.LocalAnalysis.GLTheoremA
