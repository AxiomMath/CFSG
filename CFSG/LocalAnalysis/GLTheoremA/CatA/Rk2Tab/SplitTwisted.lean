module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.PRankSmall
public import CFSG.LieType.Steinberg.CentralExt.POmegaMinusMultiplier
public import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.GH74.Uniqueness.SU.SU7Gen2
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GL83PartI.I713.Chain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.RankThree.CentralCover
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
open scoped MatrixGroups Pointwise


theorem rk2_split_low_twD_sub_ge {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twD) (hℓ4 : 4 ≤ lab.rank)
    (hpq : p ∣ 2 ^ lab.n - 1) :
    lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  classical
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  obtain ⟨t, ℓ, n⟩ := lab
  simp only at htag hℓ4 hpq
  subst htag
  simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
  have hn : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · exact absurd hlab.1 (by omega)
      · exact absurd (Nat.dvd_one.mp hpq) hp.ne_one
    · exact hge
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
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hdvd : p ∣ Nat.card F - 1 := by rw [hcard]; exact hpq
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_isElemAbelian_torus_statedOmegaMinus (F := F) (ℓ := ℓ) (r := p) hℓ4
      hp hp2 hdvd b c hirr
  have hmult1 : Nat.card (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)))) = 1 := by
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pomegaMinus_hopfMultiplier
        (n := ℓ) (K := F) (b := b) (c := c) hℓ4 hirr (p := 2) (f := n) hcard hF4
    rw [Nat.card_congr eM.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (Nat.gcd 4 ((2 ^ n) ^ ℓ + 1))) ≃
        ZMod (Nat.gcd 4 ((2 ^ n) ^ ℓ + 1))), Nat.card_zmod]
    have heven : Even ((2 ^ n) ^ ℓ) := by
      rw [← pow_mul]
      exact even_iff_two_dvd.mpr (dvd_pow_self 2
        (Nat.mul_ne_zero (by omega) (by omega)))
    have hodd : Odd ((2 ^ n) ^ ℓ + 1) := Even.add_one heven
    have h2 : Nat.Coprime 2 ((2 ^ n) ^ ℓ + 1) := Nat.coprime_two_left.mpr hodd
    have h4 : Nat.Coprime 4 ((2 ^ n) ^ ℓ + 1) := by
      have h5 := h2.pow_left 2
      simpa using h5
    rwa [Nat.coprime_iff_gcd_eq_one] at h4
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


end CFSG.LocalAnalysis.GLTheoremA
