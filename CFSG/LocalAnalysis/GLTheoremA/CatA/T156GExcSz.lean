module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwB2
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Ree CFSG.Open CFSG.StandardType
open CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.GLTheoremA.FR


theorem fixSub_sz {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {F : Set (MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K)))} (hF : InnFree p F)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K))} (hf : f ∈ F) (hord : orderOf f = p) :
    ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = 2 ^ (2 * b + 1) ∧ Nonempty (↥(FP.fixSub f) ≃* suzukiGroup b k) := by
  obtain ⟨e⟩ := nonempty_szQuot_equiv ha hK
  have hαord : orderOf (MulAut.congr e f) = p := by
    rw [MulEquiv.orderOf_eq (MulAut.congr e) f, hord]
  have hαinn : MulAut.congr e f ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
    fun h => hF f hf hord ((congr_mem_range_conj e f).1 h)
  obtain ⟨σ, h, b, k, hkF, hkfin, hσp, hbp, hkcard, hconj, ⟨eH⟩⟩ :=
    suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 (MulAut.congr e f) hαord hαinn
  have e₁ : ↥(FP.fixSub f) ≃* suzukiGroup b k :=
    (fixSubEquivCongr e f).trans ((fixSubEquivConj (MulAut.conj h) (MulAut.congr e f)).trans
      ((MulEquiv.subgroupCongr (by rw [hconj]; rfl)).trans eH))
  exact ⟨b, hbp, k, hkF, hkfin, hkcard, ⟨e₁⟩⟩

variable {p : ℕ}

theorem geomBody_sz (hp : p.Prime) (hp2 : p ≠ 2) {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GeomBody p ⟨.twB2, 0, 2 * a + 1⟩ (LargeEvenCenterQuot (LargeEvenSzGroup a K)) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K))) := by
  refine geomBody_of_field (by simp) fun hS hna f hf hord => ?_
  have hF := Y10GField.innFree_of_ggRawInnField
    (RawAutSz.ggRawInnField_suzuki ha hK hp.one_lt.ne') hS hna
  obtain ⟨b, hbp, k, _, _, hkcard, ⟨e₁⟩⟩ := fixSub_sz ha hK hp hp2 hF hf hord
  haveI := hS
  have hZ := center_eq_bot_of_simple_noncomm hna
  have hfix : FP.fixSub f = ggFixSub f := Subgroup.ext fun _ => Iff.rfl
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  ·
    subst hb0
    refine Or.inr fun E hE hEx => ?_
    haveI : Fact p.Prime := ⟨hp⟩
    have hc : Nat.card (suzukiGroup 0 k) = 20 := by
      rw [suzuki_order hkcard]
      norm_num
    have hC : Nat.card (ggFixSub f) = 20 := by
      rw [← hc, ← hfix]
      exact Nat.card_congr e₁.toEquiv
    have hdvd : Nat.card E ∣ 20 := hC ▸ card_dvd_card_fixSub hZ hEx
    haveI : Finite E := Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hdvd; norm_num at hdvd)
    have hpg : IsPGroup p E := fun φ => ⟨1, by
      apply Subtype.ext
      rw [pow_one, Subgroup.coe_pow, hE.2 φ φ.2, Subgroup.coe_one]⟩
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hpg
    rw [hr] at hdvd ⊢
    have hodd : Odd (p ^ r) := Odd.pow (hp.odd_of_ne_two hp2)
    have h5 : p ^ r ∣ 5 := by
      have h20 : (20 : ℕ) = 4 * 5 := by norm_num
      rw [h20] at hdvd
      have hcop : Nat.Coprime (p ^ r) 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hodd)
      exact hcop.dvd_of_dvd_mul_left hdvd
    have hle5 : p ^ r ≤ 5 := Nat.le_of_dvd (by norm_num) h5
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · interval_cases r
      · rw [pow_zero]
        exact hp.one_lt.le
      · rw [pow_one]
    · exfalso
      have : 3 ^ 2 ≤ p ^ r :=
        calc 3 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
          _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr2
      omega
  ·
    obtain ⟨eZ⟩ := nonempty_szQuot_equiv hb1 hkcard
    obtain ⟨hs₀, hna₀⟩ := Y10GField.szQuot_simple hb1 hkcard
    haveI := hs₀
    obtain ⟨θ₀, hθ₀⟩ := ggFixGeom_of_inn (I₀ := LargeEvenInnSet _) hna₀ hZ (fun φ hφ => hφ)
      (fun φ hφ => hφ) ((eZ.trans e₁.symm).trans (MulEquiv.subgroupCongr hfix))
    have hlab₀ : LargeEvenInLambda2 ⟨.twB2, 0, 2 * b + 1⟩ := by
      refine ⟨?_, ?_⟩
      · show 1 ≤ 2 * b + 1
        omega
      · show (0 : ℕ) = 0 ∧ Odd (2 * b + 1) ∧ 3 ≤ 2 * b + 1
        exact ⟨rfl, ⟨b, rfl⟩, by omega⟩
    refine fixAlt_of_raw hlab₀ ?_
    dsimp only [CFSG.Assembly.LargeEvenRawDatum]
    rw [show (2 * b + 1 - 1) / 2 = b by omega]
    exact ⟨k, inferInstance, inferInstance, hkcard, hs₀, hna₀, θ₀, hθ₀⟩

theorem cAll_geomBody_sz (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    MI.CAll ⟨.twB2, 0, n⟩ (GeomBody p ⟨.twB2, 0, n⟩) := by
  obtain ⟨a, rfl⟩ := hodd
  have ha : 1 ≤ a := by omega
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  rw [show (2 * a + 1 - 1) / 2 = a by omega] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ, geomBody_sz hp hp2 ha K hK⟩

end CFSG.LocalAnalysis.GLTheoremA.T156

end
