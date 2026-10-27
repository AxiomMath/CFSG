module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutTriD4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.ComponentClassification.CatLeaf
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (card_projImage_glPi_three)
open CFSG.HardMathSupport.Dickson.Sec6 (FamTriD4 blueprintLieModel_trialityD4)
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (catalogIs_of_mulEquiv
  not_mem_range_conj_of_not_mem_innAutDerived)

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}


section Layer

theorem typeLayer_fieldActor_two_allW (hD : LieSOutTypeW T tm tf tN) {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    TypeLayer T (fieldActor (t := TwistTag.D4) σ σ) False := by
  haveI := finite_graphFixedRootGroup_D4 σ
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    refine typeLayer_of_card_dvd hD.card_eq _ (M := 12096) ?_ hD.ord.not_dvd_12096
    rw [card_fixSubgroup_fieldActor Nat.prime_two le_rfl hK σ hσ]
    norm_num [lieOrderNumerator]
  · obtain ⟨hs, hnab⟩ := simple_fixSubgroup_fieldActor_two h hK σ hσ
    refine typeLayer_of_fixed_equiv _ (MulEquiv.refl _) hs hnab fun hT => ?_
    have h1 := hD.card_eq hT
    rw [card_fixSubgroup_fieldActor Nat.prime_two (by omega) hK σ hσ] at h1
    have h4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
    simp only [lieOrderNumerator] at h1
    exact hD.ord.ne_g2 _ h4 h1.symm

theorem lieSOut_not_catalogIs_projImage_slPi_trueW (hD : LieSOutTypeW T tm tf tN) {f : ℕ}
    {K : Type} [Field K] (hK : PiField true 2 f K) :
    ¬ catalogIs ↥(projImage (slPi true 3 (2 ^ f) K)) T := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_projImage_slPi_true_equiv hK
  exact (KFacts.KS14.isEmpty_mulEquiv_projSL_three_of_card (hD.card_eq h) hD.ord.ne_sl3
    (GaloisField 2 f)).false e

theorem lieSOut_not_catalogIs_projImage_slPi_falseW (hD : LieSOutTypeW T tm tf tN) {f : ℕ}
    {K : Type} [Field K] (hK : PiField false 2 f K) :
    ¬ catalogIs ↥(projImage (slPi false 3 (2 ^ f) K)) T := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_projImage_slPi_false_equiv hK
  exact (KFacts.KS14.isEmpty_mulEquiv_projSU_three_of_card (hD.card_eq h) hD.ord.ne_su3 2 f
    hK.one_le).false e

theorem typeLayer_of_autFix_equiv_evenW (hD : LieSOutTypeW T tm tf tN) {f : ℕ} (hf : 1 ≤ f)
    (hfe : Even f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {P : Type} [Group P] [Finite P] (φ : MulAut P)
    (ef : ↥(fixSubgroup φ) ≃*
      ↥(Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ))) :
    TypeLayer T φ False := by
  obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf K σ hK hσ
  have hPi : PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
  have hf2 : 2 ≤ f := by
    obtain ⟨k, hk⟩ := hfe
    omega
  have hq2 : 2 < 2 ^ f :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact typeLayer_of_equiv_projImage hPi hq2 φ (ef.trans e₃) fun hT =>
    (lieSOut_not_catalogIs_projImage_slPi_trueW hD hPi hT).elim

theorem typeLayer_of_autFix_equiv_oddW (hD : LieSOutTypeW T tm tf tN) {f : ℕ} (hf : 1 ≤ f)
    (hfo : Odd f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {P : Type} [Group P] [Finite P] (φ : MulAut P)
    (ef : ↥(fixSubgroup φ) ≃*
      ↥(Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ))) :
    TypeLayer T φ False := by
  obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo K σ hK hσ
  have hPi : PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hf1 : f = 1
  · subst hf1
    refine typeLayer_of_card_dvd hD.card_eq φ (M := 216) ?_ hD.ord.not_dvd_216
    have h1 := card_projImage_glPi_three hPi
    rw [Nat.card_congr (ef.trans e₃).toEquiv, h1]
    norm_num
  · have hf3 : 3 ≤ f := by
      obtain ⟨k, hk⟩ := hfo
      omega
    have hq2 : 2 < 2 ^ f :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
    exact typeLayer_of_equiv_projImage hPi hq2 φ (ef.trans e₃) fun hT =>
      (lieSOut_not_catalogIs_projImage_slPi_falseW hD hPi hT).elim

theorem typeLayer_three_D4_outer_twoW (hD : LieSOutTypeW T tm tf tN) {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    TypeLayer T φ False := by
  haveI := finite_graphFixedRootGroup_D4 σ
  have hG2 : TypeLayer T (fieldActor (t := TwistTag.D4) σ σ) False :=
    typeLayer_fieldActor_two_allW hD hf hK σ hσ
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hφ3
    (by exact hφ) with ⟨β, hβ | hβ⟩ | ⟨⟨e₂⟩⟩
  · rw [hβ]
    exact typeLayer_conj β hG2
  · rw [hβ]
    exact typeLayer_conj β ((typeLayer_inv_iff _ _).2 hG2)
  · have hfix : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    have ef := (MulEquiv.subgroupCongr hfix).trans e₂
    rcases Nat.even_or_odd f with hfe | hfo
    · exact typeLayer_of_autFix_equiv_evenW hD hf hfe hK σ hσ φ ef
    · exact typeLayer_of_autFix_equiv_oddW hD hf hfo hK σ hσ φ ef

end Layer

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
