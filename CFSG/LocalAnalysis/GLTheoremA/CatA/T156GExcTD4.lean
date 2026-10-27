module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTriD4
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Lang.Coordinator CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.FR


theorem fixSub_td4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {F : Set (MulAut (LargeEvenCenterQuot
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)))} (hF : FQ.InnFree p F)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))}
    (hf : f ∈ F) (hord : orderOf f = p) :
    p ∣ n ∧ ∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀), Nat.card k₀ = (2 ^ (n / p)) ^ 3 ∧
      Nonempty (↥(FP.fixSub f) ≃*
        LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 k₀ LargeEvenRhoD4 (n / p))) := by
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hchev : ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
      .trialityD4 2 n :=
    ⟨⟨Nat.prime_two, hn, rfl⟩, twistedChevalleyModel_largeEven .D4 hK⟩
  obtain ⟨K', _, _, σ, hcard', hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn hchev.2
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  have hβp : MulAut.congr e f ^ p = 1 := by rw [← map_pow, hfp, map_one]
  have hβout : MulAut.congr e f ∉ inner (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hF f hf hord ((FQ.congr_mem_range_conj e f).1 hin)
  obtain ⟨f₀, k₀, hk₀F, hk₀fin, σ₀, hf0, hk₀card, hσ₀, hp3', ⟨eα⟩⟩ :=
    trialityD4_outer_fixed_equiv Nat.prime_two hn hp hp5 K' hcard' σ hσ (MulAut.congr e f) hβp hβout
  have hf1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf0; omega
    · exact h0
  have hdiv : n / p = f₀ := by rw [hf0, Nat.mul_div_cancel_left _ hp.pos]
  refine ⟨⟨f₀, by rw [hf0, mul_comm]⟩, ?_⟩
  obtain ⟨σ', hσ'', hσ'ord, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf1
    k₀ hk₀card
  obtain ⟨eR⟩ := recipe_equiv_graph k₀ f₀ hf1 hk₀card σ' hσ''
  have e₁ : ↥(FP.fixSub f) ≃* ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) :=
    (fixSubEquivCongr e f).trans eα
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have e₂ : Nonempty (↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 k₀ σ'.toRingHom)) := by
    rcases hj with hj | hj
    · have : σ₀ = σ' := RingEquiv.ext fun c => by rw [hσ₀, hσ'', hj, pow_one]
      subst this
      exact ⟨MulEquiv.refl _⟩
    · have hσ3 : σ' ^ 3 = 1 := by
        have := pow_orderOf_eq_one σ'
        rwa [hσ'ord] at this
      obtain ⟨eo⟩ := graph_orientation_equiv k₀ σ' hσ3
      have : σ₀ = σ' ^ 2 := RingEquiv.ext fun c => by
        rw [hσ₀, hj, show (σ' ^ 2) c = σ' (σ' c) by rw [pow_two]; rfl, hσ'', hσ'', sq (2 ^ f₀),
          pow_mul]
      subst this
      exact ⟨eo.symm⟩
  obtain ⟨e₂⟩ := e₂
  rw [hdiv]
  exact ⟨k₀, hk₀F, hk₀fin, hk₀card, ⟨(e₁.trans e₂).trans eR.symm⟩⟩

variable {p : ℕ}

theorem geomBody_td4 (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {n : ℕ} (hn : 1 ≤ n) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 3) :
    GeomBody p ⟨.triD4, 0, n⟩
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
      (LargeEvenChevIDImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
      (LargeEvenChevFieldImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) := by
  intro hS hna
  refine ⟨fun _ f hf hord => Or.inl ?_, fun _ h3 => absurd h3 hp3⟩
  have hF := Y10GField.innFree_of_ggRawInnField
    (RawAutTri.ggRawInnField_triD4 hn K hK hp.one_lt.ne') hS hna
  obtain ⟨hpn, k₀, _, _, hk₀, ⟨e⟩⟩ := fixSub_td4 hn hK hp hp2 hp3 hF hf hord
  have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hchev₀ : ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 k₀ LargeEvenRhoD4 (n / p)))
      .trialityD4 2 (n / p) :=
    ⟨⟨Nat.prime_two, hm, rfl⟩, twistedChevalleyModel_largeEven .D4 hk₀⟩
  obtain ⟨hs₀, hna₀⟩ := Y10GField.triD4_model_simple hchev₀
  haveI := hS
  haveI := hs₀
  have hZ := center_eq_bot_of_simple_noncomm hna
  have hfix : FP.fixSub f = ggFixSub f := Subgroup.ext fun _ => Iff.rfl
  obtain ⟨θ₀, hθ₀⟩ := ggFixGeom_of_inn hna₀ hZ
    (fun φ hφ => by
      have h1 := TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK hφ
      obtain ⟨r, hr⟩ := h1
      exact ⟨r, hr⟩)
    (fun _ ⟨x, hx⟩ => hx ▸ conj_mem_chevIDImage _ x)
    (e.symm.trans (MulEquiv.subgroupCongr hfix))
  exact fixAlt_of_raw (lab₀ := ⟨.triD4, 0, n / p⟩) ⟨hm, rfl⟩
    ⟨k₀, inferInstance, inferInstance, hk₀, hs₀, hna₀, θ₀, hθ₀⟩

theorem cAll_geomBody_td4 (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {n : ℕ} (hn : 1 ≤ n) :
    MI.CAll ⟨.triD4, 0, n⟩ (GeomBody p ⟨.triD4, 0, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  exact recipeTwisted_and (fun K _ _ hK => geomBody_td4 hp hp2 hp3 hn K hK) hQ

end CFSG.LocalAnalysis.GLTheoremA.T156

end
