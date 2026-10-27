module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcDataTw

import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

variable {Ω : Type} [Group Ω] [Finite Ω]


private theorem excLang_twE6_marking_aux1 {p : ℕ} {X : Subgroup Ω} {x : Ω}
    {qc : TauCeti.PrimePower} (hqc : qc.p = 2) {hv : (LocalTwo.excIndex .twistedE6 qc).Valid}
    (hQ : catalogIs (PSimple p X) K155X.l154ExcTwE6)
    (e : PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex .twistedE6 qc, hv⟩)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ) (σ : K ≃+* K)
      (θ : PSimple p X ≃* CFSG.Assembly.LargeEvenCenterQuot (twistedE6RootGroup K σ))
      (φx : MulAut (CFSG.Assembly.LargeEvenCenterQuot (twistedE6RootGroup K σ))),
      CharP K 2 ∧ 1 ≤ n ∧ Nat.card K = (2 ^ n) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ n)) ∧
      2 ^ n = qc.card ∧
      φx ∈ CFSG.StandardType.RecipeExcLang.markIDImage (IsRoot TwistTag.E6.tag) K
        (twistedE6RootGroup K σ) ∧
      LargeEvenInduces θ (indRel p X x) φx := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p X)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p X x) φ :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hinn.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := MI.marking_transport (indRel p X x) hdiag hdiag
  have hlab : Y10F.HasLabel (PQuot p X) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have htag := K155X.excTwE6_tag_of_marking hlab hQ
  obtain ⟨K, instF, instFin, σ, hK, hσ, hQ'⟩ := K155X.excTwE6_raw_of_label htag hΛ.1 hraw
  obtain ⟨-, -, θ, -, hrel⟩ := hQ'
  obtain ⟨φ, hφ, hix⟩ := hrel
  have hcanon : (canonLabel lab).n = lab.n := by
    obtain ⟨t, r, k⟩ := lab
    cases htag
    rfl
  have hfield : 2 ^ (canonLabel lab).n = qc.card :=
    CanonSubcomp.two_pow_canonLabel_n_of_lie CFSG.StandardType.ggLabelRigidInput_holds hlab
      ⟨LocalTwo.excIndex .twistedE6 qc, hv⟩
      (by show (TauCeti.LieTypeIndex.twistedE6 qc).characteristic = 2; simp [hqc]) e
  have hpow : 2 ^ lab.n = qc.card := by
    rw [hcanon] at hfield
    exact hfield
  exact ⟨K, instF, instFin, lab.n, σ, θ, φ,
    CFSG.StandardType.charP_two_of_card (m := lab.n * 2) (by rw [hK, pow_mul]), hΛ.1, hK, hσ,
    hpow, hφ, hix⟩

private theorem excLang_twE6_marking_aux3 {p : ℕ} {X : Subgroup Ω} {x : Ω}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {θ : PSimple p X ≃* ↥(twistedE6RootGroup K σ)}
    {w : CFSG.StandardType.RecipeExcLang.twInndiagGroup K σ}
    (hθx : LargeEvenInduces θ (indRel p X x) (CFSG.StandardType.RecipeExcLang.twConj K σ w))
    (hX : CFSG.Open.IsQuasisimple ↥X) (hxN : x ∈ Subgroup.normalizer (X : Set Ω))
    (hcm : ¬ CentMod p X x) :
    (w : ModGL TwistTag.E6.tag K) ≠ 1 := by
  intro hw1
  have hw1' : w = 1 := Subtype.ext hw1
  have h1 : CFSG.StandardType.RecipeExcLang.twConj K σ w = 1 := by
    rw [hw1']; exact map_one _
  exact hcm (K155X.l154_centMod_of_induces_one hX.1 hxN θ (h1 ▸ hθx))

private theorem excLang_twE6_marking_aux2 {p : ℕ} {X : Subgroup Ω} {x : Ω} {qc : TauCeti.PrimePower}
    {K : Type} [Field K] [Finite K] {n : ℕ} {σ : K ≃+* K}
    {θ₀ : PSimple p X ≃* CFSG.Assembly.LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {φx₀ : MulAut (CFSG.Assembly.LargeEvenCenterQuot (twistedE6RootGroup K σ))}
    (hchar : CharP K 2) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpow : 2 ^ n = qc.card)
    (hφx : φx₀ ∈ CFSG.StandardType.RecipeExcLang.markIDImage (IsRoot TwistTag.E6.tag) K
      (twistedE6RootGroup K σ))
    (hix : LargeEvenInduces θ₀ (indRel p X x) φx₀)
    (hX : CFSG.Open.IsQuasisimple ↥X) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (θ : PSimple p X ≃* ↥(twistedE6RootGroup K σ)) (φx : MulAut ↥(twistedE6RootGroup K σ))
      (h : ModGL TwistTag.E6.tag K),
      CharP K 2 ∧ Nat.card K = qc.card ^ 2 ∧ (∀ c, σ c = c ^ qc.card) ∧ h ∈ twistedE6InndiagGL K σ ∧
      h ^ p = 1 ∧ h ≠ 1 ∧ (∀ c, (φx c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) ∧
      LargeEvenInduces θ (indRel p X x) φx := by
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  obtain ⟨w, hwx⟩ := K155X.excTwE6_exists_twConj_of_mem_markID σ hφx
  have hθx : LargeEvenInduces (θ₀.trans (CFSG.StandardType.centerQuotEquivOfBot hZ))
      (indRel p X x) (CFSG.StandardType.RecipeExcLang.twConj K σ w) := by
    have hθ := K155X.excUntw_induces_trans θ₀ (CFSG.StandardType.centerQuotEquivOfBot hZ) hix
    rw [hwx] at hθ
    exact hθ
  have hwp : w ^ p = 1 := by
    have h1 := K155X.excUntw_induces_pow_eq_one hxN hxp
      (θ₀.trans (CFSG.StandardType.centerQuotEquivOfBot hZ)) hθx
    rw [← map_pow] at h1
    exact CFSG.StandardType.NoOffTwE6Three.twConj_injective hn hK σ hσ
      (h1.trans (map_one _).symm)
  have hhne : (w : ModGL TwistTag.E6.tag K) ≠ 1 :=
    excLang_twE6_marking_aux3 hθx hX hxN hcm
  refine ⟨K, inferInstance, inferInstance, σ, θ₀.trans (CFSG.StandardType.centerQuotEquivOfBot hZ),
    CFSG.StandardType.RecipeExcLang.twConj K σ w, (w : ModGL TwistTag.E6.tag K),
    hchar, ?_, ?_, CFSG.StandardType.NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2,
    ?_, hhne, fun c => CFSG.StandardType.RecipeExcLang.coe_twConj σ w c, hθx⟩
  · rw [hK, hpow]
  · intro c; rw [hσ c, hpow]
  · rw [← Subgroup.coe_pow, hwp]; rfl

theorem excLang_twE6_marking {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup Ω} {x : Ω}
    {qc : TauCeti.PrimePower} (hqc : qc.p = 2) {hv : (LocalTwo.excIndex .twistedE6 qc).Valid}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex .twistedE6 qc, hv⟩))
    (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (θ : PSimple p X ≃* ↥(twistedE6RootGroup K σ)) (φx : MulAut ↥(twistedE6RootGroup K σ))
      (h : ModGL TwistTag.E6.tag K),
      CharP K 2 ∧ Nat.card K = qc.card ^ 2 ∧ (∀ c, σ c = c ^ qc.card) ∧ h ∈ twistedE6InndiagGL K σ ∧
      h ^ p = 1 ∧ h ≠ 1 ∧ (∀ c, (φx c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) ∧
      LargeEvenInduces θ (indRel p X x) φx := by
  obtain ⟨e⟩ := hcat
  have hQ : catalogIs (PSimple p X) K155X.l154ExcTwE6 :=
    ⟨.lie ⟨LocalTwo.excIndex .twistedE6 qc, hv⟩, hqc, ⟨e⟩⟩
  obtain ⟨K, instF, instFin, n, σ, θ₀, φx₀, hchar, hn, hK, hσ, hpow, hφx, hix⟩ :=
    excLang_twE6_marking_aux1 hqc hQ e hinn
  exact excLang_twE6_marking_aux2 hchar hn hK hσ hpow hφx hix hX hxp hxN hcm


end CFSG.LocalAnalysis.GLTheoremA.I167

end
