module

import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcData

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


private theorem excLang_untw_marking_aux_pow {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : Nat.card K = 2) {p : ℕ} {w : CFSG.StandardType.RecipeExcLang.inndiagGroup τ K}
    (h : (CFSG.StandardType.RecipeExcLang.inndiagConj τ K w) ^ p = 1) : w ^ p = 1 := by
  haveI : Subsingleton Kˣ := by
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units K, hK2]
    exact (Nat.card_eq_one_iff_unique.mp h1).1
  obtain ⟨b, j, hj, hw⟩ := w.2
  have hb : b = fun _ => 1 := funext fun i => Subsingleton.elim (b i) 1
  have hwj : (w : ModGL τ K) = j := by
    rw [hw, hb]
    change rootDiagUnit τ (1 : Fin τ.rank → Kˣ) * j = j
    rw [rootDiagUnit_one, one_mul]
  let j' : ↥(adjointGroup τ K) := ⟨j, hj⟩
  have hw' : w = ⟨j', CFSG.StandardType.RecipeExcLang.adjointGroup_le_inndiagGroup j'.2⟩ :=
    Subtype.ext hwj
  rw [hw', CFSG.StandardType.RecipeExcLang.inndiagConj_of_mem] at h
  have hjp : j' ^ p = 1 :=
    CFSG.SeitzReduction.mulAut_conj_injective_of_center_eq_bot
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (by rw [map_pow, h, map_one])
  have hjpow : j ^ p = 1 := by
    have hc := congrArg (fun x : ↥(adjointGroup τ K) => (x : ModGL τ K)) hjp
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hc
  exact Subtype.ext (by rw [Subgroup.coe_pow, hwj, hjpow]; rfl)

private theorem excLang_untw_marking_aux_diag {p : ℕ} {Ω : Type} [Group Ω] {X : Subgroup Ω} {x : Ω}
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    CFSG.Assembly.LargeEvenMarking (PQuot p X)
      (fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p X x) φ) :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono
    (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hinn.2

private theorem excLang_untw_marking_aux_exc {labm : GLALabel} {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (h : CFSG.StandardType.markTag labm = t) :
    CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcGLATag labm := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact CFSG.LocalAnalysis.GLTheoremA.K1419E.excGLATag_of_markTag (Or.inr (Or.inl rfl)) h
  · exact CFSG.LocalAnalysis.GLTheoremA.K1419E.excGLATag_of_markTag (Or.inr (Or.inr (Or.inl rfl))) h
  · exact CFSG.LocalAnalysis.GLTheoremA.K1419E.excGLATag_of_markTag (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
  · exact CFSG.LocalAnalysis.GLTheoremA.K1419E.excGLATag_of_markTag (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h

private theorem excLang_untw_marking_aux_four {K : Type} [Field K] [Finite K] {qc : TauCeti.PrimePower}
    (hqc : qc.p = 2) (hK : Nat.card K = qc.card) (hK2 : Nat.card K ≠ 2) : 4 ≤ Nat.card K := by
  have hcard : Nat.card K = 2 ^ qc.exponent := by rw [hK, TauCeti.PrimePower.card_def, hqc]
  have hexp2 : 2 ≤ qc.exponent := by
    by_contra hc
    have h1 : qc.exponent = 1 := by have := qc.exponent_pos; omega
    exact hK2 (by rw [hcard, h1]; norm_num)
  rw [hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ qc.exponent := Nat.pow_le_pow_right (by norm_num) hexp2

private theorem excLang_untw_marking_aux_lab {X : Type} [Group X] {lab labm : GLALabel}
    (hlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel X (· = lab))
    (hlabm : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel X (· = labm))
    (hEm : CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcGLATag labm) : lab = labm := by
  have h1 := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlabm
  have h2 := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlab
  exact CFSG.LocalAnalysis.GLTheoremA.K1419E.eq_of_ggLabelIso_exc
    (CFSG.StandardType.ggLabelRigidInput_holds labm lab (X ⧸ Subgroup.center X)
      h1.1 h2.1 h1.2.2 h2.2.2) hEm

private theorem excLang_untw_marking_aux0 {p : ℕ} {Ω : Type} [Group Ω] {X : Subgroup Ω} {x : Ω}
    {k : DefChar.LieFamily} {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    (hperfX : commutator ↥X = ⊤) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    {τ : Tag} (hτ : τ = excTag k) {K : Type} [Field K] [Finite K] (hK : Nat.card K = qc.card)
    (θ₀ : PSimple p X ≃* CFSG.Assembly.LargeEvenCenterQuot (adjointGroup τ K))
    (φ₀ : MulAut (CFSG.Assembly.LargeEvenCenterQuot (adjointGroup τ K)))
    (hφ₀ : φ₀ ∈ CFSG.StandardType.RecipeExcLang.markIDImage (IsRoot τ) K (adjointGroup τ K))
    (hix₀ : LargeEvenInduces θ₀ (indRel p X x) φ₀) :
    ∃ (θ : PSimple p X ≃* ↥(adjointGroup τ K)) (φx : MulAut ↥(adjointGroup τ K))
      (h : ModGL τ K),
      h ^ p = 1 ∧ h ≠ 1 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈ adjointGroup τ (AlgebraicClosure K) ∧
      (∀ c, (φx c : ModGL τ K) = h * c * h⁻¹) ∧
      LargeEvenInduces θ (indRel p X x) φx := by
  obtain ⟨w, hw⟩ := CFSG.StandardType.RecipeExcLang.exists_inndiagConj_of_mem_markID hφ₀
  have h1x := K155X.excUntw_induces_trans θ₀
    (CFSG.StandardType.centerQuotEquivOfBot CFSG.LieType.Chevalley.center_adjointGroup_eq_bot) hix₀
  change LargeEvenInduces _ _ (CFSG.StandardType.RecipeExcLang.autEquiv τ K φ₀) at h1x
  rw [hw] at h1x
  let θ : PSimple p X ≃* ↥(adjointGroup τ K) :=
    θ₀.trans (CFSG.StandardType.centerQuotEquivOfBot CFSG.LieType.Chevalley.center_adjointGroup_eq_bot)
  let φx : MulAut ↥(adjointGroup τ K) := CFSG.StandardType.RecipeExcLang.inndiagConj τ K w
  let h : ModGL τ K := (w : ModGL τ K)
  have h1x' : LargeEvenInduces θ (indRel p X x) φx := h1x
  have hwp : w ^ p = 1 := by
    by_cases hK2 : Nat.card K = 2
    · exact excLang_untw_marking_aux_pow hK2 (K155X.excUntw_induces_pow_eq_one hxN hxp θ h1x')
    · exact K155X.excUntw_pow_eq_one_of_induces
        (excLang_untw_marking_aux_four hqc hK hK2) hxN hxp θ h1x'
  have hhp : h ^ p = 1 := by
    have hcast : h ^ p = ((w ^ p : CFSG.StandardType.RecipeExcLang.inndiagGroup τ K) : ModGL τ K) := by
      rw [show h = (w : ModGL τ K) from rfl, Subgroup.coe_pow]
    rw [hcast, hwp]; rfl
  have hh1 : h ≠ 1 := by
    intro h1
    have hw1 : w = 1 := Subtype.ext (show (w : ModGL τ K) = 1 from h1)
    have hφ1 : φx = 1 := by
      show CFSG.StandardType.RecipeExcLang.inndiagConj τ K w = 1
      rw [hw1, map_one]
    exact hcm (K155X.l154_centMod_of_induces_one hperfX hxN θ (hφ1 ▸ h1x'))
  have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈ adjointGroup τ (AlgebraicClosure K) :=
    CFSG.StandardType.RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag
      (algebraMap K (AlgebraicClosure K)) w.2
  exact ⟨θ, φx, h, hhp, hh1, hbc, fun c => CFSG.StandardType.RecipeExcLang.coe_inndiagConj w c, h1x'⟩

private theorem excLang_untw_marking_aux0b {p : ℕ} {Ω : Type} [Group Ω] {X : Subgroup Ω} {x : Ω}
    {k : DefChar.LieFamily} {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    (hperfX : commutator ↥X = ⊤) {K : Type} [Field K] [Finite K] (hK : Nat.card K = qc.card)
    {τ : Tag} (hτ : τ = excTag k)
    {θ : PSimple p X ≃* ↥(adjointGroup τ K)} {φx : MulAut ↥(adjointGroup τ K)} {h : ModGL τ K}
    (hhp : h ^ p = 1) (hh1 : h ≠ 1)
    (hbc : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈ adjointGroup τ (AlgebraicClosure K))
    (hconj : ∀ c, (φx c : ModGL τ K) = h * c * h⁻¹)
    (hind : LargeEvenInduces θ (indRel p X x) φx) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (θ : PSimple p X ≃* ↥(adjointGroup (excTag k) K))
      (φx : MulAut ↥(adjointGroup (excTag k) K)) (h : ModGL (excTag k) K),
      CharP K 2 ∧ Nat.card K = qc.card ∧ commutator ↥(adjointGroup (excTag k) K) = ⊤ ∧
      h ^ p = 1 ∧ h ≠ 1 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈ adjointGroup (excTag k) (AlgebraicClosure K) ∧
      (∀ c, (φx c : ModGL (excTag k) K) = h * c * h⁻¹) ∧
      LargeEvenInduces θ (indRel p X x) φx := by
  have hcard : Nat.card K = 2 ^ qc.exponent := by rw [hK, TauCeti.PrimePower.card_def, hqc]
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hcard
  haveI : Group.IsPerfect ↥X := ⟨hperfX⟩
  haveI : Group.IsPerfect (PQuot p X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (GLAPPrimeCore p ↥X))
      (QuotientGroup.mk'_surjective _)
  haveI : Group.IsPerfect (PSimple p X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p X)))
      (QuotientGroup.mk'_surjective _)
  haveI : Group.IsPerfect ↥(adjointGroup τ K) :=
    Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective
  subst hτ
  exact ⟨K, inferInstance, inferInstance, θ, φx, h, inferInstance, hK,
    Group.IsPerfect.commutator_eq_top, hhp, hh1, hbc, hconj, hind⟩

private theorem excLang_untw_marking_aux1 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {X : Subgroup Ω} {x : Ω} {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    {hv : (LocalTwo.excIndex .F4 qc).Valid} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex .F4 qc, hv⟩))
    (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (θ₀ : PSimple p X ≃* CFSG.Assembly.LargeEvenCenterQuot (adjointGroup .F4 K))
      (φ₀ : MulAut (CFSG.Assembly.LargeEvenCenterQuot (adjointGroup .F4 K))),
      Nat.card K = qc.card ∧
      φ₀ ∈ CFSG.StandardType.RecipeExcLang.markIDImage (IsRoot .F4) K (adjointGroup .F4 K) ∧
      LargeEvenInduces θ₀ (indRel p X x) φ₀ := by
  have hdiag := excLang_untw_marking_aux_diag hinn
  have hperf : commutator (PQuot p X) = ⊤ := hdiag.1
  obtain ⟨e⟩ := hcat
  have hm : CFSG.Blueprint.LieModel (PSimple p X) .F4 0 2 qc.exponent :=
    hqc ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_F4 qc hv e
  have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hm
  obtain ⟨labm, ⟨htagm, -, -, -⟩, hlabm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K144I.exists_label_of_hasLabel hmark
  have hboth := MI.marking_transport (indRel p X x) hdiag hmark
  obtain ⟨-, lab, hΛ, hraw⟩ := hboth
  have hlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel (PQuot p X) (· = lab) :=
    ⟨hperf, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hEm := excLang_untw_marking_aux_exc (t := .F4) (Or.inl rfl) htagm
  have heq : lab = labm := excLang_untw_marking_aux_lab hlab hlabm hEm
  have htagm' : CFSG.StandardType.markTag lab = .F4 := heq.symm ▸ htagm
  obtain ⟨tg, r, nlab⟩ := lab
  have htg : tg = .F4 := by
    revert htagm'
    cases tg <;> simp [CFSG.StandardType.markTag] <;> split_ifs <;> simp_all
  subst htg
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨K, instF, instFin, hK0, hQ⟩ := hraw
  set Q : CFSG.Assembly.LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : PQuot p X ⧸ Subgroup.center (PQuot p X) ≃* R,
        (CFSG.StandardType.markTag ⟨.F4, r, nlab⟩ = .F4 ∧ CFSG.StandardType.markRank ⟨.F4, r, nlab⟩ = 0 ∧
          CFSG.StandardType.markChar ⟨.F4, r, nlab⟩ = 2 ∧ CFSG.StandardType.markDeg ⟨.F4, r, nlab⟩ = qc.exponent) ∧
        ∃ φ ∈ I, LargeEvenInduces θ (indRel p X x) φ with hQdef
  have hQ' := K155X.excUntw_chev_transport (τ := .F4) (K := K) (Q := Q) hQ
  obtain ⟨-, hrest⟩ := hQ'
  obtain ⟨-, hC⟩ := hrest
  obtain ⟨θ₀, hP₀⟩ := hC
  obtain ⟨hP, φ₀, hφ₀, hix₀⟩ := hP₀
  obtain ⟨-, -, -, hdeg'⟩ := hP
  have hn : nlab = qc.exponent := by simpa [CFSG.StandardType.markDeg] using hdeg'
  refine ⟨K, instF, instFin, θ₀, φ₀, ?_, hφ₀, hix₀⟩
  rw [hK0, hn, TauCeti.PrimePower.card_def, hqc]

private theorem excLang_untw_marking_aux2 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {X : Subgroup Ω} {x : Ω} {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    {hv : (LocalTwo.excIndex .E6 qc).Valid} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex .E6 qc, hv⟩))
    (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (θ₀ : PSimple p X ≃* CFSG.Assembly.LargeEvenCenterQuot (adjointGroup .E6 K))
      (φ₀ : MulAut (CFSG.Assembly.LargeEvenCenterQuot (adjointGroup .E6 K))),
      Nat.card K = qc.card ∧
      φ₀ ∈ CFSG.StandardType.RecipeExcLang.markIDImage (IsRoot .E6) K (adjointGroup .E6 K) ∧
      LargeEvenInduces θ₀ (indRel p X x) φ₀ := by
  have hdiag := excLang_untw_marking_aux_diag hinn
  have hperf : commutator (PQuot p X) = ⊤ := hdiag.1
  obtain ⟨e⟩ := hcat
  have hm : CFSG.Blueprint.LieModel (PSimple p X) .E6 0 2 qc.exponent :=
    hqc ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E6 qc hv e
  have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hm
  obtain ⟨labm, ⟨htagm, -, -, -⟩, hlabm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K144I.exists_label_of_hasLabel hmark
  have hboth := MI.marking_transport (indRel p X x) hdiag hmark
  obtain ⟨-, lab, hΛ, hraw⟩ := hboth
  have hlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel (PQuot p X) (· = lab) :=
    ⟨hperf, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hEm := excLang_untw_marking_aux_exc (t := .E6) (Or.inr (Or.inl rfl)) htagm
  have heq : lab = labm := excLang_untw_marking_aux_lab hlab hlabm hEm
  have htagm' : CFSG.StandardType.markTag lab = .E6 := heq.symm ▸ htagm
  obtain ⟨tg, r, nlab⟩ := lab
  have htg : tg = .E6 := by
    revert htagm'
    cases tg <;> simp [CFSG.StandardType.markTag] <;> split_ifs <;> simp_all
  subst htg
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨K, instF, instFin, hK0, hQ⟩ := hraw
  set Q : CFSG.Assembly.LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : PQuot p X ⧸ Subgroup.center (PQuot p X) ≃* R,
        (CFSG.StandardType.markTag ⟨.E6, r, nlab⟩ = .E6 ∧ CFSG.StandardType.markRank ⟨.E6, r, nlab⟩ = 0 ∧
          CFSG.StandardType.markChar ⟨.E6, r, nlab⟩ = 2 ∧ CFSG.StandardType.markDeg ⟨.E6, r, nlab⟩ = qc.exponent) ∧
        ∃ φ ∈ I, LargeEvenInduces θ (indRel p X x) φ with hQdef
  have hQ' := K155X.excUntw_chev_transport (τ := .E6) (K := K) (Q := Q) hQ
  obtain ⟨-, hrest⟩ := hQ'
  obtain ⟨-, hC⟩ := hrest
  obtain ⟨θ₀, hP₀⟩ := hC
  obtain ⟨hP, φ₀, hφ₀, hix₀⟩ := hP₀
  obtain ⟨-, -, -, hdeg'⟩ := hP
  have hn : nlab = qc.exponent := by simpa [CFSG.StandardType.markDeg] using hdeg'
  refine ⟨K, instF, instFin, θ₀, φ₀, ?_, hφ₀, hix₀⟩
  rw [hK0, hn, TauCeti.PrimePower.card_def, hqc]

private theorem excLang_untw_marking_aux3 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {X : Subgroup Ω} {x : Ω} {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    {hv : (LocalTwo.excIndex .E7 qc).Valid} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex .E7 qc, hv⟩))
    (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (θ₀ : PSimple p X ≃* CFSG.Assembly.LargeEvenCenterQuot (adjointGroup .E7 K))
      (φ₀ : MulAut (CFSG.Assembly.LargeEvenCenterQuot (adjointGroup .E7 K))),
      Nat.card K = qc.card ∧
      φ₀ ∈ CFSG.StandardType.RecipeExcLang.markIDImage (IsRoot .E7) K (adjointGroup .E7 K) ∧
      LargeEvenInduces θ₀ (indRel p X x) φ₀ := by
  have hdiag := excLang_untw_marking_aux_diag hinn
  have hperf : commutator (PQuot p X) = ⊤ := hdiag.1
  obtain ⟨e⟩ := hcat
  have hm : CFSG.Blueprint.LieModel (PSimple p X) .E7 0 2 qc.exponent :=
    hqc ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E7 qc hv e
  have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hm
  obtain ⟨labm, ⟨htagm, -, -, -⟩, hlabm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K144I.exists_label_of_hasLabel hmark
  have hboth := MI.marking_transport (indRel p X x) hdiag hmark
  obtain ⟨-, lab, hΛ, hraw⟩ := hboth
  have hlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel (PQuot p X) (· = lab) :=
    ⟨hperf, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hEm := excLang_untw_marking_aux_exc (t := .E7) (Or.inr (Or.inr (Or.inl rfl))) htagm
  have heq : lab = labm := excLang_untw_marking_aux_lab hlab hlabm hEm
  have htagm' : CFSG.StandardType.markTag lab = .E7 := heq.symm ▸ htagm
  obtain ⟨tg, r, nlab⟩ := lab
  have htg : tg = .E7 := by
    revert htagm'
    cases tg <;> simp [CFSG.StandardType.markTag] <;> split_ifs <;> simp_all
  subst htg
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨K, instF, instFin, hK0, hQ⟩ := hraw
  set Q : CFSG.Assembly.LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : PQuot p X ⧸ Subgroup.center (PQuot p X) ≃* R,
        (CFSG.StandardType.markTag ⟨.E7, r, nlab⟩ = .E7 ∧ CFSG.StandardType.markRank ⟨.E7, r, nlab⟩ = 0 ∧
          CFSG.StandardType.markChar ⟨.E7, r, nlab⟩ = 2 ∧ CFSG.StandardType.markDeg ⟨.E7, r, nlab⟩ = qc.exponent) ∧
        ∃ φ ∈ I, LargeEvenInduces θ (indRel p X x) φ with hQdef
  have hQ' := K155X.excUntw_chev_transport (τ := .E7) (K := K) (Q := Q) hQ
  obtain ⟨-, hrest⟩ := hQ'
  obtain ⟨-, hC⟩ := hrest
  obtain ⟨θ₀, hP₀⟩ := hC
  obtain ⟨hP, φ₀, hφ₀, hix₀⟩ := hP₀
  obtain ⟨-, -, -, hdeg'⟩ := hP
  have hn : nlab = qc.exponent := by simpa [CFSG.StandardType.markDeg] using hdeg'
  refine ⟨K, instF, instFin, θ₀, φ₀, ?_, hφ₀, hix₀⟩
  rw [hK0, hn, TauCeti.PrimePower.card_def, hqc]

private theorem excLang_untw_marking_aux4 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {X : Subgroup Ω} {x : Ω} {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    {hv : (LocalTwo.excIndex .E8 qc).Valid} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex .E8 qc, hv⟩))
    (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (θ₀ : PSimple p X ≃* CFSG.Assembly.LargeEvenCenterQuot (adjointGroup .E8 K))
      (φ₀ : MulAut (CFSG.Assembly.LargeEvenCenterQuot (adjointGroup .E8 K))),
      Nat.card K = qc.card ∧
      φ₀ ∈ CFSG.StandardType.RecipeExcLang.markIDImage (IsRoot .E8) K (adjointGroup .E8 K) ∧
      LargeEvenInduces θ₀ (indRel p X x) φ₀ := by
  have hdiag := excLang_untw_marking_aux_diag hinn
  have hperf : commutator (PQuot p X) = ⊤ := hdiag.1
  obtain ⟨e⟩ := hcat
  have hm : CFSG.Blueprint.LieModel (PSimple p X) .E8 0 2 qc.exponent :=
    hqc ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E8 qc hv e
  have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hm
  obtain ⟨labm, ⟨htagm, -, -, -⟩, hlabm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K144I.exists_label_of_hasLabel hmark
  have hboth := MI.marking_transport (indRel p X x) hdiag hmark
  obtain ⟨-, lab, hΛ, hraw⟩ := hboth
  have hlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel (PQuot p X) (· = lab) :=
    ⟨hperf, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hEm := excLang_untw_marking_aux_exc (t := .E8) (Or.inr (Or.inr (Or.inr rfl))) htagm
  have heq : lab = labm := excLang_untw_marking_aux_lab hlab hlabm hEm
  have htagm' : CFSG.StandardType.markTag lab = .E8 := heq.symm ▸ htagm
  obtain ⟨tg, r, nlab⟩ := lab
  have htg : tg = .E8 := by
    revert htagm'
    cases tg <;> simp [CFSG.StandardType.markTag] <;> split_ifs <;> simp_all
  subst htg
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨K, instF, instFin, hK0, hQ⟩ := hraw
  set Q : CFSG.Assembly.LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : PQuot p X ⧸ Subgroup.center (PQuot p X) ≃* R,
        (CFSG.StandardType.markTag ⟨.E8, r, nlab⟩ = .E8 ∧ CFSG.StandardType.markRank ⟨.E8, r, nlab⟩ = 0 ∧
          CFSG.StandardType.markChar ⟨.E8, r, nlab⟩ = 2 ∧ CFSG.StandardType.markDeg ⟨.E8, r, nlab⟩ = qc.exponent) ∧
        ∃ φ ∈ I, LargeEvenInduces θ (indRel p X x) φ with hQdef
  have hQ' := K155X.excUntw_chev_transport (τ := .E8) (K := K) (Q := Q) hQ
  obtain ⟨-, hrest⟩ := hQ'
  obtain ⟨-, hC⟩ := hrest
  obtain ⟨θ₀, hP₀⟩ := hC
  obtain ⟨hP, φ₀, hφ₀, hix₀⟩ := hP₀
  obtain ⟨-, -, -, hdeg'⟩ := hP
  have hn : nlab = qc.exponent := by simpa [CFSG.StandardType.markDeg] using hdeg'
  refine ⟨K, instF, instFin, θ₀, φ₀, ?_, hφ₀, hix₀⟩
  rw [hK0, hn, TauCeti.PrimePower.card_def, hqc]

private theorem excLang_untw_marking_aux_case {p : ℕ} {X : Subgroup Ω} {x : Ω}
    {k : DefChar.LieFamily} (hk : k = .F4 ∨ k = .E6 ∨ k = .E7 ∨ k = .E8)
    {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    {hv : (LocalTwo.excIndex k qc).Valid} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex k qc, hv⟩)) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (θ : PSimple p X ≃* ↥(adjointGroup (excTag k) K))
      (φx : MulAut ↥(adjointGroup (excTag k) K)) (h : ModGL (excTag k) K),
      CharP K 2 ∧ Nat.card K = qc.card ∧ commutator ↥(adjointGroup (excTag k) K) = ⊤ ∧
      h ^ p = 1 ∧ h ≠ 1 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
        adjointGroup (excTag k) (AlgebraicClosure K) ∧
      (∀ c, (φx c : ModGL (excTag k) K) = h * c * h⁻¹) ∧
      LargeEvenInduces θ (indRel p X x) φx := by
  rcases hk with rfl | rfl | rfl | rfl
  · obtain ⟨K, instF, instFin, θ₀, φ₀, hK, hφ₀, hix₀⟩ :=
      excLang_untw_marking_aux1 hqc hX hcat hxp hxN hcm hinn
    obtain ⟨θ, φx, h, hhp, hh1, hbc, hconj, hind⟩ :=
      excLang_untw_marking_aux0 (τ := .F4) (k := .F4) hqc hX.1 hxp hxN hcm rfl hK θ₀ φ₀ hφ₀ hix₀
    exact excLang_untw_marking_aux0b (k := .F4) hqc hX.1 hK rfl hhp hh1 hbc hconj hind
  · obtain ⟨K, instF, instFin, θ₀, φ₀, hK, hφ₀, hix₀⟩ :=
      excLang_untw_marking_aux2 hqc hX hcat hxp hxN hcm hinn
    obtain ⟨θ, φx, h, hhp, hh1, hbc, hconj, hind⟩ :=
      excLang_untw_marking_aux0 (τ := .E6) (k := .E6) hqc hX.1 hxp hxN hcm rfl hK θ₀ φ₀ hφ₀ hix₀
    exact excLang_untw_marking_aux0b (k := .E6) hqc hX.1 hK rfl hhp hh1 hbc hconj hind
  · obtain ⟨K, instF, instFin, θ₀, φ₀, hK, hφ₀, hix₀⟩ :=
      excLang_untw_marking_aux3 hqc hX hcat hxp hxN hcm hinn
    obtain ⟨θ, φx, h, hhp, hh1, hbc, hconj, hind⟩ :=
      excLang_untw_marking_aux0 (τ := .E7) (k := .E7) hqc hX.1 hxp hxN hcm rfl hK θ₀ φ₀ hφ₀ hix₀
    exact excLang_untw_marking_aux0b (k := .E7) hqc hX.1 hK rfl hhp hh1 hbc hconj hind
  · obtain ⟨K, instF, instFin, θ₀, φ₀, hK, hφ₀, hix₀⟩ :=
      excLang_untw_marking_aux4 hqc hX hcat hxp hxN hcm hinn
    obtain ⟨θ, φx, h, hhp, hh1, hbc, hconj, hind⟩ :=
      excLang_untw_marking_aux0 (τ := .E8) (k := .E8) hqc hX.1 hxp hxN hcm rfl hK θ₀ φ₀ hφ₀ hix₀
    exact excLang_untw_marking_aux0b (k := .E8) hqc hX.1 hK rfl hhp hh1 hbc hconj hind

theorem excLang_untw_marking {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup Ω} {x : Ω} {k : DefChar.LieFamily}
    (hk : k = .F4 ∨ k = .E6 ∨ k = .E7 ∨ k = .E8) {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    {hv : (LocalTwo.excIndex k qc).Valid} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex k qc, hv⟩)) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (θ : PSimple p X ≃* ↥(adjointGroup (excTag k) K))
      (φx : MulAut ↥(adjointGroup (excTag k) K)) (h : ModGL (excTag k) K),
      CharP K 2 ∧ Nat.card K = qc.card ∧ commutator ↥(adjointGroup (excTag k) K) = ⊤ ∧
      h ^ p = 1 ∧ h ≠ 1 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
        adjointGroup (excTag k) (AlgebraicClosure K) ∧
      (∀ c, (φx c : ModGL (excTag k) K) = h * c * h⁻¹) ∧
      LargeEvenInduces θ (indRel p X x) φx := by
  exact excLang_untw_marking_aux_case hk hqc hX hcat hxp hxN hcm hinn


end CFSG.LocalAnalysis.GLTheoremA.I167

end
