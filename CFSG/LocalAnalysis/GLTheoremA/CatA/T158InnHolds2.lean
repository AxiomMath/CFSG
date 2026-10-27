module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniSig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRedV
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcFixG2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcFixE6All
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTriD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwB2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCanon
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn2
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Facts
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158Inn

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2)
open CFSG.StandardType (markTag markRank markChar markDeg)

private theorem t158Inn_eq_twA_two_three {lab : LargeEvenLabel} (ht : markTag lab = .PSU)
    (hr : markRank lab = 3) (hc : markChar lab = 2) (hf : markDeg lab = 3) :
    lab = ⟨.twA, 2, 3⟩ := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [markTag, markRank, markChar, markDeg] at ht hr hc hf <;>
    (try split_ifs at ht hr hc hf) <;> simp_all

private theorem t158Inn_twA_two_of_canonLabel {lab : LargeEvenLabel}
    (h : (canonLabel lab).tag = .twA ∧ (canonLabel lab).rank = 2) :
    lab.tag = .twA ∧ lab.rank = 2 := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [canonLabel] at h ⊢ <;> (try split_ifs at h) <;> simp_all

private theorem t158Inn_eight_eq (q : TauCeti.PrimePower) (h : q.card = 8) : q.p = 2 ∧ q.exponent = 3 := by
  have hdvd : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  rw [h] at hdvd
  have h2 : q.p ∣ 2 := q.prime_p.dvd_of_dvd_pow (n := 3) (by norm_num; exact hdvd)
  have hp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h2
  refine ⟨hp, ?_⟩
  have h8 : q.p ^ q.exponent = 8 := (TauCeti.PrimePower.card_def q).symm.trans h
  rw [hp, show (8 : ℕ) = 2 ^ 3 by norm_num] at h8
  exact Nat.pow_right_injective le_rfl h8

section Sec_t158Inn_hasLabel_u38


theorem t158Inn_hasLabel_u38 {G : Type} [Group G] [Finite G] {X J : Subgroup G} (hJ : GLAPComponent 3 X J)
    (hq : CFSG.Open.IsQuasisimple ↥J) (hU : catalogIs (PSimple 3 J) S9.isU3eight) :
    Y10F.HasLabel ↥J (fun l => l = ⟨.twA, 2, 3⟩) := by
  obtain ⟨eJ⟩ := I141F.centerQuot_equiv_pSimple Nat.prime_three hJ hq
  obtain ⟨q, hv, hq8, ⟨e8⟩⟩ := CatB.lieIndex_isU3eight hU
  obtain ⟨hp2, he3⟩ := t158Inn_eight_eq q hq8
  have hm := CFSG.Models.lieModel_twistedA 2 q hv (eJ.trans e8)
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  rw [hc, hf, hp2, he3] at hm
  have hb : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSU (2 + 1) 2 3 :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [CFSG.Blueprint.classicalTags]) hm
  obtain ⟨hperf, lab, hlab, hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hb
  obtain ⟨R, _, I, F, -, -, -, ht, hr, hc', hf'⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hlab' : lab = ⟨.twA, 2, 3⟩ := t158Inn_eq_twA_two_three ht hr hc' hf'
  exact ⟨hperf, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hlab'⟩) hraw⟩

end Sec_t158Inn_hasLabel_u38

section Sec_t158Inn_fldPiece


theorem t158Inn_fldPiece : Y10GField.FldPiece :=
  fun S _ _ p α J labK labJ hp hp2 hcen hfld hnot hα hlabJ hJ =>
    Y10GField.fld_of_families (Y10GField.fldLin_of_labelDict Y10GInnLin.linLabelDict_holds)
      (Y10GFldUni.fldUni_of_sigmaPow Y10GFldUniSig.uniSigmaPowOne_holds) Y10GField.fldSymp_holds
      Y10GFldOrth.fldOrth_holds
      (Y10GField.fldExc_of_gaps Y10GField.fixGapG2_holds Y10GField.fixGapE6_holds
        Y10GField.fixGapTwE6_holds Y10GField.fixGapTriD4_holds Y10GField.fixGapTwB2_holds
        Y10GField.fixGapTwF4_holds)
      S p α J labK labJ hp hp2 hcen hfld hnot hα hlabJ hJ

end Sec_t158Inn_fldPiece

section Sec_t158Inn_field_label


theorem t158Inn_field_label {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω} {x : Ω}
    (hSc : GLAPComponent 3 S S) (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group) (hx3 : x ^ 3 = 1)
    (hF : FieldOn 3 x S) (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) L)
    (hU : catalogIs (PSimple 3 L) S9.isU3eight) :
    GLAMarking (PQuot 3 S) (fun lab _ _ I F θ => lab = ⟨.twA, 2, 9⟩ ∧
      GLAPrimeField 3 lab I F (GLAInduces θ (indRel 3 S x))) := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hSc
  haveI := hsimple
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hSc
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  haveI : Group.IsPerfect (PQuot 3 S) := ⟨hq.1⟩
  have hTperf : commutator (PSimple 3 S) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot 3 S)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨hN, hmk⟩ := hF
  have hmk' := FP.canon_marking_and_labelAll_simple'
    (P' := fun _ R _ I F => CFSG.StandardType.GGRawInnField 3 R I F ∧ CFSG.StandardType.GGRawFieldCentral R I F)
    (fun lab hlab => ((MI.canonRawInnAny (by norm_num) hlab).and (FP.canonRawFieldCentral hlab)).mono
      fun R _ I F h _ _ => h) hmk
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmk'
  set β : MulAut (PSimple 3 S) := (chevAut 3 S ⟨x, hN⟩)⁻¹ with hβdef
  have hck : ∀ k : ↥S, chevQuotHom 3 S k = QuotientGroup.mk (QuotientGroup.mk k : PQuot 3 S) := fun _ => rfl
  have hβk : ∀ k : ↥S, β (chevQuotHom 3 S k) =
      chevQuotHom 3 S (S.normalizerMonoidHom (⟨x, hN⟩ : ↥(Subgroup.normalizer (S : Set Ω)))⁻¹ k) := by
    intro k
    rw [hβdef, ← map_inv, chevAut_chevQuotHom]
  have hxk : ∀ k : ↥S,
      ((S.normalizerMonoidHom (⟨x, hN⟩ : ↥(Subgroup.normalizer (S : Set Ω)))⁻¹ k : ↥S) : Ω) = x⁻¹ * k * x := by
    intro k
    rw [chev_coe_normalizerMonoidHom]
    simp
  have hT : ∀ (R : Type) [Group R] (θ : PQuot 3 S ⧸ Subgroup.center (PQuot 3 S) ≃* R) (ψ : MulAut R),
      CFSG.Assembly.LargeEvenInduces θ (indRel 3 S x) ψ →
      CFSG.Assembly.LargeEvenInduces ((CanonInn.quotCenterEquivOfBot hcen).trans θ)
        (fun s s' => s' = β s) ψ := by
    intro R _ θ ψ hψ s s' hss'
    subst hss'
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk,
      CanonInn.quotCenterEquivOfBot_mk]
    have h1 := hβk k
    rw [hck, hck] at h1
    rw [h1]
    exact hψ (QuotientGroup.mk k)
      (QuotientGroup.mk (S.normalizerMonoidHom (⟨x, hN⟩ : ↥(Subgroup.normalizer (S : Set Ω)))⁻¹ k))
      ⟨k, _, rfl, rfl, hxk k⟩
  have hFK : Y10GField.FieldKind (PSimple 3 S) lab β := by
    refine ⟨hTperf, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna', θ, ⟨-, f, hf, u, hu, hord, hind⟩, hIF, hC⟩
    obtain ⟨hmul, hinv, -, hFnot⟩ := hIF hs hna'
    have hnorm := CFSG.StandardType.ggRawFieldNorm_of_central hC hIF hs hna'
    have hψ := hT R θ _ hind
    refine ⟨hs, hna', (CanonInn.quotCenterEquivOfBot hcen).trans θ, rfl, ?_, ?_⟩
    · refine ⟨u * (f * u⁻¹ * f⁻¹), hmul _ hu _ (hnorm f (Subgroup.subset_closure hf) _ (hinv u hu)),
        f, hf, ?_⟩
      have h1 : u * (f * u⁻¹ * f⁻¹) * f = u * f * u⁻¹ := by group
      rw [h1]
      exact hψ
    · rintro ⟨i, hi, hind'⟩
      have hieq : i = u * f * u⁻¹ := by
        ext r
        obtain ⟨t, rfl⟩ := ((CanonInn.quotCenterEquivOfBot hcen).trans θ).surjective r
        obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective t
        rw [hind' s (β s) rfl, hψ s (β s) rfl]
      have hfI : f ∈ I := by
        have h1 : f = u⁻¹ * i * u := by rw [hieq]; group
        rw [h1]
        exact hmul _ (hmul _ (hinv u hu) _ hi) _ hu
      exact hFnot f hf hord hfI
  have hα3 : (chevAut 3 S ⟨x, hN⟩) ^ 3 = 1 := chevAut_pow_eq_one 3 S hN hx3
  have hβ3 : β ^ 3 = 1 := by rw [hβdef, inv_pow, hα3, inv_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    obtain ⟨R, _, I, F, hs, hna', θ, ⟨-, f, hf, u, hu, hord, hind⟩, hIF, -⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    obtain ⟨hmul, hinv, -, hFnot⟩ := hIF hs hna'
    have hψ := hT R θ _ hind
    have hid : u * f * u⁻¹ = 1 := by
      ext r
      obtain ⟨t, rfl⟩ := ((CanonInn.quotCenterEquivOfBot hcen).trans θ).surjective r
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective t
      rw [hψ s (β s) rfl, h1]
      rfl
    have hf1 : f = 1 := by
      have h2 : f = u⁻¹ * (u * f * u⁻¹) * u := by group
      rw [h2, hid]
      group
    rw [hf1, orderOf_one] at hord
    norm_num at hord
  have hnot : ¬ (lab.tag = .triD4 ∧ (3 : ℕ) = 3) := by
    obtain ⟨R, _, I, F, -, -, θ, ⟨hne, -⟩, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    rintro ⟨h1, -⟩
    rcases hne with h | h
    · exact h h1
    · exact h rfl
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hN hxp hL
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hN hxp hL
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 S L)) S9.isU3eight := I2018.catalogIs_congr' eJ hU
  have hfixβ : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (chevAut 3 S ⟨x, hN⟩) := by
    ext y
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
      CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, hβdef, MulAut.inv_apply,
      MulEquiv.symm_apply_eq, eq_comm]
  have hJβ : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β)
      (chevTransfer 3 S L) := by
    rw [hfixβ]
    exact hJ'
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent (PSimple 3 S)
    hsimple hna d ⟨e⟩ 3 Nat.prime_three (by decide) (by rw [hd]; decide) β hβ3 hβ1
  have hJle := hpil (chevTransfer 3 S L) hJβ.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJβ)
  have hJc := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJβ hJle).1
  have hlabJ := t158Inn_hasLabel_u38 hJβ hJc.2.2 hU'
  obtain ⟨hn, htag, hrank⟩ := t158Inn_fldPiece (PSimple 3 S) 3 β (chevTransfer 3 S L) lab ⟨.twA, 2, 3⟩
    Nat.prime_three (by norm_num) hcen hFK hnot hβ3 hlabJ hJβ
  have hc3 : canonLabel (⟨.twA, 2, 3⟩ : LargeEvenLabel) = ⟨.twA, 2, 3⟩ := rfl
  rw [hc3] at hn htag hrank
  obtain ⟨ht, hr⟩ := t158Inn_twA_two_of_canonLabel ⟨htag, hrank⟩
  have hlab9 : lab = ⟨.twA, 2, 9⟩ := by
    obtain ⟨t, r, n⟩ := lab
    simp only at ht hr
    subst ht hr
    have hcl : canonLabel (⟨.twA, 2, n⟩ : LargeEvenLabel) = ⟨.twA, 2, n⟩ := rfl
    rw [hcl] at hn
    simp only at hn
    rw [hn]
  exact ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F ⟨hs, hna', θ, hPF, _⟩ => ⟨hs, hna', θ, hlab9, hPF⟩) hraw⟩

end Sec_t158Inn_field_label

section Sec_t158Inn_one


theorem t158Inn_one
    (hFc : T158FieldCoreU) (hTc : T158TriCore) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x₁ x₂ : Ω} {L₁ L₂ : Subgroup Ω}
    (hSn : S.Normal) (hq : CFSG.Open.IsQuasisimple ↥S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hcat : CFSG.Open.IsCatalogGroup (PSimple p S)) (hx1 : x₁ ^ p = 1) (hx2 : x₂ ^ p = 1)
    (hc : x₁ * x₂ = x₂ * x₁)
    (hL1 : GLAPComponent p (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁)
    (hU1 : catalogIs (PSimple p L₁) S9.isU3eight)
    (hL2 : GLAPComponent p (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂)
    (hU2 : catalogIs (PSimple p L₂) S9.isU3eight)
    (hF12 : FieldOn p x₁ L₂) (hF21 : FieldOn p x₂ L₁) :
    InnDiagOn p (Subgroup.zpowers x₁) S := by
  obtain rfl : p = 3 := t158Inn_prime_eq_three hp hp2 hL1 hU1 hx2 hF21
  have hSc : GLAPComponent 3 S S :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_self_of_quasisimple hq hcore
  have hx1N : x₁ ∈ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top x₁
  obtain ⟨d, hd, ⟨e⟩⟩ := t158Inn_char2_index hSc hcat hx1N hx1 hL1 hU1
  have hchev : IsChevSimple 2 (PSimple 3 S) := Or.inl ⟨TauCeti.CFSGIndex.lie d, hd, ⟨e⟩⟩
  by_contra hnot
  have hnon : NonInnDiag 3 x₁ S := ⟨hx1N, hnot⟩
  have hfield : FieldOn 3 x₁ S → False := fun hF =>
    hFc Ω S x₁ x₂ L₁ L₂ hSn hq hcore hx1 hx2 hc hx1N (t158Inn_field_label hSc d hd e hx1 hF hL1 hU1)
      hL1 hU1 hL2 hU2 hF12 hF21
  rcases i91_holds Ω 3 Nat.prime_three (by norm_num) S S x₁ hSc hchev hx1N hx1 hnon with hF | ⟨-, hD⟩
  · exact hfield hF
  · by_cases hF : FieldOn 3 x₁ S
    · exact hfield hF
    · exact hTc Ω S x₁ x₂ L₁ L₂ hSn hq hcore (t158Inn_tri_eight hSc hD hx1N hx1 hL1 hU1) hx1 hx2 hc hnon hF
        hL1 hU1 hL2 hU2 hF12 hF21

end Sec_t158Inn_one

section Sec_t158Inn_inn_of_cores


theorem t158Inn_inn_of_cores
    (hFc : T158FieldCoreU) (hTc : T158TriCore) (p : ℕ) :
    p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x₁ x₂ : Ω) (L₁ L₂ : Subgroup Ω),
      S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      CFSG.Open.IsCatalogGroup (PSimple p S) →
      x₁ ^ p = 1 → x₂ ^ p = 1 → x₁ * x₂ = x₂ * x₁ →
      GLAPComponent p (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁ → catalogIs (PSimple p L₁) S9.isU3eight →
      GLAPComponent p (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂ → catalogIs (PSimple p L₂) S9.isU3eight →
      FieldOn p x₁ L₂ → FieldOn p x₂ L₁ →
      InnDiagOn p (Subgroup.zpowers x₁) S ∧ InnDiagOn p (Subgroup.zpowers x₂) S := by
  intro hp hp2 Ω _ _ S x₁ x₂ L₁ L₂ hSn hq hcore hcat hx1 hx2 hc hL1 hU1 hL2 hU2 hF12 hF21
  exact ⟨t158Inn_one hFc hTc hp hp2 hSn hq hcore hcat hx1 hx2 hc hL1 hU1 hL2 hU2 hF12 hF21,
    t158Inn_one hFc hTc hp hp2 hSn hq hcore hcat hx2 hx1 hc.symm hL2 hU2 hL1 hU1 hF21 hF12⟩

end Sec_t158Inn_inn_of_cores

section Sec_t158InnFactOmega_of_fg


theorem t158InnFactOmega_of_fg
    (hFc : T158FieldCoreU) (hTc : T158TriCore)
    (hfg : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω) (J : Subgroup Ω),
      S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple 2 (PSimple p S) →
      x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ∉ Subgroup.zpowers y → y ∉ Subgroup.zpowers x →
      InnDiagOn p (Subgroup.zpowers x) S → FieldOn p y S →
      GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J → y ∈ Subgroup.normalizer (J : Set Ω) →
      FGOn p y J) :
    ∀ p, T158.T158InnFactOmega p :=
  fun p => ⟨t158Inn_inn_of_cores hFc hTc p, hfg p⟩

end Sec_t158InnFactOmega_of_fg

end CFSG.LocalAnalysis.GLTheoremA.T158Inn

end
