module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144ILabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows1
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144I

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel centerQuotAut centerQuotAut_mk
  center_centerQuot_eq_bot)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind)
open CFSG.LocalAnalysis.GLTheoremA.K144 (I144Cat I144Inner)

theorem exists_label_of_hasLabel {X : Type} [Group X] {T : GLALabel → Prop} (h : HasLabel X T) :
    ∃ lab : GLALabel, T lab ∧ HasLabel X (· = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hT⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hT, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

theorem i144Cat_label_cases {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    (h : catalogIs (X ⧸ Subgroup.center X) I144Cat) :
    ∃ labJ : GLALabel, (labJ = ⟨.twA, 3, 1⟩ ∨ labJ = ⟨.twA, 4, 1⟩ ∨ labJ = ⟨.B, 3, 1⟩) ∧
      HasLabel X (· = labJ) := by
  have hq := isQuasisimple_of_openQuasisimple hX
  obtain ⟨i, hi, he⟩ := h
  rcases hi with hU4 | hU5 | hSp
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex_of_catalogIs_onLie ⟨i, hU4, he⟩
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact ⟨⟨.twA, 3, 1⟩, Or.inl rfl,
          Y10F.hasLabel_of_statedClassicalModel_PSU hq (statedClassicalModel_psu_two hP e)⟩
      · exact hP.elim
    | _ => exact hP.elim
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex_of_catalogIs_onLie ⟨i, hU5, he⟩
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact ⟨⟨.twA, 4, 1⟩, Or.inr (Or.inl rfl),
          Y10F.hasLabel_of_statedClassicalModel_PSU hq (statedClassicalModel_psu_two hP e)⟩
      · exact hP.elim
    | _ => exact hP.elim
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex_of_catalogIs_onLie ⟨i, hSp, he⟩
    cases d with
    | B r q =>
      rcases r with _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact ⟨⟨.B, 3, 1⟩, Or.inr (Or.inr rfl),
          Y10F.hasLabel_of_statedClassicalModel_PSp hq (statedClassicalModel_psp_two hP e)⟩
      · exact hP.elim
    | _ => exact hP.elim

theorem quotCenterEquivOfBot_symm_apply {S : Type} [Group S] (h : Subgroup.center S = ⊥) (s : S) :
    (CanonInn.quotCenterEquivOfBot h).symm s = QuotientGroup.mk s := by
  rw [MulEquiv.symm_apply_eq, CanonInn.quotCenterEquivOfBot_mk]

theorem i144Inner_of_innDiagKind {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    {α : MulAut K} {labK : GLALabel}
    (h : InnDiagKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α)) : I144Inner K α := by
  have hcen := center_centerQuot_eq_bot hK
  obtain ⟨-, lab, hlam, hraw⟩ := h
  refine ⟨hK.1, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, -, u, hu, hind⟩
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).symm.trans θ, u, hu, ?_⟩
  intro l l' hll'
  subst hll'
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, quotCenterEquivOfBot_symm_apply,
    quotCenterEquivOfBot_symm_apply]
  exact hind (QuotientGroup.mk l) (QuotientGroup.mk (α l)) (centerQuotAut_mk K α l).symm

section Lang


theorem primeField_of_fieldKind {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    {α : MulAut K} (hα3 : α ^ 3 = 1) {labK : GLALabel} (htri : labK.tag ≠ .triD4)
    (h : FieldKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α)) :
    GLAMarking K fun lab _ _ I F θ =>
      GLAPrimeField 3 lab I F (GLAInduces θ fun x y => α x = y) := by
  have hcen := center_centerQuot_eq_bot hK
  have h' := FP.canon_marking_and_labelAll_simple' (P' := FP.TransportFacts 3)
    (fun lab hlab => FP.canonTransportFacts Nat.prime_three (by norm_num) hlab) h
  obtain ⟨-, lab, hlam, hraw⟩ := h'
  refine ⟨hK.1, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨hlab, ⟨i, hi, f, hf, hind⟩, hnot⟩, ⟨-, -, hlift⟩⟩
  subst hlab
  obtain ⟨-, hC⟩ := hlift fun h3 => htri h3.1
  obtain ⟨e, he_apply⟩ : ∃ e : K ⧸ Subgroup.center K ≃* R, ∀ s, e s = θ (QuotientGroup.mk s) :=
    ⟨(CanonInn.quotCenterEquivOfBot hcen).symm.trans θ, fun s => by
      rw [MulEquiv.trans_apply, quotCenterEquivOfBot_symm_apply]⟩
  have huniq : ∀ u : MulAut R,
      CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = centerQuotAut K α s) u →
        u = MulAut.congr e (centerQuotAut K α) := by
    intro u hu
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      he_apply, he_apply]
    exact hu s _ rfl
  have hif := huniq _ hind
  have hpow : (i * f) ^ 3 = 1 := by
    rw [hif, ← map_pow]
    have : centerQuotAut K α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    rw [this, map_one]
  have hnotI : i * f ∉ I := fun hmem => hnot ⟨i * f, hmem, hind⟩
  obtain ⟨f', hf', u', hu', hord, hconj⟩ := hC i hi f (Subgroup.subset_closure hf) hnotI hpow
  refine ⟨hs, hna, e, Or.inl htri, f', hf', u', hu', hord, ?_⟩
  intro l l' hll'
  subst hll'
  rw [← hconj, hif, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, centerQuotAut_mk]

end Lang

section Orders


theorem card_of_i144Cat {X : Type} [Group X] [Finite X] (h : catalogIs X I144Cat) :
    Nat.card X = 25920 ∨ Nat.card X = 13685760 ∨ Nat.card X = 1451520 := by
  obtain ⟨i, hi, he⟩ := h
  rcases hi with h1 | h2 | h3
  · exact Or.inl (I1431Z.card_eq_of_u4two ⟨i, h1, he⟩)
  · exact Or.inr (Or.inl (K14Spor.card_u5two ⟨i, h2, he⟩))
  · exact Or.inr (Or.inr (K14Spor.card_sp6two ⟨i, h3, he⟩))

theorem five_dvd_card_of_i144Cat {X : Type} [Group X] [Finite X] (h : catalogIs X I144Cat) :
    5 ∣ Nat.card X := by
  rcases card_of_i144Cat h with h1 | h1 | h1 <;> rw [h1] <;> norm_num

end Orders

section Triality


theorem card_graphFixedRootGroup_D4_two {K₃ : Type} [Field K₃] [Finite K₃] {Fr : K₃ ≃+* K₃}
    (hK : Nat.card K₃ = (2 ^ 1) ^ 3) (hFr : ∀ c, Fr c = c ^ (2 ^ 1)) :
    Nat.card ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K₃
      Fr.toRingHom) = 211341312 := by
  obtain ⟨e⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv
    CFSG.Blueprint.Chevalley.TwistTag.D4 Nat.prime_two (le_refl 1) K₃ hK Fr.toRingHom hFr
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel
      ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K₃
        Fr.toRingHom) .trialityD4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl⟩, K₃, inferInstance, inferInstance, hK, Fr.toRingHom, hFr,
      ⟨e.symm⟩⟩
  rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc]
  rfl

end Triality

section TrialityLabel


theorem card_of_hasLabel_triD4_one {X : Type} [Group X] {r : ℕ}
    (h : HasLabel X (· = ⟨.triD4, r, 1⟩)) : Nat.card (X ⧸ Subgroup.center X) = 211341312 := by
  have hm := CanonSubcomp.markedModel_of_hasLabel h
  change CFSG.Blueprint.LieModel _ .trialityD4 0 2 1 at hm
  rcases hm with ⟨ht, -⟩ | ⟨-, -, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc]
    rfl
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end TrialityLabel

end CFSG.LocalAnalysis.GLTheoremA.K144I

end
