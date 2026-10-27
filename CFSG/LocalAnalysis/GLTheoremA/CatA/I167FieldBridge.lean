module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167FieldDict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenLabel)
open CFSG.StandardType (markTag markRank markChar markDeg)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}

private theorem fld_fixSubgroup_inv {K : Type} [Group K] (α : MulAut K) :
    fixSubgroup α⁻¹ = fixSubgroup α := by
  ext y
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.inv_apply,
    MulEquiv.symm_apply_eq, eq_comm]

theorem fld_card_pSimple_le (hp : p.Prime) {X J : Subgroup Ω} {x : Ω}
    (hN : x ∈ Subgroup.normalizer (X : Set Ω)) (hxp : IsPGroup p (Subgroup.zpowers x))
    (hJ : GLAPComponent p (X ⊓ cx x) J) :
    Nat.card (PSimple p J) ≤ Nat.card (PSimple p X) := by
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer hp hN hxp hJ
  rw [Nat.card_congr eJ.toEquiv]
  exact (Nat.card_le_card_of_surjective _ (chevQuotHom_surjective p (chevTransfer p X J))).trans
    (Subgroup.card_le_card_group _)

theorem fld_range_mul {t : StatedLieTag} {n f q : ℕ} (hq : 2 ≤ q) (hr : FldRange t n f) :
    FldRange t n (q * f) := by
  obtain ⟨hf, h⟩ := hr
  refine ⟨by nlinarith, ?_⟩
  rcases h with ⟨ht, h5 | ⟨h4, h2⟩⟩ | h
  · exact Or.inl ⟨ht, Or.inl h5⟩
  · exact Or.inl ⟨ht, Or.inr ⟨h4, by nlinarith⟩⟩
  · exact Or.inr h

section Bridge


theorem fld_induces_inv {S : Subgroup Ω} {x : Ω} (hN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hcen : Subgroup.center (PSimple p S) = ⊥) {R : Type} [Group R]
    (θ : PQuot p S ⧸ Subgroup.center (PQuot p S) ≃* R) (ψ : MulAut R)
    (h : CFSG.Assembly.LargeEvenInduces θ (indRel p S x) ψ) :
    CFSG.Assembly.LargeEvenInduces ((CanonInn.quotCenterEquivOfBot hcen).trans θ)
      (fun s s' => s' = (chevAut p S ⟨x, hN⟩)⁻¹ s) ψ := by
  set β : MulAut (PSimple p S) := (chevAut p S ⟨x, hN⟩)⁻¹ with hβdef
  have hck : ∀ k : ↥S, chevQuotHom p S k = QuotientGroup.mk (QuotientGroup.mk k : PQuot p S) :=
    fun _ => rfl
  have hβk : ∀ k : ↥S, β (chevQuotHom p S k) =
      chevQuotHom p S (S.normalizerMonoidHom (⟨x, hN⟩ : ↥(Subgroup.normalizer (S : Set Ω)))⁻¹ k) := by
    intro k
    rw [hβdef, ← map_inv, chevAut_chevQuotHom]
  have hxk : ∀ k : ↥S,
      ((S.normalizerMonoidHom (⟨x, hN⟩ : ↥(Subgroup.normalizer (S : Set Ω)))⁻¹ k : ↥S) : Ω) =
        x⁻¹ * k * x := by
    intro k
    rw [chev_coe_normalizerMonoidHom]
    simp
  intro s s' hss'
  subst hss'
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk,
    CanonInn.quotCenterEquivOfBot_mk]
  have h1 := hβk k
  rw [hck, hck] at h1
  rw [h1]
  exact h (QuotientGroup.mk k)
    (QuotientGroup.mk (S.normalizerMonoidHom (⟨x, hN⟩ : ↥(Subgroup.normalizer (S : Set Ω)))⁻¹ k))
    ⟨k, _, rfl, rfl, hxk k⟩

theorem fld_fieldKind_of_fieldOn (hp : p.Prime) {X : Subgroup Ω} {x : Ω} (hSc : GLAPComponent p X X)
    (hF : FieldOn p x X) :
    ∃ lab : LargeEvenLabel, Y10GField.FieldKind (PSimple p X) lab (chevAut p X ⟨x, hF.1⟩)⁻¹ ∧
      ¬ (lab.tag = .triD4 ∧ p = 3) := by
  have hq : CFSG.Open.IsQuasisimple (PQuot p X) := isQuasisimple_pQuot_of_glaPComponent hp hSc
  have hcen : Subgroup.center (PSimple p X) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  haveI : Group.IsPerfect (PQuot p X) := ⟨hq.1⟩
  have hTperf : commutator (PSimple p X) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p X)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨hN, hmk⟩ := hF
  have hmk' := FP.canon_marking_and_labelAll_simple'
    (P' := fun _ R _ I F =>
      CFSG.StandardType.GGRawInnField p R I F ∧ CFSG.StandardType.GGRawFieldCentral R I F)
    (fun lab hlab => ((MI.canonRawInnAny hp.one_lt.ne' hlab).and (FP.canonRawFieldCentral hlab)).mono
      fun R _ I F h _ _ => h) hmk
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmk'
  have hnot : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    obtain ⟨R, _, I, F, -, -, θ, ⟨hne, -⟩, -⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    exact fun ⟨h1, h2⟩ => hne.elim (fun h => h h1) (fun h => h h2)
  refine ⟨lab, ?_, hnot⟩
  refine ⟨hTperf, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna', θ, ⟨-, f, hf, u, hu, hord, hind⟩, hIF, hC⟩
  obtain ⟨hmul, hinv, -, hFnot⟩ := hIF hs hna'
  have hnorm := CFSG.StandardType.ggRawFieldNorm_of_central hC hIF hs hna'
  have hψ := fld_induces_inv hN hcen θ _ hind
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
      rw [hind' s ((chevAut p X ⟨x, hN⟩)⁻¹ s) rfl, hψ s ((chevAut p X ⟨x, hN⟩)⁻¹ s) rfl]
    have hfI : f ∈ I := by
      have h1 : f = u⁻¹ * i * u := by rw [hieq]; group
      rw [h1]
      exact hmul _ (hmul _ (hinv u hu) _ hi) _ hu
    exact hFnot f hf hord hfI

theorem fld_chevAut_ne_one (hp : p.Prime) {X : Subgroup Ω} {x : Ω} (hSc : GLAPComponent p X X)
    (hF : FieldOn p x X) : chevAut p X ⟨x, hF.1⟩ ≠ 1 := by
  have hq : CFSG.Open.IsQuasisimple (PQuot p X) := isQuasisimple_pQuot_of_glaPComponent hp hSc
  have hcen : Subgroup.center (PSimple p X) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨hN, hmk⟩ := hF
  have hmk' := FP.canon_marking_and_labelAll_simple'
    (P' := fun _ R _ I F =>
      CFSG.StandardType.GGRawInnField p R I F ∧ CFSG.StandardType.GGRawFieldCentral R I F)
    (fun lab hlab => ((MI.canonRawInnAny hp.one_lt.ne' hlab).and (FP.canonRawFieldCentral hlab)).mono
      fun R _ I F h _ _ => h) hmk
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmk'
  intro hα1
  have hβ1 : (chevAut p X ⟨x, hN⟩)⁻¹ = 1 := by rw [hα1, inv_one]
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, f, hf, u, hu, hord, hind⟩, -, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hψ := fld_induces_inv hN hcen θ _ hind
  have hid : u * f * u⁻¹ = 1 := by
    ext r
    obtain ⟨t, rfl⟩ := ((CanonInn.quotCenterEquivOfBot hcen).trans θ).surjective r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective t
    rw [hψ s ((chevAut p X ⟨x, hN⟩)⁻¹ s) rfl, hβ1]
    rfl
  have hf1 : f = 1 := by
    have h2 : f = u⁻¹ * (u * f * u⁻¹) * u := by group
    rw [h2, hid]
    group
  rw [hf1, orderOf_one] at hord
  exact hp.one_lt.ne' hord.symm

theorem fld_transfer_isQuasisimple (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup Ω} {x : Ω}
    (hSc : GLAPComponent p X X) {d : TauCeti.ValidLieTypeIndex} (hd : d.1.characteristic = 2)
    (e : PSimple p X ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hN : x ∈ Subgroup.normalizer (X : Set Ω)) (hxp : x ^ p = 1) (hne : chevAut p X ⟨x, hN⟩ ≠ 1)
    (hJ : GLAPComponent p (X ⊓ cx x) J) : CFSG.Open.IsQuasisimple ↥(chevTransfer p X J) := by
  have hxp' : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hxp
  have hJ' := glaPComponent_chevTransfer hp hN hxp' hJ
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian hp hSc
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
    (PSimple p X) hsimple hna d ⟨e⟩ p hp hp2
    (fun h : p = d.1.characteristic => hp2 (h.trans hd))
    (chevAut p X ⟨x, hN⟩) (chevAut_pow_eq_one p X hN hxp) hne
  have hJle := hpil (chevTransfer p X J) hJ'.1
    (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ')
  exact (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ' hJle).1.2.2

private theorem fld_hasLabel_of_lieModel_aux1 {t : StatedLieTag} {n f : ℕ} (hr : FldRange t n f) :
    canonLabel (fldClassicalLabel t n f) = fldClassicalLabel t n f := by
  rcases hr with ⟨-, ⟨rfl, hn⟩ | ⟨rfl | rfl, hn⟩⟩
  · rfl
  · dsimp only [fldClassicalLabel, canonLabel]
    rw [if_neg (show n ≠ 3 by omega)]
  · dsimp only [fldClassicalLabel, canonLabel]
    rw [if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 2 by omega)]

theorem fld_hasLabel_of_lieModel {G : Type} [Group G] [Finite G] (hp : p.Prime) {Y K : Subgroup G}
    (hK : GLAPComponent p Y K) (hq : CFSG.Open.IsQuasisimple ↥K) {t : StatedLieTag} {n f : ℕ}
    (hr : FldRange t n f) (hm : CFSG.Blueprint.LieModel (PSimple p K) t n 2 f) :
    ∃ labJ : LargeEvenLabel, Y10F.HasLabel ↥K (fun l => l = labJ) ∧
      canonLabel labJ = fldClassicalLabel t n f := by
  obtain ⟨eK⟩ := I141F.centerQuot_equiv_pSimple hp hK hq
  have hb : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) t n 2 f := hm.of_mulEquiv eK.symm
  obtain ⟨hperf, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hb
  obtain ⟨R, _, I, F, -, -, -, ht, hrk, hch, hdf⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hpar := fld_label_eq_of_markParams hr ⟨ht, hrk, hch, hdf⟩
  refine ⟨lab, ?_, ?_⟩
  · exact ⟨hperf, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  · rcases hpar with h | ⟨rfl, rfl, rfl⟩
    · rw [h]
      exact fld_hasLabel_of_lieModel_aux1 hr
    · simp [canonLabel, fldClassicalLabel]

private theorem fld_label_eq_of_components {L : LargeEvenLabel} {t : StatedLieTag} {n f : ℕ}
    (hn : L.n = p * (fldClassicalLabel t n f).n) (htag : L.tag = (fldClassicalLabel t n f).tag)
    (hrank : L.rank = (fldClassicalLabel t n f).rank) : L = fldClassicalLabel t n (p * f) := by
  rcases L with ⟨tg, rk, m⟩
  cases t <;> simp only [fldClassicalLabel] at hn htag hrank ⊢ <;> subst htag hrank hn <;> rfl

theorem fld_canon_of_lieModel (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup Ω} {x : Ω}
    (hSc : GLAPComponent p X X) (hxp : x ^ p = 1) (hF : FieldOn p x X)
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1.characteristic = 2)
    (e : PSimple p X ≃* (TauCeti.CFSGIndex.lie d).Group) (hJ : GLAPComponent p (X ⊓ cx x) J)
    {t : StatedLieTag} {n f : ℕ} (hr : FldRange t n f)
    (hm : CFSG.Blueprint.LieModel (PSimple p J) t n 2 f) :
    ∃ labX : LargeEvenLabel, Y10GField.FieldKind (PSimple p X) labX (chevAut p X ⟨x, hF.1⟩)⁻¹ ∧
      canonLabel labX = fldClassicalLabel t n (p * f) := by
  have hN := hF.1
  obtain ⟨labX, hFK, hnot⟩ := fld_fieldKind_of_fieldOn hp hSc hF
  have hxp' : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hxp
  have hq := fld_transfer_isQuasisimple hp hp2 hSc hd e hN hxp (fld_chevAut_ne_one hp hSc hF) hJ
  have hJ' := glaPComponent_chevTransfer hp hN hxp' hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer hp hN hxp' hJ
  obtain ⟨labJ, hlabJ, hcanJ⟩ := fld_hasLabel_of_lieModel hp hJ' hq hr (hm.of_mulEquiv eJ)
  have hcen : Subgroup.center (PSimple p X) = ⊥ :=
    Y10F.center_centerQuot_eq_bot (isQuasisimple_pQuot_of_glaPComponent hp hSc)
  have hα : ((chevAut p X ⟨x, hN⟩)⁻¹) ^ p = 1 := by
    rw [inv_pow, chevAut_pow_eq_one p X hN hxp, inv_one]
  have hJα : GLAPComponent p (fixSubgroup (chevAut p X ⟨x, hN⟩)⁻¹) (chevTransfer p X J) := by
    rw [fld_fixSubgroup_inv]
    exact hJ'
  obtain ⟨h1, h2, h3⟩ := T158Inn.t158Inn_fldPiece (PSimple p X) p (chevAut p X ⟨x, hN⟩)⁻¹
    (chevTransfer p X J) labX labJ hp hp2 hcen hFK hnot hα hlabJ hJα
  rw [hcanJ] at h1 h2 h3
  exact ⟨labX, hFK, fld_label_eq_of_components h1 h2 h3⟩

private theorem fld_markedModel_of_fieldKind {S : Type} [Group S] {lab : LargeEvenLabel} {α : MulAut S}
    (h : Y10GField.FieldKind S lab α) :
    CFSG.StandardType.MarkedModel lab (S ⧸ Subgroup.center S) := by
  obtain ⟨lab', -, R, _, I, F, θ, -, -, hP, hM⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel h
  obtain ⟨rfl, -⟩ := hP
  exact CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hM

theorem fld_lieModel_of_fieldOn (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup Ω} {x : Ω}
    (hchev : IsChevSimple 2 (PSimple p X)) (hSc : GLAPComponent p X X) (hxp : x ^ p = 1)
    (hF : FieldOn p x X) (hJ : GLAPComponent p (X ⊓ cx x) J) {t : StatedLieTag} {n f : ℕ}
    (hr : FldRange t n f) (hm : CFSG.Blueprint.LieModel (PSimple p J) t n 2 f) :
    CFSG.Blueprint.LieModel (PSimple p X) t n 2 (p * f) := by
  have hbig : 20160 < Nat.card (PSimple p X) :=
    lt_of_lt_of_le (fld_card_gt_of_lieModel hr hm)
      (fld_card_pSimple_le hp hF.1 (isPGroup_zpowers_of_pow_eq_one hxp) hJ)
  obtain ⟨d, hd, ⟨e⟩⟩ := fld_exists_char2_index hchev hbig
  obtain ⟨labX, hFK, hcan⟩ := fld_canon_of_lieModel hp hp2 hSc hxp hF hd e hJ hr hm
  have hcen : Subgroup.center (PSimple p X) = ⊥ :=
    Y10F.center_centerQuot_eq_bot (isQuasisimple_pQuot_of_glaPComponent hp hSc)
  have hM := fld_markedModel_of_fieldKind hFK
  have hpar : markTag labX = t ∧ markRank labX = n ∧ markChar labX = 2 ∧ markDeg labX = p * f :=
    fld_markParams_of_canonLabel (fld_range_mul hp.two_le hr) hcan
  unfold CFSG.StandardType.MarkedModel at hM
  rw [hpar.1, hpar.2.1, hpar.2.2.1, hpar.2.2.2] at hM
  exact CFSG.Blueprint.LieModel.of_quotient_center hcen hM

end Bridge

end CFSG.LocalAnalysis.GLTheoremA.I167

end



