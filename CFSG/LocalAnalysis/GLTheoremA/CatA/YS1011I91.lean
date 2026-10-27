module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.GH74.KGroups.Cover
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Assembly

section I91

variable {G : Type} [Group G]


theorem i91_rawIff {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hG : lab.tag ≠ .G2der) (hF : lab.tag ≠ .twF4der) (Q : LargeEvenRawCont) :
    LargeEvenRawDatum lab Q ↔ CFSG.StandardType.LargeEvenRawDatum lab Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case G2der => exact (hG rfl).elim
  case twF4der => exact (hF rfl).elim
  case twF4 =>
    obtain ⟨-, -, h3⟩ := hlab.2
    have h3' : 3 ≤ n := h3
    have h0 : (n - 1) / 2 ≠ 0 := by omega
    simp only [LargeEvenRawDatum, CFSG.StandardType.LargeEvenRawDatum,
      LargeEvenRecipeTwF4Inherited, LargeEvenRecipeTwF4, if_neg h0]
  all_goals exact Iff.rfl

theorem i91_or_split {lab : LargeEvenLabel} {A B : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab fun R _ I F => A R I F ∨ B R I F) :
    LargeEvenRawDatum lab A ∨ LargeEvenRawDatum lab B := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact hq.elim (fun hq => Or.inl ⟨K, i1, i2, hK, b, c, hbc, hq⟩)
         (fun hq => Or.inr ⟨K, i1, i2, hK, b, c, hbc, hq⟩))
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact hq.elim (fun hq => Or.inl ⟨K, i1, i2, hK, hq⟩)
         (fun hq => Or.inr ⟨K, i1, i2, hK, hq⟩))

section Induced

noncomputable def i91Phi (p : ℕ) (J : Subgroup G) {R : Type} [Group R] (θ : PSimple p J ≃* R) :
    ↥(Subgroup.normalizer (J : Set G)) →* MulAut R :=
  (MulAut.congr θ).toMonoidHom.comp
    ((CFSG.GH74.KGroups.inducedHom (K := PQuot p J)).comp
      (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p J))

theorem i91Phi_induces {p : ℕ} (J : Subgroup G) {R : Type} [Group R] (θ : PSimple p J ≃* R)
    (g : ↥(Subgroup.normalizer (J : Set G))) :
    LargeEvenInduces θ (indRel p J (g : G)) (i91Phi p J θ g⁻¹) := by
  rintro q q' ⟨l, l', rfl, rfl, hl⟩
  have hkey : J.normalizerMonoidHom g⁻¹ l = l' := by
    apply Subtype.ext
    show ((g⁻¹ : ↥(Subgroup.normalizer (J : Set G))) : G) * (l : G) *
      (((g⁻¹ : ↥(Subgroup.normalizer (J : Set G))) : G))⁻¹ = (l' : G)
    rw [hl]
    simp
  simp only [i91Phi, MonoidHom.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    CFSG.GH74.KGroups.inducedHom_mk, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, hkey]

theorem i91Phi_zpow {p : ℕ} (J : Subgroup G) {R : Type} [Group R] (θ : PSimple p J ≃* R)
    (g : ↥(Subgroup.normalizer (J : Set G))) (k : ℤ) :
    i91Phi p J θ (g ^ k)⁻¹ = (i91Phi p J θ g⁻¹) ^ k := by
  rw [← inv_zpow, map_zpow]

theorem i91_zpow_pow {b : G} {p : ℕ} (hbp : b ^ p = 1) (k : ℤ) : (b ^ k) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]

theorem i91_zpowers_mem {p : ℕ} (J : Subgroup G) {b : G}
    (hbN : b ∈ Subgroup.normalizer (J : Set G)) {R : Type} [Group R] (θ : PSimple p J ≃* R)
    {I : Set (MulAut R)} (hI : i91Phi p J θ ⟨b, hbN⟩⁻¹ ∈ I)
    (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I) (h1 : (1 : MulAut R) ∈ I) :
    ∀ a ∈ Subgroup.zpowers b, ∃ φ ∈ I, LargeEvenInduces θ (indRel p J a) φ := by
  intro a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hk : b ^ k ∈ Subgroup.normalizer (J : Set G) := Subgroup.zpow_mem _ hbN k
  refine ⟨i91Phi p J θ ⟨b ^ k, hk⟩⁻¹, ?_, i91Phi_induces J θ ⟨b ^ k, hk⟩⟩
  have hg : (⟨b ^ k, hk⟩ : ↥(Subgroup.normalizer (J : Set G))) = ⟨b, hbN⟩ ^ k :=
    Subtype.ext (by simp)
  rw [hg, i91Phi_zpow]
  let S : Subgroup (MulAut R) :=
    { carrier := I, mul_mem' := fun ha hb => hmul _ ha _ hb, one_mem' := h1,
      inv_mem' := fun ha => hinv _ ha }
  exact S.zpow_mem hI k

theorem i91_zpowers_odd {p : ℕ} (J : Subgroup G) {b : G}
    (hbN : b ∈ Subgroup.normalizer (J : Set G)) (hbp : b ^ p = 1) {R : Type} [Group R]
    (θ : PSimple p J ≃* R) {I : Set (MulAut R)} (hodd : ∀ α : MulAut R, α ^ p = 1 → α ∈ I) :
    ∀ a ∈ Subgroup.zpowers b, ∃ φ ∈ I, LargeEvenInduces θ (indRel p J a) φ := by
  intro a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hk : b ^ k ∈ Subgroup.normalizer (J : Set G) := Subgroup.zpow_mem _ hbN k
  refine ⟨i91Phi p J θ ⟨b ^ k, hk⟩⁻¹, hodd _ ?_, i91Phi_induces J θ ⟨b ^ k, hk⟩⟩
  have hpN : (⟨b ^ k, hk⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ p = 1 :=
    Subtype.ext (by simpa using i91_zpow_pow hbp k)
  rw [← map_pow, inv_pow, hpN, inv_one, map_one]

end Induced

def i91OddInner (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  IsSimpleGroup R → (∃ x y : R, x * y ≠ y * x) → ∀ m : ℕ, Odd m → ∀ α : MulAut R,
    α ^ m = 1 → α ∈ I

theorem i91_oddInner_g2der {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    i91OddInner (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))
      (LargeEvenChevParentIDImage LargeEvenCartanG2 K (LargeEvenChevGroup LargeEvenCartanG2 K)
        (LargeEvenChevH LargeEvenCartanG2 K true)) := by
  intro _ hna m hm α hα
  obtain ⟨r, rfl⟩ := CFSG.StandardType.RawAutSmall.mem_inner_g2der hK hna hm hα
  exact Subgroup.subset_closure (Or.inl (CFSG.StandardType.conj_mem_chevIDImage _ r))

theorem i91_oddInner_twF4der {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 0 + 1)) :
    i91OddInner (LargeEvenCenterQuot (LargeEvenTwF4H 0 K))
      (LargeEvenChevParentIDImage LargeEvenCartanF4 K (LargeEvenTwF4Parent 0 K)
        (LargeEvenTwF4H 0 K)) := by
  intro _ _ m hm α hα
  obtain ⟨r, rfl⟩ := CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
    (CFSG.StandardType.RawAutSmall.isPGroup_outer_twF4der rfl hK) hm hα
  exact Subgroup.subset_closure (Or.inl (CFSG.StandardType.conj_mem_chevIDImage _ r))

theorem i91_g2der_odd {l n : ℕ} {Q : LargeEvenRawCont} (h : LargeEvenRawDatum ⟨.G2der, l, n⟩ Q) :
    LargeEvenRawDatum ⟨.G2der, l, n⟩ fun R _ I F => Q R I F ∧ i91OddInner R I := by
  obtain ⟨K, instF, instFin, hK, hQ⟩ := h
  exact ⟨K, instF, instFin, hK, hQ, i91_oddInner_g2der hK⟩

theorem i91_twF4der_odd {l n : ℕ} (hn : n = 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum ⟨.twF4der, l, n⟩ Q) :
    LargeEvenRawDatum ⟨.twF4der, l, n⟩ fun R _ I F => Q R I F ∧ i91OddInner R I := by
  have ha : (n - 1) / 2 = 0 := by omega
  obtain ⟨K, instF, instFin, hK, hQ⟩ := h
  refine ⟨K, instF, instFin, hK, hQ, ?_⟩
  rw [ha, if_pos rfl]
  exact i91_oddInner_twF4der (by rw [hK, ha])

def i91FieldCont (p : ℕ) (J : Subgroup G) (b : G) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R ∧ (∃ x y : R, x * y ≠ y * x) ∧
    ∃ θ : PSimple p J ≃* R, LargeEvenPrimeField p lab I F (LargeEvenInduces θ (indRel p J b))

def i91InnCont (p : ℕ) (J : Subgroup G) (b : G) : LargeEvenRawCont :=
  fun R _ I _ => IsSimpleGroup R ∧ (∃ x y : R, x * y ≠ y * x) ∧
    ∃ θ : PSimple p J ≃* R, ∀ a ∈ Subgroup.zpowers b, ∃ φ ∈ I, LargeEvenInduces θ (indRel p J a) φ

theorem i91_pointwise {p : ℕ} (J : Subgroup G) {b : G} {lab : LargeEvenLabel}
    (hbN : b ∈ Subgroup.normalizer (J : Set G)) (hbp : b ^ p = 1)
    (hne : lab.tag ≠ .triD4 ∨ p ≠ 3) {R : Type} [Group R] {I F : Set (MulAut R)}
    (hs : IsSimpleGroup R) (hna : ∃ x y : R, x * y ≠ y * x) (θ : PSimple p J ≃* R)
    (hPa : IsSimpleGroup R → (∃ x y : R, x * y ≠ y * x) → CFSG.StandardType.GGOddAutInnField p I F)
    (hPfc : CFSG.StandardType.GGRawFieldConj p R I F)
    (hPinn : CFSG.StandardType.GGRawInnField p R I F) :
    i91FieldCont p J b lab R I F ∨ i91InnCont p J b R I F := by
  obtain ⟨hmul, hinv, hconj, -⟩ := hPinn hs hna
  have h1 : (1 : MulAut R) ∈ I := by
    have := hconj 1
    rwa [map_one] at this
  have hαpow : i91Phi p J θ ⟨b, hbN⟩⁻¹ ^ p = 1 := by
    rw [← map_pow]
    have h0 : (⟨b, hbN⟩⁻¹ : ↥(Subgroup.normalizer (J : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hbp)
    rw [h0, map_one]
  by_cases hαI : i91Phi p J θ ⟨b, hbN⟩⁻¹ ∈ I
  · exact Or.inr ⟨hs, hna, θ, i91_zpowers_mem J hbN θ hαI hmul hinv h1⟩
  · left
    obtain ⟨u, hu, f, hf, hαuf⟩ := hPa hs hna _ hαpow
    have hnot : u * f ∉ I := hαuf ▸ hαI
    have hpow' : (u * f) ^ p = 1 := hαuf ▸ hαpow
    obtain ⟨f', hf', u', hu', hord, heq⟩ := hPfc hs hna u hu f hf hnot hpow'
    refine ⟨hs, hna, θ, hne, f', hf', u', hu', hord, ?_⟩
    rw [← heq, ← hαuf]
    exact i91Phi_induces J θ ⟨b, hbN⟩

theorem i91_catalog_D4 {R : Type} [Group R] {f : ℕ} (hf : 1 ≤ f)
    (h : CFSG.Blueprint.LieModel R .POmegaPlus 4 2 f) :
    catalogIs R CFSG.LocalAnalysis.GLTheoremA.isD4any := by
  rcases h with ⟨-, hS⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := hS
    let _ := hfield
    let _ := hfinite
    obtain ⟨hp, -, hn⟩ := hadm
    let q : TauCeti.PrimePower := ⟨2, f, hp, by omega⟩
    have hv : (TauCeti.LieTypeIndex.D 4 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hn, not_false⟩
    obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField
      ⟨.D 4 q, hv⟩ K (by simp [TauCeti.ValidLieTypeIndex.fieldOrder, q, hK])
    exact ⟨TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩, rfl, ⟨(θ.trans
      (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
          (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ))).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv).symm⟩⟩
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)

theorem i91_catalog_TD4 {R : Type} [Group R] {f : ℕ}
    (h : CFSG.Blueprint.LieModel R .trialityD4 0 2 f) :
    catalogIs R (onLie fun | .trialityD4 _ => True | _ => False) := by
  rcases h with ⟨h1, -⟩ | ⟨-, -, hCEM⟩ | ⟨-, h2, -⟩ | ⟨-, h3, -⟩
  · exact absurd h1 (by decide)
  · obtain ⟨hadm, hm⟩ := hCEM
    have hf : 1 ≤ f := hadm.2.1
    let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf⟩
    have hq : q.card = 2 ^ f := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
      (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨TauCeti.CFSGIndex.lie ⟨_, hv⟩, trivial, ⟨e.trans b⟩⟩
  · exact absurd h2 (by decide)
  · exact absurd h3 (by decide)

theorem i91_holds (G : Type) [Group G] [Finite G] (p : ℕ) : I91FieldAt G p := by
  intro hp hp2 X J b hJ hchev hbN hbp hnon
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨hcomm, lab, hlab, hraw⟩ := CFSG.StandardType.ChevTwo.ys08_holds (PQuot p J)
    (isQuasisimple_pQuot_of_glaPComponent hp hJ) hchev
  obtain ⟨tg, rk, nn⟩ := lab
  by_cases hA : p = 3 ∧ (tg = .triD4 ∨ (tg = .D ∧ rk = 4))
  ·
    obtain ⟨hp3, hcase⟩ := hA
    subst hp3
    refine Or.inr ⟨rfl, ?_⟩
    have hM := CFSG.StandardType.Canonical.largeEvenRawDatum_markedModel
      (lab := ⟨tg, rk, nn⟩) hlab (by intro R _ I F h; exact h.2.1) hraw
    obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, -⟩, hMM⟩⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hM
    rcases hcase with ht | ⟨ht, hr⟩
    · subst ht
      have hL : CFSG.Blueprint.LieModel R .trialityD4 0 2 nn := hMM
      obtain ⟨i, hi, ⟨e⟩⟩ := i91_catalog_TD4 hL
      exact Or.inr ⟨i, hi, ⟨θ.trans e⟩⟩
    · subst ht
      subst hr
      have hL : CFSG.Blueprint.LieModel R .POmegaPlus 4 2 nn := hMM
      obtain ⟨i, hi, ⟨e⟩⟩ := i91_catalog_D4 hlab.1 hL
      exact Or.inl ⟨i, hi, ⟨θ.trans e⟩⟩
  by_cases hB : tg = .G2der ∨ tg = .twF4der
  ·
    have hodd : LargeEvenRawDatum ⟨tg, rk, nn⟩ (fun R _ I F =>
        (IsSimpleGroup R ∧ (∃ x y : R, x * y ≠ y * x) ∧ ∃ θ : PSimple p J ≃* R, True) ∧
          i91OddInner R I) := by
      rcases hB with rfl | rfl
      · exact i91_g2der_odd hraw
      · exact i91_twF4der_odd hlab.2.2 hraw
    have hin : LargeEvenRawDatum ⟨tg, rk, nn⟩ (i91InnCont p J b) := by
      refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hodd
      intro R _ I F h
      obtain ⟨⟨hs, hna, θ, -⟩, hI⟩ := h
      exact ⟨hs, hna, θ, i91_zpowers_odd J hbN hbp θ (fun α hα => hI hs hna p hpodd α hα)⟩
    exact (hnon.2 ⟨Subgroup.zpowers_le.mpr hbN, hcomm, ⟨tg, rk, nn⟩, hlab, hin⟩).elim
  ·
    have hTri : ¬ (tg = .triD4 ∧ p = 3) := fun h => hA ⟨h.2, Or.inl h.1⟩
    have hD4 : ¬ (tg = .D ∧ rk = 4 ∧ p = 3) := fun h => hA ⟨h.2.2, Or.inr ⟨h.1, h.2.1⟩⟩
    have hne : tg ≠ .triD4 ∨ p ≠ 3 := not_and_or.mp hTri
    have hG : tg ≠ .G2der := fun h => hB (Or.inl h)
    have hF : tg ≠ .twF4der := fun h => hB (Or.inr h)
    have hQw := (i91_rawIff hlab hG hF _).mp hraw
    have hA' := CFSG.StandardType.ggOddAutOn_all p ⟨tg, rk, nn⟩ hp hp2 hlab trivial hD4
    have hB' := CFSG.StandardType.ggRawFieldConjInputExc_holds p hp hp2 ⟨tg, rk, nn⟩ hlab hTri
    have hC' := CFSG.StandardType.ggRawInnFieldInput_holds p hp hp2 ⟨tg, rk, nn⟩ hlab
    have D3c := (i91_rawIff hlab hG hF _).mpr (hC' _ (hB' _ (hA' _ hQw)))
    have Dg : LargeEvenRawDatum ⟨tg, rk, nn⟩ (fun R _ I F =>
        i91FieldCont p J b ⟨tg, rk, nn⟩ R I F ∨ i91InnCont p J b R I F) := by
      refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ D3c
      intro R _ I F h
      obtain ⟨⟨⟨⟨hs, hna, θ, -⟩, hPa⟩, hPfc⟩, hPinn⟩ := h
      exact i91_pointwise J hbN hbp hne hs hna θ hPa hPfc hPinn
    rcases i91_or_split (A := i91FieldCont p J b ⟨tg, rk, nn⟩) (B := i91InnCont p J b) Dg with
      hfp | hin
    · exact Or.inl ⟨hbN, hcomm, ⟨tg, rk, nn⟩, hlab, hfp⟩
    · exact (hnon.2 ⟨Subgroup.zpowers_le.mpr hbN, hcomm, ⟨tg, rk, nn⟩, hlab, hin⟩).elim

end I91

end CFSG.LocalAnalysis.GLTheoremA

end
