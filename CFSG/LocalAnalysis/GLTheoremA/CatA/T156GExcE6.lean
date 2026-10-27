module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcGap
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevModel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Model
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixAut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixData
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
public import CFSG.LieType.SeitzGeneration.ExcWideThree.FixedE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.StandardType.RecipeExcLang
open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA


theorem e6_fixed_equiv_of_cube {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hcube : CFSG.LieType.SeitzGeneration.ExcWideThree.CubeDescent σ) :
    Nonempty (adjointGroup Tag.E6 (fixSubfield σ) ≃*
      ↥(ggAutFixedSubgroup (entrywiseAdjointAut Tag.E6 σ))) := by
  have hfix : ggAutFixedSubgroup (entrywiseAdjointAut Tag.E6 σ) =
      (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) := by
    rw [gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup Tag.E6 σ,
      CFSG.LieType.SeitzGeneration.ExcWideThree.entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow σ
        hcube]
  have hJC : fixedFieldImage Tag.E6 σ ≤ adjointGroup Tag.E6 K :=
    fun x hx => (fixedFieldImage_le hx).1
  exact ⟨(fixedFieldImageEquiv (τ := Tag.E6) σ).trans
    ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.subgroupCongr hfix.symm))⟩

theorem e6_chevFixGroupOn_odd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (hodd : Odd n) {p : ℕ} (hp : 0 < p) :
    ChevFixGroupOn K Tag.E6 (IsRoot Tag.E6) n p := by
  suffices h : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.E6) K), H = adjointGroup Tag.E6 K →
      ∀ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot Tag.E6) K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup Tag.E6 k ≃* ↥(ggFixSub f)) from
    h _ (chevH_false_eq_adjointGroup K Tag.E6)
  intro H hH f hf hford
  subst hH
  have hr : 0 < Tag.E6.rank := by decide
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hford]
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
    Nat.prime_two hn hK σ
  rw [hσp] at hdvd hcard
  have hodd' : Odd (n / p) := by
    obtain ⟨c, hc⟩ := hdvd
    have hc' : n / p = c := by rw [hc, Nat.mul_div_cancel_left c hp]
    rw [hc']
    exact (Nat.odd_mul.1 (hc ▸ hodd)).2
  have hcube : CFSG.LieType.SeitzGeneration.ExcWideThree.CubeDescent σ := by
    intro b _ _
    have hcop : (Nat.card (fixSubfield σ)ˣ).Coprime 3 := by
      rw [Nat.card_units, hcard]
      exact coprime_two_pow_sub_one_three hodd'
    refine ⟨(powCoprime hcop).symm b, ?_⟩
    have h1 := (powCoprime hcop).apply_symm_apply b
    rw [powCoprime_apply] at h1
    exact h1.symm
  obtain ⟨E⟩ := e6_fixed_equiv_of_cube σ hcube
  let m : LargeEvenCenterQuot (adjointGroup Tag.E6 K) ≃* adjointGroup Tag.E6 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have key : ∀ x, ((1 : MulAut (adjointGroup Tag.E6 K)) * entrywiseAdjointAut Tag.E6 σ * 1⁻¹)
      (m x) = m (f x) := by
    intro x
    rw [one_mul, inv_one, mul_one, ← hσ, RecipeExcLang.autEquiv, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  obtain ⟨E'⟩ := gff_nonempty_equiv_fixed m f 1 (entrywiseAdjointAut Tag.E6 σ) key E
  exact ⟨↥(fixSubfield σ), inferInstance, inferInstance, hcard,
    ⟨E'.symm.trans (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))⟩⟩

theorem e6_fixGroup_odd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (hodd : Odd n) {p : ℕ} (hp : p.Prime)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.E6.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false))
    (hord : orderOf f = p) :
    p ∣ n ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
      Nonempty (adjointGroup Tag.E6 k ≃* ↥(ggFixSub f)) := by
  refine ⟨Y10GField.dvd_of_chevField_order hn hK hp (LargeEvenChevH Tag.E6.cartan K false)
    (fun σ h hh => chevH_stable Tag.E6.cartan K false σ h hh) hf hord, ?_⟩
  have h := (e6_chevFixGroupOn_odd hn hK hodd hp.pos).of_eq (largeEvenIsRoot_eq_isRoot Tag.E6).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL Tag.E6.cartan K),
      H = MarkChev.chevH Tag.E6.cartan (LargeEvenIsRoot Tag.E6.cartan) K false →
      ∀ f ∈ LargeEvenChevFieldImage Tag.E6.cartan K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup Tag.E6 k ≃* ↥(ggFixSub f)) from
    key _ (largeEvenChevH_eq Tag.E6.cartan K false) f hf hord
  intro H hH
  subst hH
  exact h

variable {p : ℕ}

theorem geomBody_e6_odd (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hodd : Odd n) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hinn : LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false) ⊆
      LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenChevH Tag.E6.cartan K false))) :
    GeomBody p ⟨.E6, 0, n⟩ (LargeEvenCenterQuot (LargeEvenChevH Tag.E6.cartan K false))
      (LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false))
      (LargeEvenChevFieldImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) := by
  have hn : 1 ≤ n := hodd.pos
  refine geomBody_of_field (by simp) fun hS hna f hf hord => ?_
  obtain ⟨hpn, k, hkF, hkfin, hk, ⟨E⟩⟩ := e6_fixGroup_odd hn hK hodd hp hf hord
  haveI := hS
  have hZ := center_eq_bot_of_simple_noncomm hna
  have hI : ∀ φ ∈ LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false),
      φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : LargeEvenCenterQuot
        (LargeEvenChevH Tag.E6.cartan K false) →* _) := by
    intro φ hφ _
    obtain ⟨r, hr⟩ := hinn hφ
    exact ⟨r, hr⟩
  have hdiv : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hq := CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k
  haveI : Group.IsPerfect ↥(adjointGroup Tag.E6 k) := hq.1
  have hZk : Subgroup.center (adjointGroup Tag.E6 k) = ⊥ := center_adjointGroup_eq_bot
  have hPC : Group.IsPerfect ↥(ggFixSub f) :=
    Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
  have hdef : ggFixDer f = ggFixSub f := Subgroup.isPerfect_iff.1 hPC
  have hlab : GGHasLabel (⟨.E6, 0, n / p⟩ : LargeEvenLabel)
      (LargeEvenCenterQuot (adjointGroup Tag.E6 k)) := by
    unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
    obtain ⟨eC⟩ := centerQuot_chevGroup_equiv k Tag.E6
    exact ⟨k, hkF, hkfin, hk, ⟨eC.symm⟩⟩
  exact fixAlt_of_hasLabel (lab₀ := ⟨.E6, 0, n / p⟩) hp hp2 hZ hI (pow_mem_ggFixDer_of_eq hdef)
    ⟨hdiv, rfl⟩ hq.2.1 hq.2.2 hlab
    ⟨(MulEquiv.subgroupCongr hdef).trans (E.symm.trans (centerQuotEquivOfBot hZk).symm)⟩

theorem cAll_geomBody_e6_odd (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hodd : Odd n) :
    MI.CAll ⟨.E6, 0, n⟩ (GeomBody p ⟨.E6, 0, n⟩) := by
  have hlab : LargeEvenInLambda2 ⟨.E6, 0, n⟩ := ⟨show 1 ≤ n from hodd.pos, rfl⟩
  have hinn := (MI.canonAll_iff_legacyAll hlab (by simp [MI.DerivedLab]) _).2
    (largeEvenLabelAll_subset_inn_E6_odd hodd)
  have hraw : ∀ (k : ℕ) (Q : LargeEvenRawCont), CFSG.Assembly.LargeEvenRawDatum ⟨.E6, 0, k⟩ Q =
      LargeEvenRecipeChevalley Tag.E6.cartan (2 ^ k) false Q :=
    fun _ _ => rfl
  have hgeom : MI.CAll ⟨.E6, 0, n⟩ fun R _ I F =>
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F →
        GeomBody p ⟨.E6, 0, n⟩ R I F := by
    intro Q hQ
    rw [hraw] at hQ ⊢
    exact recipeChevalley_and (fun K _ _ hK hguard hS hna =>
      geomBody_e6_odd hp hp2 hodd K hK (hguard hS hna) hS hna) hQ
  exact MI.CAll.mono (fun R _ I F h => h.2 h.1) (MI.CAll.and hinn hgeom)

theorem e6FixOn_isRoot_even {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (heven : Even n) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    E6FixOn K (IsRoot Tag.E6) n p := by
  intro H hH f hf hord
  rw [chevH_false_eq_adjointGroup K Tag.E6] at hH
  subst hH
  have hrank : 0 < Tag.E6.rank := by decide
  obtain ⟨σ, hσ⟩ :=
    RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField (τ := Tag.E6) (K := K) hf
  have hσord : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut
      (τ := Tag.E6) (K := K) hrank σ, ← hσ, MulEquiv.orderOf_eq, hord]
  have hσpow : σ ^ p = 1 := by
    rw [← hσord]
    exact pow_orderOf_eq_one σ
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  obtain ⟨hdvd, hcardfix⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      Nat.prime_two hn hK σ
  rw [hσord] at hdvd hcardfix
  have hbig : 2 < Nat.card (fixSubfield σ) := by
    rw [hcardfix]
    obtain ⟨c, hc⟩ := hdvd
    have hc' : n / p = c := by rw [hc, Nat.mul_div_cancel_left c hp.pos]
    have hceven : Even c := by
      rcases Nat.even_mul.1 (hc ▸ heven) with h | h
      · exact absurd h (Nat.not_even_iff_odd.2 (hp.odd_of_ne_two hp2))
      · exact h
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      omega
    have hc2 : 2 ≤ c := by
      obtain ⟨j, hj⟩ := hceven
      omega
    rw [hc']
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc2
  let m : LargeEvenCenterQuot (adjointGroup Tag.E6 K) ≃* adjointGroup Tag.E6 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  let m₀ : LargeEvenCenterQuot (adjointGroup Tag.E6 ↥(fixSubfield σ)) ≃*
      adjointGroup Tag.E6 ↥(fixSubfield σ) :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have hm : MulAut.congr m = autEquiv Tag.E6 K := rfl
  have hm₀ : MulAut.congr m₀ = autEquiv Tag.E6 ↥(fixSubfield σ) := rfl
  have hs : entrywiseAdjointAut Tag.E6 σ = MulAut.congr m f := by
    rw [← hσ, ← hm]
  refine ⟨↥(fixSubfield σ), inferInstance, inferInstance, hcardfix, ?_⟩
  intro H₀ hH₀
  rw [chevH_false_eq_adjointGroup ↥(fixSubfield σ) Tag.E6] at hH₀
  subst hH₀
  have hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 ↥(fixSubfield σ)
  haveI : IsSimpleGroup (LargeEvenCenterQuot (adjointGroup Tag.E6 ↥(fixSubfield σ))) :=
    hq.2.1
  refine ⟨hq.2.1, hq.2.2, ?_⟩
  refine ggFixGeom_of_transport hq.2.2 m m₀ hs (E6FieldFix.fixE6Equiv σ hσpow hcop) ?_ ?_
  · intro φ hφ hcomm
    obtain ⟨w, hw⟩ :=
      RecipeExcLang.exists_inndiagConj_of_mem_markID (τ := Tag.E6) (K := K) hφ
    have hwm : MulAut.congr m φ = inndiagConj Tag.E6 K w := by
      rw [← hw, ← hm]
    have hc : inndiagConj Tag.E6 K w * entrywiseAdjointAut Tag.E6 σ =
        entrywiseAdjointAut Tag.E6 σ * inndiagConj Tag.E6 K w := by
      have h1 := congrArg (MulAut.congr m) hcomm
      rwa [map_mul, map_mul, hwm, ← hs] at h1
    obtain ⟨w₀, hw₀⟩ :=
      E6FieldFix.exists_inndiagConj_restrict hn hK hp hσord hσpow hcop w hc
    refine ⟨(autEquiv Tag.E6 ↥(fixSubfield σ)).symm
      (inndiagConj Tag.E6 ↥(fixSubfield σ) w₀), ?_, ?_⟩
    · exact RecipeExcLang.inndiagConj_mem_markID w₀
    · intro y
      have h0 : MulAut.congr m₀ ((autEquiv Tag.E6 ↥(fixSubfield σ)).symm
          (inndiagConj Tag.E6 ↥(fixSubfield σ) w₀)) =
          inndiagConj Tag.E6 ↥(fixSubfield σ) w₀ := by
        rw [← hm₀]
        exact MulEquiv.apply_symm_apply _ _
      rw [hwm, h0]
      exact hw₀ y
  · intro φ hφ hcomm hfix
    obtain ⟨w, hw⟩ :=
      RecipeExcLang.exists_inndiagConj_of_mem_markID (τ := Tag.E6) (K := K) hφ
    have hwm : MulAut.congr m φ = inndiagConj Tag.E6 K w := by
      rw [← hw, ← hm]
    have hfixw : ∀ x : ↥(ggFixSub (entrywiseAdjointAut Tag.E6 σ)),
        inndiagConj Tag.E6 K w (x : adjointGroup Tag.E6 K) = x := by
      intro x
      rw [← hwm]
      exact hfix x
    have hw1 : inndiagConj Tag.E6 K w = 1 :=
      E6FieldFix.eq_one_of_inndiagConj_fixes hbig w hfixw
    have h1 : MulAut.congr m φ = 1 := by rw [hwm, hw1]
    exact (MulAut.congr m).injective (by rw [h1, map_one])

theorem e6_fixStd_even {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (heven : Even n) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.E6.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false))
    (hord : orderOf f = p) :
    LargeEvenRecipeChevalley Tag.E6.cartan (2 ^ (n / p)) false fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        ∃ θ₀ : ggFixDer f ≃* R₀,
          GGFixGeom
            (LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) f I₀
            θ₀ := by
  have h := (e6FixOn_isRoot_even hn hK heven hp hp2 hp3).of_eq
    (largeEvenIsRoot_eq_isRoot Tag.E6).symm
  obtain ⟨k, _, _, hk, hconcl⟩ :=
    h (LargeEvenChevH Tag.E6.cartan K false) (largeEvenChevH_eq _ K false) f hf hord
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  obtain ⟨hs, hna, θ₀, hg⟩ :=
    hconcl (LargeEvenChevH Tag.E6.cartan k false) (largeEvenChevH_eq _ k false)
  refine ⟨hs, hna, θ₀, ?_⟩
  rw [largeEvenChevIDImage_eq, largeEvenChevIDImage_eq]
  exact hg

theorem cAll_geomBody_e6_even (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {n : ℕ} (hn : 1 ≤ n)
    (heven : Even n) : MI.CAll ⟨.E6, 0, n⟩ (GeomBody p ⟨.E6, 0, n⟩) := by
  have hraw : ∀ (k : ℕ) (Q : LargeEvenRawCont), CFSG.Assembly.LargeEvenRawDatum ⟨.E6, 0, k⟩ Q =
      LargeEvenRecipeChevalley Tag.E6.cartan (2 ^ k) false Q :=
    fun _ _ => rfl
  intro Q hQ
  rw [hraw] at hQ ⊢
  refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
  refine geomBody_of_field (by simp) fun _ _ f hf hord => ?_
  have h := e6_fixStd_even hn hK heven hp hp2 hp3 hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨.E6, 0, n / p⟩ := ⟨one_le_of_card_field hK₀, rfl⟩
  refine fixAlt_of_raw hlab₀ ?_
  rw [hraw]
  exact e6_fixStd_even hn hK heven hp hp2 hp3 hf hord

end CFSG.LocalAnalysis.GLTheoremA.T156

end
