module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcGap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapGlue
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixAut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixData
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LieType.Steinberg.G2.Perfect
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.Blueprint.ChevalleyParameterAddition
public import CFSG.Blueprint.ChevalleySimpleRoots
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.Blueprint.Chevalley (Tag adjointGroup IsRoot xOp yOp xOp_mul_xOp yOp_mul_yOp xOp_zero
  yOp_zero upTransport downTransport)
open CFSG.LieType.Chevalley (entrywiseAdjointAut fixedFieldImage fixedFieldImage_le
  fixedFieldImageEquiv entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
  center_adjointGroup_eq_bot fixSubfield)
open scoped commutatorElement

section Squares


theorem sq_mem_commutator_adjointGroup (τ : Tag) {k : Type} [Field k] [CharP k 2] :
    ∀ g ∈ adjointGroup τ k, g ^ 2 ∈ ⁅adjointGroup τ k, adjointGroup τ k⁆ := by
  intro g hg
  have key := Subgroup.closure_induction
    (p := fun g _ => g ∈ adjointGroup τ k ∧ g ^ 2 ∈ ⁅adjointGroup τ k, adjointGroup τ k⁆)
    (fun x hx => by
      refine ⟨Subgroup.subset_closure hx, ?_⟩
      have h1 : x * x = 1 := by
        obtain ⟨i, c, hx | hx⟩ := hx
        · apply Units.ext
          rw [Units.val_mul, hx, xOp_mul_xOp (upTransport τ), CharTwo.add_self_eq_zero, xOp_zero,
            Units.val_one]
        · apply Units.ext
          rw [Units.val_mul, hx, yOp_mul_yOp (downTransport τ), CharTwo.add_self_eq_zero, yOp_zero,
            Units.val_one]
      rw [pow_two, h1]
      exact Subgroup.one_mem _)
    ⟨Subgroup.one_mem _, by rw [one_pow]; exact Subgroup.one_mem _⟩
    (fun x y _ _ ⟨hxA, hx2⟩ ⟨hyA, hy2⟩ => by
      refine ⟨Subgroup.mul_mem _ hxA hyA, ?_⟩
      have he : (x * y) ^ 2 = x ^ 2 * ⁅x⁻¹, y⁆ * y ^ 2 := by
        rw [commutatorElement_def, inv_inv, pow_two, pow_two, pow_two]
        simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
      rw [he]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx2
        (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxA) hyA)) hy2)
    (fun x _ ⟨hxA, hx2⟩ => ⟨Subgroup.inv_mem _ hxA, by rw [inv_pow]; exact Subgroup.inv_mem _ hx2⟩)
    hg
  exact key.2

theorem sq_mem_ggFixDer_of_adjoint {R : Type} [Group R] {f : MulAut R} (τ : Tag) {k : Type}
    [Field k] [CharP k 2] (E : adjointGroup τ k ≃* ↥(ggFixSub f)) :
    ∀ g ∈ ggFixSub f, g ^ 2 ∈ ggFixDer f := by
  intro g hg
  have hA : ∀ a : ↥(adjointGroup τ k), a ^ 2 ∈ commutator ↥(adjointGroup τ k) := by
    intro a
    have h1 := sq_mem_commutator_adjointGroup τ a.1 a.2
    rw [← Subgroup.map_subtype_commutator] at h1
    obtain ⟨b, hb, hba⟩ := h1
    have hb' : b = a ^ 2 := Subtype.ext (by simpa using hba)
    exact hb' ▸ hb
  have hmap : (commutator ↥(adjointGroup τ k)).map E.toMonoidHom = commutator ↥(ggFixSub f) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 E.surjective]
  have h2 : (⟨g, hg⟩ : ↥(ggFixSub f)) ^ 2 ∈ commutator ↥(ggFixSub f) := by
    rw [← hmap]
    exact ⟨E.symm ⟨g, hg⟩ ^ 2, hA _, by simp⟩
  have h3 : (((⟨g, hg⟩ : ↥(ggFixSub f)) ^ 2 : ↥(ggFixSub f)) : R) ∈
      (commutator ↥(ggFixSub f)).map (ggFixSub f).subtype := ⟨_, h2, rfl⟩
  rw [Subgroup.map_subtype_commutator] at h3
  show g ^ 2 ∈ ⁅ggFixSub f, ggFixSub f⁆
  simpa using h3

end Squares

section G2


theorem g2_fixed_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (σ : K ≃+* K) :
    Nonempty (adjointGroup Tag.G2 (fixSubfield σ) ≃*
      ↥(ggAutFixedSubgroup (entrywiseAdjointAut Tag.G2 σ))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcharP : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hfix : ggAutFixedSubgroup (entrywiseAdjointAut Tag.G2 σ) =
      (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup Tag.G2 σ,
      entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (Or.inl rfl) hchar σ]
  have hJC : fixedFieldImage Tag.G2 σ ≤ adjointGroup Tag.G2 K :=
    fun x hx => (fixedFieldImage_le hx).1
  exact ⟨(fixedFieldImageEquiv (τ := Tag.G2) σ).trans
    ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.subgroupCongr hfix.symm))⟩

theorem g2_chevFixGroupOn {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : 0 < p) :
    ChevFixGroupOn K Tag.G2 (IsRoot Tag.G2) n p := by
  suffices h : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.G2) K), H = adjointGroup Tag.G2 K →
      ∀ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot Tag.G2) K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup Tag.G2 k ≃* ↥(ggFixSub f)) from
    h _ (chevH_false_eq_adjointGroup K Tag.G2)
  intro H hH f hf hford
  subst hH
  have hr : 0 < Tag.G2.rank := by decide
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hford]
  obtain ⟨-, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
    Nat.prime_two hn hK σ
  rw [hσp] at hcard
  obtain ⟨E⟩ := g2_fixed_equiv hn hK σ
  let m : LargeEvenCenterQuot (adjointGroup Tag.G2 K) ≃* adjointGroup Tag.G2 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have key : ∀ x, ((1 : MulAut (adjointGroup Tag.G2 K)) * entrywiseAdjointAut Tag.G2 σ * 1⁻¹)
      (m x) = m (f x) := by
    intro x
    rw [one_mul, inv_one, mul_one, ← hσ, RecipeExcLang.autEquiv, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  obtain ⟨E'⟩ := gff_nonempty_equiv_fixed m f 1 (entrywiseAdjointAut Tag.G2 σ) key E
  exact ⟨↥(fixSubfield σ), inferInstance, inferInstance, hcard,
    ⟨E'.symm.trans (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))⟩⟩

theorem g2_fixGroup {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false))}
    (hf : f ∈ LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false))
    (hord : orderOf f = p) :
    p ∣ n ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
      Nonempty (adjointGroup Tag.G2 k ≃* ↥(ggFixSub f)) := by
  refine ⟨dvd_of_chevField_order hn hK hp (LargeEvenChevH LargeEvenCartanG2 K false)
    (fun σ h hh => chevH_stable LargeEvenCartanG2 K false σ h hh) hf hord, ?_⟩
  have h := (g2_chevFixGroupOn hn hK hp.pos).of_eq (largeEvenIsRoot_eq_isRoot Tag.G2).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL LargeEvenCartanG2 K),
      H = MarkChev.chevH LargeEvenCartanG2 (LargeEvenIsRoot LargeEvenCartanG2) K false →
      ∀ f ∈ LargeEvenChevFieldImage LargeEvenCartanG2 K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup Tag.G2 k ≃* ↥(ggFixSub f)) from
    key _ (largeEvenChevH_eq LargeEvenCartanG2 K false) f hf hord
  intro H hH
  subst hH
  exact h

variable {p : ℕ}

theorem geomBody_g2 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n)
    (hinn : LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false) ⊆
      LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false))) :
    GeomBody p ⟨.G2, 0, n⟩ (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false))
      (LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false))
      (LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false)) := by
  refine geomBody_of_field (by simp) fun hS hna f hf hord => ?_
  obtain ⟨hpn, k, hkF, hkfin, hk, ⟨E⟩⟩ := g2_fixGroup (by omega) hK hp hf hord
  haveI := hS
  have hZ := center_eq_bot_of_simple_noncomm hna
  have hI : ∀ φ ∈ LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false),
      φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : LargeEvenCenterQuot
        (LargeEvenChevH LargeEvenCartanG2 K false) →* _) := by
    intro φ hφ _
    obtain ⟨r, hr⟩ := hinn hφ
    exact ⟨r, hr⟩
  have hdiv : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  rcases Nat.lt_or_ge (n / p) 2 with hlt | hge
  ·
    have h1 : n / p = 1 := by omega
    have hk2 : Nat.card k = 2 := by rw [hk, h1]; norm_num
    haveI : Fintype k := Fintype.ofFinite k
    haveI : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hk2]; norm_num)
    have hC : StatedClassicalModel ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ .PSU 3 3 1 := by
      rcases CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk2 with
        ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact h
      all_goals exact absurd h0 (by norm_num)
    obtain ⟨-, K₃, _, _, hK₃, ⟨eU⟩⟩ := hC
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsSimpleGroup (StatedProj (StatedSU 3 (3 ^ 1) K₃)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K₃ 3 1 hK₃ 3 le_rfl
        (by decide)
    haveI : IsSimpleGroup ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ := eU.isSimpleGroup
    haveI : Group.IsPerfect ↥(StatedSU 3 (3 ^ 1) K₃) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 3) (f := 1) hK₃ le_rfl (by decide)
    haveI : Group.IsPerfect (StatedProj (StatedSU 3 (3 ^ 1) K₃)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isPerfect (StatedProj (StatedSU 3 (3 ^ 1) K₃))
    have hnaX : ∃ a b : ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆, a * b ≠ b * a :=
      ⟨eU.symm x, eU.symm y, fun h => hxy (by simpa using congrArg eU h)⟩
    have hZX := center_eq_bot_of_simple_noncomm hnaX
    have hsimp : IsSimpleGroup (LargeEvenCenterQuot ⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆) :=
      (centerQuotEquivOfBot hZX).isSimpleGroup
    have hnab : ∃ a b : LargeEvenCenterQuot ⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆,
        a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnaX
      let eR := centerQuotEquivOfBot hZX
      exact ⟨eR.symm a, eR.symm b, fun h => hab (by simpa using congrArg eR h)⟩
    have hlab : GGHasLabel (⟨.G2der, 0, 1⟩ : LargeEvenLabel)
        (CFSG.Blueprint.DerivedCentralQuotient (adjointGroup Tag.G2 k)) := by
      unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      obtain ⟨eD⟩ := centerQuot_commutator_chevGroup_equiv k Tag.G2
      exact ⟨k, hkF, hkfin, hk2, ⟨eD.symm⟩⟩
    have hmap : (commutator ↥(adjointGroup Tag.G2 k)).map E.toMonoidHom =
        commutator ↥(ggFixSub f) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.2 E.surjective]
    have e1 : ↥(ggFixDer f) ≃* ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ :=
      (ggCommutatorEquiv (ggFixSub f)).trans
        (((Subgroup.equivMapOfInjective _ E.toMonoidHom E.injective).trans
          (MulEquiv.subgroupCongr hmap)).symm.trans
          (ggCommutatorEquiv (adjointGroup Tag.G2 k)).symm)
    have hpK : ∀ g ∈ ggFixSub f, g ^ p = 1 → g ∈ ggFixDer f :=
      pow_mem_ggFixDer_of_coprime fun g hg =>
        ⟨2, Nat.coprime_two_right.2 (hp.odd_of_ne_two hp2),
          sq_mem_ggFixDer_of_adjoint Tag.G2 E g hg⟩
    exact fixAlt_of_hasLabel (lab₀ := ⟨.G2der, 0, 1⟩)
      (R₀ := CFSG.Blueprint.DerivedCentralQuotient (adjointGroup Tag.G2 k)) hp hp2 hZ hI hpK
      ⟨le_rfl, rfl, rfl⟩ hsimp hnab hlab ⟨e1.trans (centerQuotEquivOfBot hZX).symm⟩
  ·
    have h3 : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n / p) := Nat.pow_le_pow_right (by norm_num) hge
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k h3
    haveI : Group.IsPerfect ↥(adjointGroup Tag.G2 k) := hq.1
    have hZk : Subgroup.center (adjointGroup Tag.G2 k) = ⊥ := center_adjointGroup_eq_bot
    have hPC : Group.IsPerfect ↥(ggFixSub f) :=
      Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
    have hdef : ggFixDer f = ggFixSub f := Subgroup.isPerfect_iff.1 hPC
    have hlab : GGHasLabel (⟨.G2, 0, n / p⟩ : LargeEvenLabel)
        (LargeEvenCenterQuot (adjointGroup Tag.G2 k)) := by
      unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      obtain ⟨eC⟩ := centerQuot_chevGroup_equiv k Tag.G2
      exact ⟨k, hkF, hkfin, hk, ⟨eC.symm⟩⟩
    exact fixAlt_of_hasLabel (lab₀ := ⟨.G2, 0, n / p⟩) hp hp2 hZ hI (pow_mem_ggFixDer_of_eq hdef)
      ⟨hdiv, rfl, hge⟩ hq.2.1 hq.2.2 hlab
      ⟨(MulEquiv.subgroupCongr hdef).trans (E.symm.trans (centerQuotEquivOfBot hZk).symm)⟩

theorem cAll_geomBody_g2 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) :
    MI.CAll ⟨.G2, 0, n⟩ (GeomBody p ⟨.G2, 0, n⟩) := by
  have hlab : LargeEvenInLambda2 ⟨.G2, 0, n⟩ := ⟨show 1 ≤ n by omega, rfl, hn⟩
  have hinn := (MI.canonAll_iff_legacyAll hlab (by simp [MI.DerivedLab]) _).2
    (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inl rfl)))
  have hgeom : MI.CAll ⟨.G2, 0, n⟩ fun R _ I F =>
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F → GeomBody p ⟨.G2, 0, n⟩ R I F := by
    intro Q hQ
    dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_and (fun K _ _ hK hguard hS hna =>
      geomBody_g2 hp hp2 hn K hK (hguard hS hna) hS hna) hQ
  exact MI.CAll.mono (fun R _ I F h => h.2 h.1) (MI.CAll.and hinn hgeom)

end G2

end CFSG.LocalAnalysis.GLTheoremA.T156

end
