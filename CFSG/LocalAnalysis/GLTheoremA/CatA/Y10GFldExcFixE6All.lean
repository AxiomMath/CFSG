module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcGap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcOrd
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixAut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixData
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherCore
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Chevalley (Tag adjointGroup IsRoot ModGL)
open CFSG.LieType.Chevalley (entrywiseAdjointAut fixSubfield entrywiseFixedGroup fixedFieldImage
  fixedFieldImage_le fixedFieldImageEquiv Chevalley_coordinate_field_fixed_normal_subgroup
  center_adjointGroup_eq_bot)
open scoped commutatorElement

section E6All


theorem fixE6_derived_fixed {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    ⁅(entrywiseFixedGroup Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K),
      (entrywiseFixedGroup Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K)⁆ =
      (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) := by
  obtain ⟨-, -, -, hJΓ, -, hNorm, hAb⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup Tag.E6 K σ
  haveI : ((fixedFieldImage Tag.E6 σ).subgroupOf (entrywiseFixedGroup Tag.E6 σ)).Normal := hNorm
  have hcomm : ∀ x ∈ entrywiseFixedGroup Tag.E6 σ, ∀ y ∈ entrywiseFixedGroup Tag.E6 σ,
      ⁅x, y⁆ ∈ fixedFieldImage Tag.E6 σ := by
    intro x hx y hy
    set N := (fixedFieldImage Tag.E6 σ).subgroupOf (entrywiseFixedGroup Tag.E6 σ) with hN
    let x' : ↥(entrywiseFixedGroup Tag.E6 σ) := ⟨x, hx⟩
    let y' : ↥(entrywiseFixedGroup Tag.E6 σ) := ⟨y, hy⟩
    have h1 : ⁅(QuotientGroup.mk' N) x', (QuotientGroup.mk' N) y'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hAb _ _
    have h2 : (QuotientGroup.mk' N) ⁅x', y'⁆ = 1 := by
      rw [map_commutatorElement]
      exact h1
    have h3 : ⁅x', y'⁆ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      rw [← h2]
      rfl
    have hc : ((⁅x', y'⁆ : ↥(entrywiseFixedGroup Tag.E6 σ)) : ModGL Tag.E6 K) = ⁅x, y⁆ :=
      map_commutatorElement (entrywiseFixedGroup Tag.E6 σ).subtype x' y'
    rw [← hc]
    exact (Subgroup.mem_subgroupOf).1 h3
  have hle : ⁅entrywiseFixedGroup Tag.E6 σ, entrywiseFixedGroup Tag.E6 σ⁆ ≤
      fixedFieldImage Tag.E6 σ :=
    Subgroup.commutator_le.2 hcomm
  have hq := CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 ↥(fixSubfield σ)
  haveI : Group.IsPerfect (adjointGroup Tag.E6 ↥(fixSubfield σ)) := hq.1
  have hJperf : Group.IsPerfect ↥(fixedFieldImage Tag.E6 σ) :=
    Group.IsPerfect.ofSurjective (f := (fixedFieldImageEquiv (τ := Tag.E6) σ).toMonoidHom)
      (fixedFieldImageEquiv (τ := Tag.E6) σ).surjective
  haveI : Group.IsPerfect ↥(fixedFieldImage Tag.E6 σ) := hJperf
  have hJJ : ⁅fixedFieldImage Tag.E6 σ, fixedFieldImage Tag.E6 σ⁆ = fixedFieldImage Tag.E6 σ :=
    Subgroup.isPerfect_iff.1 hJperf
  have hJA : fixedFieldImage Tag.E6 σ ≤ adjointGroup Tag.E6 K := fun x hx =>
    (fixedFieldImage_le hx).1
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy ⊢
    have hc : ((⁅x, y⁆ : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
        ⁅(x : ModGL Tag.E6 K), (y : ModGL Tag.E6 K)⁆ :=
      map_commutatorElement (adjointGroup Tag.E6 K).subtype x y
    rw [hc]
    exact hcomm _ hx _ hy
  · have hJAperf : Group.IsPerfect ↥((fixedFieldImage Tag.E6 σ).subgroupOf
        (adjointGroup Tag.E6 K)) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJA).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hJA).symm.surjective
    have hJAJA := Subgroup.isPerfect_iff.1 hJAperf
    calc (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K)
        = ⁅(fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K),
            (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K)⁆ := hJAJA.symm
      _ ≤ _ := Subgroup.commutator_mono (Subgroup.subgroupOf_mono _ hJΓ)
          (Subgroup.subgroupOf_mono _ hJΓ)

@[expose] def E6DerOn (K : Type) [Field K] (S : (Fin Tag.E6.rank → ℤ) → Prop) (n p : ℕ) : Prop :=
  ∀ f ∈ RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH Tag.E6.cartan S K false),
    orderOf f = p → ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
      Nonempty (↥(ggFixDer f) ≃* adjointGroup Tag.E6 k)

theorem E6DerOn.of_eq {K : Type} [Field K] {S S' : (Fin Tag.E6.rank → ℤ) → Prop} {n p : ℕ}
    (hS : S = S') (h : E6DerOn K S n p) : E6DerOn K S' n p :=
  hS ▸ h

theorem fixE6all_model {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : 0 < p) : E6DerOn K (IsRoot Tag.E6) n p := by
  suffices h : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.E6) K), H = adjointGroup Tag.E6 K →
      ∀ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot Tag.E6) K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (↥(ggFixDer f) ≃* adjointGroup Tag.E6 k) from
    h _ (chevH_false_eq_adjointGroup K Tag.E6)
  intro H hH f hf hford
  subst hH
  have hr : 0 < Tag.E6.rank := by decide
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hford]
  obtain ⟨-, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
    Nat.prime_two hn hK σ
  rw [hσp] at hcard
  let m : LargeEvenCenterQuot (adjointGroup Tag.E6 K) ≃* adjointGroup Tag.E6 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have key : ∀ x, ((1 : MulAut (adjointGroup Tag.E6 K)) * entrywiseAdjointAut Tag.E6 σ * 1⁻¹)
      (m x) = m (f x) := by
    intro x
    rw [one_mul, inv_one, mul_one, ← hσ, RecipeExcLang.autEquiv, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have key' : ∀ x, entrywiseAdjointAut Tag.E6 σ (m x) = m (f x) := by
    intro x
    simpa using key x
  have hmap : (ggFixSub f).map m.toMonoidHom = ggAutFixedSubgroup (entrywiseAdjointAut Tag.E6 σ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : f x = x := hx
      show entrywiseAdjointAut Tag.E6 σ (m x) = m x
      rw [key' x, hx']
    · intro hy
      have hy' : entrywiseAdjointAut Tag.E6 σ y = y := hy
      refine ⟨m.symm y, ?_, m.apply_symm_apply y⟩
      show f (m.symm y) = m.symm y
      apply m.injective
      rw [← key' (m.symm y), m.apply_symm_apply]
      exact hy'
  rw [gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup Tag.E6 σ] at hmap
  have hD : (ggFixDer f).map m.toMonoidHom =
      (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) := by
    unfold ggFixDer
    rw [Subgroup.map_commutator, hmap, fixE6_derived_fixed σ]
  have hJA : fixedFieldImage Tag.E6 σ ≤ adjointGroup Tag.E6 K := fun x hx =>
    (fixedFieldImage_le hx).1
  refine ⟨↥(fixSubfield σ), inferInstance, inferInstance, hcard, ?_⟩
  exact ⟨((Subgroup.equivMapOfInjective (ggFixDer f) m.toMonoidHom m.injective).trans
    (MulEquiv.subgroupCongr hD)).trans
    ((Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv (τ := Tag.E6) σ).symm)⟩

theorem fixE6all_fixGroup {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))}
    (hf : f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false))
    (hord : orderOf f = p) :
    p ∣ n ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
      Nonempty (↥(ggFixDer f) ≃* adjointGroup Tag.E6 k) := by
  refine ⟨dvd_of_chevField_order hn hK hp (LargeEvenChevH (LargeEvenCartanE 6) K false)
    (fun σ h hh => chevH_stable (LargeEvenCartanE 6) K false σ h hh) hf hord, ?_⟩
  have h := E6DerOn.of_eq (largeEvenIsRoot_eq_isRoot Tag.E6).symm
    (fixE6all_model hn hK hp.pos)
  suffices key : ∀ H : Subgroup (LargeEvenChevGL (LargeEvenCartanE 6) K),
      H = MarkChev.chevH (LargeEvenCartanE 6) (LargeEvenIsRoot (LargeEvenCartanE 6)) K false →
      ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (↥(ggFixDer f) ≃* adjointGroup Tag.E6 k) from
    key _ (largeEvenChevH_eq (LargeEvenCartanE 6) K false) f hf hord
  intro H hH
  subst hH
  exact h

theorem fixGapE6_holds : FixGapE6 := by
  intro n p K _ _ hn hK hp _ _ f hf hord
  obtain ⟨hpn, k, hkF, hkfin, hk, ⟨E⟩⟩ := fixE6all_fixGroup hn hK hp hf hord
  have hq := CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k
  haveI : Group.IsPerfect ↥(adjointGroup Tag.E6 k) := hq.1
  have hZ : Subgroup.center (adjointGroup Tag.E6 k) = ⊥ := center_adjointGroup_eq_bot
  refine ⟨hpn, LargeEvenCenterQuot (adjointGroup Tag.E6 k), inferInstance,
    (⟨.E6, 0, n / p⟩ : LargeEvenLabel), hq.2.1, hq.2.2,
    ⟨Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos, rfl⟩, rfl, ?_, ?_⟩
  · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
    obtain ⟨eC⟩ := centerQuot_chevGroup_equiv k Tag.E6
    exact ⟨k, hkF, hkfin, hk, ⟨eC.symm⟩⟩
  · exact ⟨E.trans (centerQuotEquivOfBot hZ).symm⟩

end E6All

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
