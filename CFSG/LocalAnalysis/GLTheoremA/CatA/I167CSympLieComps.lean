module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (LieFactorData SLFactorFacts SUFactorFacts SpFactorFacts
  SpFourTwoFacts)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (IsLieFactorOf components_of_orbit_family_lieFactor)
open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.RankThree.CentralLift CFSG.ClassicalGroups.UnitaryFlag

@[expose] def I167CSpFactor (p ℓ q : ℕ) (K : Type) [Field K] (X : Type) [inst : Group X] : Prop :=
  letI := inst
  (∃ (m j : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 2 ≤ m ∧ 1 ≤ j ∧ ringChar E = ℓ ∧
      Fintype.card E = q ^ j ∧ (m = 2 → 4 ≤ Fintype.card E) ∧ (m = 2 ∨ p ∣ Fintype.card E - 1) ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin m) E))
  ∨ (∃ (m j q' : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 3 ≤ m ∧ 1 ≤ j ∧
      ringChar E = ℓ ∧ q' = q ^ j ∧ Fintype.card E = q' ^ 2 ∧ (m, q') ≠ (3, 2) ∧
      Nonempty (X ≃* ↥(StatedSU m q' E)))
  ∨ (q = Nat.card K ∧ ringChar K = ℓ ∧ ∃ s : ℕ, 2 ≤ s ∧ (s, Nat.card K) ≠ (2, 2) ∧
      Nonempty (X ≃* StatedSp s K))
  ∨ (q = Nat.card K ∧ ringChar K = ℓ ∧ Nat.card K = 2 ∧
      Nonempty (X ≃* ↥(commutator (StatedSp 2 K))))

private theorem i167CS_commutator_le_self' {G : Type*} [Group G] (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

private theorem i167CS_map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

private theorem i167CS_range_eq_commutator_of_perfect {X B Ab : Type*} [Group X] [Group B]
    [CommGroup Ab] (θ : X →* B) (hX : commutator X = ⊤) (D : B →* Ab) (hD : D.ker ≤ θ.range) :
    θ.range = commutator B := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← hX, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · refine le_trans ?_ hD
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

private theorem i167CS_range_comp_eq_commutator {G : Type*} [Group G] {A : Subgroup G}
    {B X : Type*} [Group B] [Group X]
    (φ : A ≃* B) (θ : X →* B) (hθ : θ.range = commutator B) :
    (A.subtype.comp (φ.symm.toMonoidHom.comp θ)).range = ⁅A, A⁆ := by
  have h1 : (φ.symm.toMonoidHom.comp θ).range = commutator ↥A := by
    rw [MonoidHom.range_comp, hθ]
    exact i167CS_map_commutator_mulEquiv φ.symm
  rw [MonoidHom.range_comp, h1]
  exact Subgroup.map_subtype_commutator A

private theorem i167CS_not_isSolvable_of_isQuasisimple_commutator {G : Type*} [Group G]
    {H : Subgroup G} (hQ : CFSG.IsQuasisimple ↥⁅H, H⁆) : ¬ Group.IsSolvable ↥H := by
  intro hs
  haveI := hs
  have hle : ⁅H, H⁆ ≤ H := i167CS_commutator_le_self' H
  haveI : Group.IsSolvable ↥⁅H, H⁆ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥⁅H, H⁆ := hQ.1
  haveI : Nontrivial ↥⁅H, H⁆ := by
    obtain ⟨a, b, hab⟩ := hQ.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  exact Group.IsPerfect.not_isSolvable ↥⁅H, H⁆ inferInstance

private abbrev GoodOver (p : ℕ) (ℓ : ℕ) {r : ℕ} {K : Type} [Field K]
    (H : Subgroup (StatedSp r K)) : Prop :=
  IsLieFactorOf (fun X inst => by
    letI := inst
    exact LieFactorData ℓ X ∧ I167CSpFactor p ℓ (Nat.card K) K X) H

private theorem i167CS_isSolvable_sl_two_of_card_lt_four {E : Type} [Field E] [Fintype E]
    (h : Fintype.card E < 4) : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have hcard : Nat.card E = 2 ∨ Nat.card E = 3 := by
    have h2 : 1 < Fintype.card E := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) E →* _))
    Matrix.SpecialLinearGroup.toGL_injective

private theorem i167CS_four_le_card_of_equiv_sl_two {G : Type*} [Group G] {E : Type} [Field E]
    [Fintype E] {A : Subgroup G}
    (φ : A ≃* Matrix.SpecialLinearGroup (Fin 2) E) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    4 ≤ Fintype.card E := by
  by_contra hlt
  haveI := i167CS_isSolvable_sl_two_of_card_lt_four (not_le.1 hlt)
  exact i167CS_not_isSolvable_of_isQuasisimple_commutator hQ
    (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)

private theorem i167CS_ringChar_eq_two_of_card_eq_two {E : Type} [Field E] [Fintype E]
    (h2 : Fintype.card E = 2) : ringChar E = 2 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card E (ringChar E)
  have hdvd : ringChar E ∣ 2 := by
    have : ringChar E ∣ ringChar E ^ (n : ℕ) := dvd_pow_self _ n.ne_zero
    rwa [← hn, h2] at this
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd

private theorem i167CS_range_equiv_eq_commutator {X B : Type*} [Group X] [Group B] (e : X ≃* B)
    (hX : commutator X = ⊤) : e.toMonoidHom.range = commutator B := by
  rw [MonoidHom.range_eq_map, ← i167CS_map_commutator_mulEquiv e, hX]

private theorem i167CS_good_sp_one {p r : ℕ} {K : Type} [Field K] [Finite K]
    (hSL : SLFactorFacts) {A : Subgroup (StatedSp r K)} (φ : A ≃* StatedSp 1 K)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : GoodOver p (ringChar K) ⁅A, A⁆ := by
  classical
  haveI := Fintype.ofFinite K
  let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSp 1 K :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
  have h4 : 4 ≤ Fintype.card K := i167CS_four_le_card_of_equiv_sl_two (φ.trans e1.symm) hQ
  have hX := hSL K 2 le_rfl (fun _ => h4)
  have hfac : I167CSpFactor p (ringChar K) (Nat.card K) K
      (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine Or.inl ⟨2, 1, K, inferInstance, inferInstance, le_rfl, le_rfl, rfl, ?_, ?_,
      Or.inl rfl, ⟨MulEquiv.refl _⟩⟩
    · rw [Nat.card_eq_fintype_card, pow_one]
    · intro _
      exact h4
  refine ⟨Matrix.SpecialLinearGroup (Fin 2) K, inferInstance, inferInstance,
    A.subtype.comp (φ.symm.toMonoidHom.comp e1.toMonoidHom),
    Subtype.val_injective.comp (φ.symm.injective.comp e1.injective),
    i167CS_range_comp_eq_commutator φ _ (i167CS_range_equiv_eq_commutator e1 hX.perfect),
    ⟨hX, hfac⟩⟩

private theorem i167CS_good_sp_two_two {p r : ℕ} {K : Type} [Field K] [Fintype K]
    (hSp42 : SpFourTwoFacts) (hc2 : Fintype.card K = 2) {A : Subgroup (StatedSp r K)}
    (φ : A ≃* StatedSp 2 K) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    GoodOver p (ringChar K) ⁅A, A⁆ := by
  classical
  have hX := hSp42 K hc2
  have h2 : ringChar K = 2 := i167CS_ringChar_eq_two_of_card_eq_two hc2
  have hfac : I167CSpFactor p (ringChar K) (Nat.card K) K
      ↥(commutator ↥(StatedSp 2 K)) := by
    refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_, ⟨MulEquiv.refl _⟩⟩))
    rw [Nat.card_eq_fintype_card]
    exact hc2
  refine ⟨↥(commutator ↥(StatedSp 2 K)), inferInstance, inferInstance,
    A.subtype.comp (φ.symm.toMonoidHom.comp (commutator ↥(StatedSp 2 K)).subtype),
    Subtype.val_injective.comp (φ.symm.injective.comp Subtype.val_injective),
    i167CS_range_comp_eq_commutator φ _ (Subgroup.range_subtype _),
    ⟨h2 ▸ hX, hfac⟩⟩

private theorem i167CS_good_sp_generic {p r s : ℕ} {K : Type} [Field K] [Fintype K]
    (hSp : SpFactorFacts) (hs2 : 2 ≤ s) (hspecial : ¬ (s = 2 ∧ Fintype.card K = 2))
    {A : Subgroup (StatedSp r K)} (φ : A ≃* StatedSp s K)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : GoodOver p (ringChar K) ⁅A, A⁆ := by
  classical
  have hne : (s, Fintype.card K) ≠ (2, 2) := fun h =>
    hspecial ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hne' : (s, Nat.card K) ≠ (2, 2) := by
    rwa [Nat.card_eq_fintype_card]
  have hX := hSp K s hs2 hne
  have hθ : (MonoidHom.id ↥(StatedSp s K)).range = commutator ↥(StatedSp s K) := by
    rw [MonoidHom.range_eq_top.2 Function.surjective_id, hX.perfect]
  have hfac : I167CSpFactor p (ringChar K) (Nat.card K) K ↥(StatedSp s K) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, rfl, s, hs2, hne', ⟨MulEquiv.refl _⟩⟩))
  refine ⟨↥(StatedSp s K), inferInstance, inferInstance,
    A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.id _)),
    Subtype.val_injective.comp (φ.symm.injective.comp Function.injective_id),
    i167CS_range_comp_eq_commutator φ _ hθ, ⟨hX, hfac⟩⟩

private theorem i167CS_good_sp {p r : ℕ} {K : Type} [Field K] [Finite K] {ℓ : ℕ}
    (hKℓ : ringChar K = ℓ) (hSL : SLFactorFacts) (hSp : SpFactorFacts) (hSp42 : SpFourTwoFacts)
    {A : Subgroup (StatedSp r K)} {s : ℕ} (hs : 1 ≤ s) (φ : A ≃* StatedSp s K)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : GoodOver p ℓ ⁅A, A⁆ := by
  classical
  haveI := Fintype.ofFinite K
  subst hKℓ
  by_cases hs1 : s = 1
  · subst hs1
    exact i167CS_good_sp_one hSL φ hQ
  · have hs2 : 2 ≤ s := by omega
    by_cases hspecial : s = 2 ∧ Fintype.card K = 2
    · obtain ⟨rfl, hc2⟩ := hspecial
      exact i167CS_good_sp_two_two hSp42 hc2 φ hQ
    · exact i167CS_good_sp_generic hSp hs2 hspecial φ hQ

private theorem i167CS_isSolvable_gl_of_le_one {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
  refine Group.isSolvable_of_comm fun a b => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact Matrix.ext fun i => i.elim0
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact mul_comm _ _

private theorem i167CS_good_gl {p r : ℕ} {K : Type} [Field K] {ℓ : ℕ} {E : Type} [Field E]
    [Fintype E] {j : ℕ} (hEℓ : ringChar E = ℓ) (hj : 1 ≤ j)
    (hEc : Fintype.card E = Nat.card K ^ j) (hdvd : p ∣ Fintype.card E - 1)
    (h4 : 4 ≤ Fintype.card E) (hSL : SLFactorFacts) {m : ℕ} {A : Subgroup (StatedSp r K)}
    (φ : A ≃* Matrix.GeneralLinearGroup (Fin m) E) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    GoodOver p ℓ ⁅A, A⁆ := by
  classical
  have hm : 2 ≤ m := by
    by_contra hlt
    haveI := i167CS_isSolvable_gl_of_le_one (E := E) (not_le.1 hlt |> Nat.lt_succ_iff.1)
    exact i167CS_not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  have hX := hSL E m hm (fun _ => h4)
  let θ : Matrix.SpecialLinearGroup (Fin m) E →* Matrix.GeneralLinearGroup (Fin m) E :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin m) E) := by
    refine i167CS_range_eq_commutator_of_perfect θ hX.perfect
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin m) (Fin m) E).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  have hfac : I167CSpFactor p ℓ (Nat.card K) K (Matrix.SpecialLinearGroup (Fin m) E) :=
    Or.inl ⟨m, j, E, inferInstance, inferInstance, hm, hj, hEℓ, hEc, (fun _ => h4), Or.inr hdvd,
      ⟨MulEquiv.refl _⟩⟩
  refine ⟨Matrix.SpecialLinearGroup (Fin m) E, inferInstance, inferInstance,
    A.subtype.comp (φ.symm.toMonoidHom.comp θ),
    Subtype.val_injective.comp (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective),
    i167CS_range_comp_eq_commutator φ θ hθ, ⟨hEℓ ▸ hX, hfac⟩⟩

private theorem i167CS_card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem i167CS_isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_primeFactors_le_two (h ▸ i167CS_card_primeFactors_two_three a b ha hb)

private theorem i167CS_finite_generalLinearGroup {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have := hE.finite
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem i167CS_isSolvable_sesqUnitaryGroup_small_large {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft)
    (hsmall : Module.finrank E W ≤ 1 ∨ (¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)))) (hq2 : 2 ≤ ℓ ^ g)
    (hm : 2 ≤ Module.finrank E W) : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  haveI := i167CS_finite_generalLinearGroup hE (W := W)
  have hq : ¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)) := by
    rcases hsmall with h | h
    · omega
    · exact h
  obtain ⟨hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    rfl (by omega : 1 ≤ Module.finrank E W)
  have hexc : (Module.finrank E W = 2 ∧ ℓ ^ g = 2) ∨ (Module.finrank E W = 2 ∧ ℓ ^ g = 3) ∨
      (Module.finrank E W = 3 ∧ ℓ ^ g = 2) := by
    by_contra hn
    push Not at hn
    obtain ⟨h1, h2, h3⟩ := hn
    refine hq ⟨fun h2' => ?_, fun h3' => ?_⟩
    · by_contra hlt
      rcases (show ℓ ^ g = 2 ∨ ℓ ^ g = 3 by omega) with hQ | hQ
      · exact h1 h2' hQ
      · exact h2 h2' hQ
    · by_contra hlt
      exact h3 h3' (by omega)
  rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
  · rw [hm2, hQ] at hcard
    have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
    have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
    exact i167CS_isSolvable_of_card_two_three (a := 1) (b := 2) (by norm_num) (by norm_num)
      (by rw [h18]; norm_num)
  · rw [hm2, hQ] at hcard
    have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by decide +kernel
    have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by exact_mod_cast hcard.trans e
    exact i167CS_isSolvable_of_card_two_three (a := 5) (b := 1) (by norm_num) (by norm_num)
      (by rw [h96]; norm_num)
  · rw [hm3, hQ] at hcard
    have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
    have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
    exact i167CS_isSolvable_of_card_two_three (a := 3) (b := 4) (by norm_num) (by norm_num)
      (by rw [h648]; norm_num)

private theorem i167CS_isSolvable_sesqUnitaryGroup_small_comm {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm : ¬ 2 ≤ Module.finrank E W) :
    Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  haveI := i167CS_finite_generalLinearGroup hE (W := W)
  refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
  have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
    (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
    ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
  simpa [Subgroup.coe_mul, Units.val_mul] using this

private theorem i167CS_isSolvable_sesqUnitaryGroup_small {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft)
    (hsmall : Module.finrank E W ≤ 1 ∨ (¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)))) : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  have hq2 : 2 ≤ ℓ ^ g := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : g ≠ 0) hE.prime.one_lt
    omega
  by_cases hm : 2 ≤ Module.finrank E W
  · exact i167CS_isSolvable_sesqUnitaryGroup_small_large hE hHf hHfl hsmall hq2 hm
  · exact i167CS_isSolvable_sesqUnitaryGroup_small_comm hE hHf hHfl hm

private theorem i167CS_exists_range_of_special_equiv {ℓ g : ℕ} {G : Type*} [Group G] {E : Type}
    [Field E] (hE : UnitaryFieldData ℓ g E) {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm1 : 1 ≤ Module.finrank E V) {A : Subgroup G}
    (φ : A ≃* sesqUnitaryGroup Hf) {X : Type} [Group X] (hXp : commutator X = ⊤)
    (e : ↥(sesqSpecialUnitaryGroup Hf) ≃* X) :
    ∃ ψ : X →* G, Function.Injective ψ ∧ ψ.range = ⁅A, A⁆ := by
  obtain ⟨-, -, -, -, hker, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl hm1
  let θ : X →* ↥(sesqUnitaryGroup Hf) :=
    (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)).comp e.symm.toMonoidHom
  have hθi : Function.Injective θ :=
    (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le Hf)).comp e.symm.injective
  have hθ : θ.range = commutator ↥(sesqUnitaryGroup Hf) := by
    refine i167CS_range_eq_commutator_of_perfect θ hXp (CFSG.LinearGroups.unitaryDet Hf) fun u hu => ?_
    rw [hker] at hu
    exact ⟨e ⟨u, hu⟩, Subtype.ext (by simp [θ])⟩
  exact ⟨A.subtype.comp (φ.symm.toMonoidHom.comp θ),
    Subtype.val_injective.comp (φ.symm.injective.comp hθi), i167CS_range_comp_eq_commutator φ θ hθ⟩

private theorem i167CS_good_gu_two {p r : ℕ} {K : Type} [Field K] {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) [Fintype ↥hE.fixedField] {d : ℕ} (hd : 1 ≤ d) (hSL : SLFactorFacts)
    {V : Type}
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) {m : ℕ} (hfin : Module.finrank E V = m)
    (hm : 2 ≤ m) (hm3 : m < 3) (hFcard : Fintype.card ↥hE.fixedField = ℓ ^ g)
    (hq2 : m = 2 → 4 ≤ ℓ ^ g) (hFℓ : ringChar ↥hE.fixedField = ℓ)
    (hFq : Fintype.card ↥hE.fixedField = Nat.card K ^ d) {A : Subgroup (StatedSp r K)}
    (φ : A ≃* sesqUnitaryGroup Hf) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    GoodOver p ℓ ⁅A, A⁆ := by
  obtain rfl : m = 2 := by omega
  obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hfin
  have hX := hSL ↥hE.fixedField 2 le_rfl (fun _ => by rw [hFcard]; exact hq2 rfl)
  obtain ⟨ψ, hψi, hψ⟩ := i167CS_exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e
  have hX' : LieFactorData ℓ (Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField) := by
    rw [hFℓ] at hX
    exact hX
  have hfac : I167CSpFactor p ℓ (Nat.card K) K
      (Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField) :=
    Or.inl ⟨2, d, ↥hE.fixedField, inferInstance, inferInstance, le_rfl, hd, hFℓ, hFq,
      (fun _ => by rw [hFcard]; exact hq2 rfl), Or.inl rfl, ⟨MulEquiv.refl _⟩⟩
  refine ⟨Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField, inferInstance, inferInstance, ψ,
    hψi, hψ, ⟨hX', hfac⟩⟩

private theorem i167CS_good_gu_three {p r : ℕ} {K : Type} [Field K] {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) [Fintype E] [Fintype ↥hE.fixedField] {d : ℕ} (hd : 1 ≤ d)
    (hSU : SUFactorFacts) {V : Type}
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) {m : ℕ} (hfin : Module.finrank E V = m)
    (b : Module.Basis (Fin m) E V) (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0)
    (hEℓ : ringChar E = ℓ) (hEcard : Fintype.card E = (ℓ ^ g) ^ 2)
    (hFcard : Fintype.card ↥hE.fixedField = ℓ ^ g)
    (hFq : Fintype.card ↥hE.fixedField = Nat.card K ^ d) (hq3 : m = 3 → 3 ≤ ℓ ^ g)
    (hm3 : 3 ≤ m) {A : Subgroup (StatedSp r K)} (φ : A ≃* sesqUnitaryGroup Hf)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : GoodOver p ℓ ⁅A, A⁆ := by
  have hnq : (m, ℓ ^ g) ≠ (3, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    have := hq3 h1
    omega
  have hX := hSU E m (ℓ ^ g) hEcard hm3 hnq
  obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
    (G := (1 : Matrix (Fin m) (Fin m) E)) (fun i j => by rw [hb i j, Matrix.one_apply])
  have hSUeq : StatedSU m (ℓ ^ g) E = gramSU hE (1 : Matrix (Fin m) (Fin m) E) :=
    unitarySU_eq_gramSU hE m
  let e' : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSU m (ℓ ^ g) E) :=
    e.trans (MulEquiv.subgroupCongr hSUeq.symm)
  obtain ⟨ψ, hψi, hψ⟩ := i167CS_exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e'
  have hX' : LieFactorData ℓ ↥(StatedSU m (ℓ ^ g) E) := by
    rw [hEℓ] at hX
    exact hX
  have hq' : ℓ ^ g = Nat.card K ^ d := by
    rw [← hFcard, hFq]
  have hfac : I167CSpFactor p ℓ (Nat.card K) K ↥(StatedSU m (ℓ ^ g) E) :=
    Or.inr (Or.inl ⟨m, d, ℓ ^ g, E, inferInstance, inferInstance, hm3, hd, hEℓ, hq',
      hEcard, hnq, ⟨MulEquiv.refl _⟩⟩)
  exact ⟨↥(StatedSU m (ℓ ^ g) E), inferInstance, inferInstance, ψ, hψi, hψ, ⟨hX', hfac⟩⟩

private theorem i167CS_good_gu {p r : ℕ} {K : Type} [Field K] {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {f d : ℕ} (hK : Nat.card K = ℓ ^ f) (hd : 1 ≤ d)
    (hg : g = f * d) (hSL : SLFactorFacts) (hSU : SUFactorFacts) {V : Type}
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) {m : ℕ} (b : Module.Basis (Fin m) E V)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0) {A : Subgroup (StatedSp r K)}
    (φ : A ≃* sesqUnitaryGroup Hf) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    GoodOver p ℓ ⁅A, A⁆ := by
  classical
  have hfin : Module.finrank E V = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hsolv : ¬ (Module.finrank E V ≤ 1 ∨ ¬ ((Module.finrank E V = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E V = 3 → 3 ≤ ℓ ^ g))) := fun h => by
    haveI := i167CS_isSolvable_sesqUnitaryGroup_small hE hHf hHfl h
    exact i167CS_not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  rw [hfin] at hsolv
  push Not at hsolv
  obtain ⟨hm, hq2, hq3⟩ := hsolv
  haveI := hE.finite
  haveI := Fintype.ofFinite E
  haveI : Fact ℓ.Prime := ⟨hE.prime⟩
  haveI : CharP E ℓ := hE.charP
  have hEℓ : ringChar E = ℓ := ringChar.eq E ℓ
  have hEcard : Fintype.card E = (ℓ ^ g) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_eq_sq
  haveI : Finite ↥hE.fixedField := inferInstance
  haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
  have hFcard : Fintype.card ↥hE.fixedField = ℓ ^ g := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_fixedField
  haveI : CharP ↥hE.fixedField ℓ := charP_of_card_eq_prime_pow (f := g) hFcard
  have hFℓ : ringChar ↥hE.fixedField = ℓ := ringChar.eq _ ℓ
  have hFq : Fintype.card ↥hE.fixedField = Nat.card K ^ d := by
    rw [hFcard, hg, hK, pow_mul]
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · exact i167CS_good_gu_two hE hd hSL hHf hHfl hfin (by omega : 2 ≤ m) hm3 hFcard hq2 hFℓ hFq φ hQ
  · exact i167CS_good_gu_three hE hd hSU hHf hHfl hfin b hb hEℓ hEcard hFcard hFq hq3 hm3 φ hQ

private theorem i167CS_good_spSupported_fixed {r : ℕ} {K : Type} [Field K] [Finite K] {ℓ : ℕ}
    (hKℓ : ringChar K = ℓ) (hSL : SLFactorFacts) (hSp : SpFactorFacts) (hSp42 : SpFourTwoFacts)
    {f p : ℕ} {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks ℓ f p x a)
    (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X])}, spSupported x {(h : K[X])}⁆)
    (h1 : (h : K[X]) = X - 1) :
    GoodOver p ℓ ⁅spSupported x {(h : K[X])}, spSupported x {(h : K[X])}⁆ := by
  obtain ⟨h0, hm⟩ := h
  change h0 = X - 1 at h1
  subst h1
  obtain ⟨φ, -⟩ := blocks.fixedFactor hm
  have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
    (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
    (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
  have hs1 : 1 ≤ s := by
    have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
    omega
  exact i167CS_good_sp hKℓ hSL hSp hSp42 hs1 (φ.trans e) hQ

private theorem i167CS_good_spSupported_selfDual {r : ℕ} {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} (hK : Nat.card K = ℓ ^ f) (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks ℓ f p x a)
    (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X])}, spSupported x {(h : K[X])}⁆)
    (hself : reciprocalPolynomial (h : K[X]) = (h : K[X])) (h1 : (h : K[X]) ≠ X - 1) :
    GoodOver p ℓ ⁅spSupported x {(h : K[X])}, spSupported x {(h : K[X])}⁆ := by
  obtain ⟨d, hdeg, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ⟩ :=
    (blocks.selfDual h h1 hself).exists_half
  have hd : 1 ≤ d := by
    have hpos : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    omega
  exact i167CS_good_gu (f := f) (d := d) hE hK hd rfl hSL hSU hHf hHfl e he φ hQ

private theorem i167CS_good_spSupported_paired {r : ℕ} {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} (hp3 : 3 ≤ p) (hK : Nat.card K = ℓ ^ f) (hKℓ : ringChar K = ℓ)
    (hSL : SLFactorFacts) (hq : 2 ≤ ℓ ^ f) {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (blocks : SpPrimaryBlocks ℓ f p x a) (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆)
    (hself : ¬ (reciprocalPolynomial (h : K[X]) = (h : K[X]))) :
    GoodOver p ℓ ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ := by
  have hP := blocks.paired h (fun e => hself e.symm)
  obtain ⟨φ⟩ := hP.matrixFactor
  haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
  haveI := Fintype.ofFinite (AdjoinRoot (h : K[X]))
  have hEℓ : ringChar (AdjoinRoot (h : K[X])) = ℓ :=
    (Algebra.ringChar_eq K (AdjoinRoot (h : K[X]))).symm.trans hKℓ
  have hdeg : 1 ≤ (h : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
  have hEc : Fintype.card (AdjoinRoot (h : K[X])) = Nat.card K ^ (h : K[X]).natDegree := by
    rw [Fintype.card_eq_nat_card, hP.card_field, hK]
  have h4 : 4 ≤ Fintype.card (AdjoinRoot (h : K[X])) := by
    have hN : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
    have hle := Nat.le_of_dvd (by omega) hP.dvd
    rw [Fintype.card_eq_nat_card, hP.card_field]
    omega
  have hdvd : p ∣ Fintype.card (AdjoinRoot (h : K[X])) - 1 := by
    rw [Fintype.card_eq_nat_card, hP.card_field]
    exact hP.dvd
  exact i167CS_good_gl (j := (h : K[X]).natDegree) hEℓ hdeg hEc hdvd h4 hSL φ hQ

private theorem i167CS_good_spSupported_of_factor {r : ℕ} {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} (hp3 : 3 ≤ p) (hK : Nat.card K = ℓ ^ f)
    (hKℓ : ringChar K = ℓ) (hSL : SLFactorFacts) (hSU : SUFactorFacts) (hSp : SpFactorFacts)
    (hSp42 : SpFourTwoFacts) (hq : 2 ≤ ℓ ^ f) {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks ℓ f p x a)
    (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆) :
    GoodOver p ℓ ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ := by
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO] at hQ ⊢
    by_cases h1 : (h : K[X]) = X - 1
    · exact i167CS_good_spSupported_fixed hKℓ hSL hSp hSp42 hsq blocks h hQ h1
    · exact i167CS_good_spSupported_selfDual hK hSL hSU blocks h hQ hself h1
  · exact i167CS_good_spSupported_paired hp3 hK hKℓ hSL hq blocks h hQ hself

private theorem i167CS_tame_statedSp {s : ℕ} (hs : 1 ≤ s) {K : Type} [Field K] [Finite K] :
    CFSG.IsQuasisimple ↥(commutator (StatedSp s K)) ∨ Group.IsSolvable (StatedSp s K) := by
  by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
      (Nat.card K = 2 ∧ 3 ≤ s)
  · left
    have h := CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hq
    have h1 : commutator (StatedSp s K) = ⊤ := Group.isPerfect_def.mp h.1
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr h1).trans Subgroup.topEquiv).symm h
  · have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
    have hK4 : Nat.card K < 4 := by
      by_contra h
      exact hq (Or.inl (Or.inr (by omega)))
    have h3 : Nat.card K = 3 → s < 2 := fun h => by
      by_contra h'
      exact hq (Or.inr (Or.inl ⟨h, by omega⟩))
    have h2 : Nat.card K = 2 → s < 3 := fun h => by
      by_contra h'
      exact hq (Or.inr (Or.inr ⟨h, by omega⟩))
    have hcard := SymplecticFlag.card_statedSp (K := K) s
    rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with hK | hK
    · rcases (show s = 1 ∨ s = 2 by have := h2 hK; omega) with rfl | rfl
      · right
        refine i167CS_isSolvable_of_card_two_three (a := 1) (b := 1) (by norm_num) (by norm_num) ?_
        rw [hcard, hK]
        norm_num [Finset.Icc_self]
      · left
        have hd : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
        obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK
          (CFSG.RankThree.Classical.spForm_isAlt (r := 2) (K := K))
          (CFSG.RankThree.Classical.spForm_nondegenerate (r := 2) (K := K)) hd
        let e₀ : StatedSp 2 K ≃* sesqUnitaryGroup (CFSG.RankThree.Classical.spForm 2 K) :=
          (MonoidHom.ofInjective
            (CFSG.RankThree.Classical.spLin_injective (r := 2) (K := K))).trans
            (MulEquiv.subgroupCongr (CFSG.RankThree.Classical.range_spLin (r := 2) (K := K)))
        exact (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e₀.trans E)).1
    · have hs1 : s = 1 := by have := h3 hK; omega
      subst hs1
      right
      refine i167CS_isSolvable_of_card_two_three (a := 3) (b := 1) (by norm_num) (by norm_num) ?_
      rw [hcard, hK]
      norm_num [Finset.Icc_self]

private theorem i167CS_tame_top_statedSp {r : ℕ} (hr : 1 ≤ r) {K : Type} [Field K] [Finite K] :
    CFSG.IsQuasisimple ↥⁅(⊤ : Subgroup ↥(StatedSp r K)), (⊤ : Subgroup ↥(StatedSp r K))⁆ ∨
      Group.IsSolvable ↥(⊤ : Subgroup ↥(StatedSp r K)) := by
  rcases i167CS_tame_statedSp (s := r) (K := K) hr with h | h
  · left
    rw [← _root_.commutator_def]
    exact h
  · right
    let e : ↥(StatedSp r K) ≃* ↥(⊤ : Subgroup ↥(StatedSp r K)) := Subgroup.topEquiv.symm
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

private theorem i167CS_lieComps_one {p r : ℕ} {K : Type} [Field K] [Finite K]
    (hKℓ : ringChar K = 2) (hSL : SLFactorFacts) (hSp : SpFactorFacts) (hSp42 : SpFourTwoFacts)
    (hr : 1 ≤ r) (x : StatedSp r K) (hx1 : x = 1) :
    ∀ K' : Subgroup (StatedProj (StatedSp r K)),
      IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) →
      ∃ (X : Type) (inst : Group X) (_ : Finite X), LieFactorData 2 X ∧
        I167CSpFactor p 2 (Nat.card K) K X ∧
        (∃ g : X →* ↥K', Function.Surjective g ∧ g.ker ≤ Subgroup.center X) := by
  subst hx1
  intro K' hK'
  obtain ⟨X, inst, hfin, ⟨hX, hfac⟩, hf'⟩ :=
    components_of_orbit_family_lieFactor (r := r) 1
      (fun _ : Unit => (⊤ : Subgroup (StatedSp r K)))
      (fun i j hij => absurd (Subsingleton.elim i j) hij)
      (by ext g; simp [Subgroup.mem_centralizer_iff]) (fun _ => i167CS_tame_top_statedSp hr)
      (fun _ hQ => i167CS_good_sp hKℓ hSL hSp hSp42 hr Subgroup.topEquiv hQ) K' hK'
  exact ⟨X, inst, hfin, hX, hfac, hf'⟩

private theorem i167CS_lieComps_ne {p r f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hSL : SLFactorFacts) (hSU : SUFactorFacts) (hSp : SpFactorFacts) (hSp42 : SpFourTwoFacts)
    (hr : 1 ≤ r) (hKℓ : ringChar K = 2) (x : StatedSp r K) (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    ∀ K' : Subgroup (StatedProj (StatedSp r K)),
      IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) →
      ∃ (X : Type) (inst : Group X) (_ : Finite X), LieFactorData 2 X ∧
        I167CSpFactor p 2 (Nat.card K) K X ∧
        (∃ g : X →* ↥K', Function.Surjective g ∧ g.ker ≤ Subgroup.center X) := by
  haveI := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq : 2 ≤ 2 ^ f := Nat.prime_two.two_le.trans (Nat.le_self_pow (by omega) 2)
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) p := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
    hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
      (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp) (by rw [h, map_one]))
  have ha : orderOf (SymplecticFlag.proj r K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = p := orderOf_eq_prime hx hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK hp hp2 hp2 hr _ ha).2 x rfl hxp
  have hpK : (p : K) ≠ 0 := fun h => by
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  intro K' hK'
  obtain ⟨X, inst, hfin, ⟨hX, hfac⟩, hf'⟩ :=
    components_of_orbit_family_lieFactor x
      (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin (fun O =>
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
          hp3 hq hsq blocks O)
      (fun O hQ => by
        obtain ⟨O, h, hh, rfl⟩ := O
        exact i167CS_good_spSupported_of_factor hp3 hK hKℓ hSL hSU hSp hSp42 hq hsq blocks ⟨h, hh⟩ hQ) K' hK'
  exact ⟨X, inst, hfin, hX, hfac, hf'⟩

theorem i167CS_lieComps (hSL : SLFactorFacts) (hSU : SUFactorFacts) (hSp : SpFactorFacts)
    (hSp42 : SpFourTwoFacts) {p r f : ℕ} {K : Type} [Field K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r)
    (x : StatedSp r K) (hx : x ^ p = 1) :
    ∀ K' : Subgroup (StatedProj (StatedSp r K)),
      IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) →
      ∃ (X : Type) (inst : Group X) (_ : Finite X), LieFactorData 2 X ∧
        I167CSpFactor p 2 (Nat.card K) K X ∧
        (∃ g : X →* ↥K', Function.Surjective g ∧ g.ker ≤ Subgroup.center X) := by
  classical
  have hq0 : 2 ^ f ≠ 0 := pow_ne_zero f Nat.prime_two.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f) hcardK
  have hKℓ : ringChar K = 2 := ringChar.eq K 2
  by_cases hx1 : x = 1
  · exact i167CS_lieComps_one hKℓ hSL hSp hSp42 hr x hx1
  · exact i167CS_lieComps_ne hp hp2 hf hK hSL hSU hSp hSp42 hr hKℓ x hx hx1

end CFSG.LocalAnalysis.GLTheoremA.I167

end
