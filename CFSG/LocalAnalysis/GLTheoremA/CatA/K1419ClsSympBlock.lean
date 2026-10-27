module

import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsSympCent
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsRank
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial

private theorem commutator_le_self' {G : Type*} [Group G] (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

section Generic

variable {G : Type*} [Group G]

private theorem map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

private theorem range_eq_commutator_of_perfect {X B Ab : Type*} [Group X] [Group B]
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

private theorem range_comp_eq_commutator {A : Subgroup G} {B X : Type*} [Group B] [Group X]
    (φ : A ≃* B) (θ : X →* B) (hθ : θ.range = commutator B) :
    (A.subtype.comp (φ.symm.toMonoidHom.comp θ)).range = ⁅A, A⁆ := by
  have h1 : (φ.symm.toMonoidHom.comp θ).range = commutator ↥A := by
    rw [MonoidHom.range_comp, hθ]
    exact map_commutator_mulEquiv φ.symm
  rw [MonoidHom.range_comp, h1]
  exact Subgroup.map_subtype_commutator A

private theorem not_isSolvable_of_isQuasisimple_commutator {H : Subgroup G}
    (hQ : CFSG.IsQuasisimple ↥⁅H, H⁆) : ¬ Group.IsSolvable ↥H := by
  intro hs
  haveI := hs
  have hle : ⁅H, H⁆ ≤ H := commutator_le_self' H
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

end Generic
section SpFactor

variable {G : Type*} [Group G]

private theorem isSolvable_sl_two_of_card_lt_four {E : Type} [Field E] [Fintype E]
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

private theorem four_le_card_of_equiv_sl_two {E : Type} [Field E] [Fintype E] {A : Subgroup G}
    (φ : A ≃* Matrix.SpecialLinearGroup (Fin 2) E) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    4 ≤ Fintype.card E := by
  by_contra hlt
  haveI := isSolvable_sl_two_of_card_lt_four (not_le.1 hlt)
  exact not_isSolvable_of_isQuasisimple_commutator hQ
    (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)

private theorem range_equiv_eq_commutator {X B : Type*} [Group X] [Group B] (e : X ≃* B)
    (hX : commutator X = ⊤) : e.toMonoidHom.range = commutator B := by
  rw [MonoidHom.range_eq_map, ← map_commutator_mulEquiv e, hX]

end SpFactor

section GLFactor

variable {G : Type*} [Group G]

private theorem isSolvable_gl_of_le_one {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
  refine Group.isSolvable_of_comm fun a b => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact Matrix.ext fun i => i.elim0
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact mul_comm _ _

end GLFactor

section GUFactor

private theorem card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_primeFactors_le_two (h ▸ card_primeFactors_two_three a b ha hb)

private theorem finite_generalLinearGroup {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have := hE.finite
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem isSolvable_sesqUnitaryGroup_of_small {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft)
    (hsmall : Module.finrank E W ≤ 1 ∨ (¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)))) : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  have hq2 : 2 ≤ ℓ ^ g := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : g ≠ 0) hE.prime.one_lt
    omega
  haveI := finite_generalLinearGroup hE (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · have hq : ¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)) := by
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
      exact isSolvable_of_card_two_three (a := 1) (b := 2) (by norm_num) (by norm_num)
        (by rw [h18]; norm_num)
    · rw [hm2, hQ] at hcard
      have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by decide +kernel
      have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by exact_mod_cast hcard.trans e
      exact isSolvable_of_card_two_three (a := 5) (b := 1) (by norm_num) (by norm_num)
        (by rw [h96]; norm_num)
    · rw [hm3, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
      have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
      exact isSolvable_of_card_two_three (a := 3) (b := 4) (by norm_num) (by norm_num)
        (by rw [h648]; norm_num)
  · refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

end GUFactor

section TopTame

private theorem tame_statedSp {s : ℕ} (hs : 1 ≤ s) {K : Type} [Field K] [Finite K] :
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
        refine isSolvable_of_card_two_three (a := 1) (b := 1) (by norm_num) (by norm_num) ?_
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
      refine isSolvable_of_card_two_three (a := 3) (b := 1) (by norm_num) (by norm_num) ?_
      rw [hcard, hK]
      norm_num [Finset.Icc_self]

end TopTame

private theorem commutator_equiv_statedSp {s r : ℕ} {K : Type} [Field K] [Finite K]
    {A : Subgroup (StatedSp r K)} (φ : A ≃* StatedSp s K) :
    Nonempty (↥(commutator ↥A) ≃* ↥(commutator (StatedSp s K))) := by
  refine ⟨(Subgroup.equivMapOfInjective (commutator ↥A) φ φ.injective).trans
    (MulEquiv.subgroupCongr ?_)⟩
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
    MonoidHom.range_eq_top.2 φ.surjective, ← commutator_def]

private theorem tame_of_mulEquiv_statedSp {s : ℕ} (hs : 1 ≤ s) {r : ℕ} {K : Type} [Field K]
    [Finite K] {A : Subgroup (StatedSp r K)} (φ : A ≃* StatedSp s K) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A := by
  rcases tame_statedSp (s := s) (K := K) hs with h | h
  · left
    obtain ⟨e1⟩ := commutator_equiv_statedSp φ
    have h2 : CFSG.IsQuasisimple ↥(commutator ↥A) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm h
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))) h2
  · right
    exact Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective

private theorem tame_of_mulEquiv_gl {r R : ℕ} {K : Type} [Field K] [Finite K]
    {A : Subgroup (StatedSp R K)} (φ : A ≃* Matrix.GeneralLinearGroup (Fin r) K) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A := by
  classical
  haveI := Fintype.ofFinite K
  rcases Nat.lt_or_ge r 2 with hr | hr
  · right
    haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin r) K) :=
      isSolvable_gl_of_le_one (by omega)
    exact Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  · by_cases hsmall : r = 2 ∧ Nat.card K ≤ 3
    · right
      obtain ⟨rfl, hK3⟩ := hsmall
      have hcard : Nat.card K = 2 ∨ Nat.card K = 3 := by
        have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
        omega
      haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K hcard
      exact Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    · left
      have hcond : 3 ≤ r ∨ ∃ s : Finset K, s.card = 4 := by
        rcases Nat.lt_or_ge r 3 with h3 | h3
        · have hr2 : r = 2 := by omega
          subst hr2
          right
          have h4 : 4 ≤ Nat.card K := by
            have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
            by_contra hcon
            exact hsmall ⟨rfl, by omega⟩
          have h4' : 4 ≤ (Finset.univ : Finset K).card := by
            simpa [Nat.card_eq_fintype_card] using h4
          obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4'
          exact ⟨s, hs⟩
        · exact Or.inl h3
      have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin r) K) :=
        CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hr hcond
      have hperf : commutator (Matrix.SpecialLinearGroup (Fin r) K) = ⊤ :=
        Group.isPerfect_def.mp hqSL.1
      let θ : Matrix.SpecialLinearGroup (Fin r) K →* Matrix.GeneralLinearGroup (Fin r) K :=
        Matrix.SpecialLinearGroup.toGL
      have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin r) K) := by
        refine range_eq_commutator_of_perfect θ hperf
          (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin r) K →* Kˣ) fun g hg => ?_
        rw [MonoidHom.mem_ker] at hg
        have hdet : (g : Matrix (Fin r) (Fin r) K).det = 1 := by
          have := congrArg Units.val hg
          simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
        exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
      let ψ : Matrix.SpecialLinearGroup (Fin r) K →* StatedSp R K :=
        A.subtype.comp (φ.symm.toMonoidHom.comp θ)
      have hψi : Function.Injective ψ :=
        Subtype.val_injective.comp (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective)
      have hψr : ψ.range = ⁅A, A⁆ := range_comp_eq_commutator φ θ hθ
      have eM : ↥⁅A, A⁆ ≃* Matrix.SpecialLinearGroup (Fin r) K :=
        ((Subgroup.equivMapOfInjective (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin r) K))
            ψ hψi).trans (MulEquiv.subgroupCongr (by rw [Subgroup.map_top, hψr]))).symm.trans
          Subgroup.topEquiv
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eM.symm hqSL

private theorem tame_of_mulEquiv_heldGU {r n : ℕ} {K E : Type} [Field K] [Finite K]
    [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hEc : Nat.card E = Nat.card K ^ 2) (hτQ : ∀ y, τ y = y ^ Nat.card K)
    {R : ℕ} {A : Subgroup (StatedSp R K)} (φ : A ≃* heldGU r E τ hτ) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A := by
  classical
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite E
  have hE : UnitaryFieldData 2 n E :=
    { prime := Nat.prime_two
      one_le := hn
      card := by
        rw [hEc, hK, ← pow_mul, show n * 2 = 2 * n by omega] }
  let ρE : E ≃+* E :=
    { toFun := hE.bar, invFun := hE.bar, left_inv := hE.bar_bar, right_inv := hE.bar_bar,
      map_mul' := hE.bar.map_mul, map_add' := hE.bar.map_add }
  have hρE : ∀ y, ρE (ρE y) = y := hE.bar_bar
  have hτbar : τ = ρE := by
    refine RingEquiv.ext fun y => ?_
    rw [hτQ y, hK]
    change y ^ 2 ^ n = hE.bar y
    rw [hE.bar_apply]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := hE.charP
  let B : (Fin r → E) →ₛₗ[hE.bar] (Fin r → E) →ₗ[E] E :=
    CFSG.LinearGroups.stdHermForm hE r
  have hB : B.IsSymm := CFSG.LinearGroups.stdHermForm_isSymm hE r
  have hBl : B.SeparatingLeft := CFSG.LinearGroups.stdHermForm_separatingLeft hE r
  let b : Module.Basis (Fin r) E (Fin r → E) := Pi.basisFun E (Fin r)
  have hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    change (CFSG.LinearGroups.stdHermForm hE r (b i)) (b j) = if i = j then 1 else 0
    rw [CFSG.LinearGroups.stdHermForm_apply]
    by_cases h : i = j <;> simp [b, Pi.basisFun_apply, Pi.single_apply, h, eq_comm]
  obtain ⟨eU⟩ := CFSG.LieType.SemisimpleCentralizers.HeldUCD.nonempty_mulEquiv_heldGU
    ρE hρE B b hb
  have eG : heldGU r E τ hτ ≃* heldGU r E ρE hρE := by
    have h : (heldGU r E τ hτ : Subgroup (GL (Fin r) E)) = heldGU r E ρE hρE := by
      subst hτbar
      rfl
    exact MulEquiv.subgroupCongr h
  let φU : A ≃* sesqUnitaryGroup B := (φ.trans eG).trans eU.symm
  have hfind : Module.finrank E (Fin r → E) = r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  by_cases hsmall : Module.finrank E (Fin r → E) ≤ 1 ∨
      ¬ ((Module.finrank E (Fin r → E) = 2 → 4 ≤ 2 ^ n) ∧
        (Module.finrank E (Fin r → E) = 3 → 3 ≤ 2 ^ n))
  · right
    haveI : Group.IsSolvable ↥(sesqUnitaryGroup B) :=
      isSolvable_sesqUnitaryGroup_of_small hE hB hBl hsmall
    exact Group.isSolvable_of_surjective (f := φU.symm.toMonoidHom) φU.symm.surjective
  · left
    have hnot1 : ¬ Module.finrank E (Fin r → E) ≤ 1 := fun h => hsmall (Or.inl h)
    have hq : (Module.finrank E (Fin r → E) = 2 → 4 ≤ 2 ^ n) ∧
        (Module.finrank E (Fin r → E) = 3 → 3 ≤ 2 ^ n) := by
      by_contra hc
      exact hsmall (Or.inr hc)
    rw [hfind] at hnot1
    have hm : 2 ≤ r := by omega
    have hqSL : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup B) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
        hE hB hBl (by rw [hfind]; exact hm) hq
    have hker : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitarySpecial (h := hE) B =
        (sesqSpecialUnitaryGroup B).subgroupOf (sesqUnitaryGroup B) := by
      ext δ
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_unitarySpecial (h := hE),
        Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
      exact ⟨fun h => ⟨δ.2, h⟩, fun h => h.2⟩
    have hle : ⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ ≤ sesqSpecialUnitaryGroup B := by
      rw [← Subgroup.map_subtype_commutator (sesqUnitaryGroup B)]
      refine Subgroup.map_le_iff_le_comap.2 ?_
      rw [Subgroup.comap_subtype, ← hker]
      exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.commutator_le_unitarySpecial (h := hE) B
    have hss_eq : (sesqSpecialUnitaryGroup B) =
        ⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ := by
      refine le_antisymm ?_ hle
      have hperf : ⁅(sesqSpecialUnitaryGroup B), (sesqSpecialUnitaryGroup B)⁆ =
          sesqSpecialUnitaryGroup B := Subgroup.isPerfect_iff.mp hqSL.1
      rw [← hperf]
      exact Subgroup.commutator_mono (sesqSpecialUnitaryGroup_le B) (sesqSpecialUnitaryGroup_le B)
    have hqU : CFSG.IsQuasisimple ↥⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hss_eq) hqSL
    obtain ⟨ecom⟩ : Nonempty (↥(commutator ↥A) ≃*
        ↥(commutator ↥(sesqUnitaryGroup B))) := by
      refine ⟨(Subgroup.equivMapOfInjective (commutator ↥A) φU φU.injective).trans
        (MulEquiv.subgroupCongr ?_)⟩
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.2 φU.surjective, ← commutator_def]
    have e1 : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
      (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
    have e2 : ↥(commutator ↥(sesqUnitaryGroup B)) ≃*
        ↥⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ :=
      (Subgroup.equivMapOfInjective (commutator ↥(sesqUnitaryGroup B))
        (sesqUnitaryGroup B).subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr
          (Subgroup.map_subtype_commutator (sesqUnitaryGroup B)))
    have eAU : ↥⁅A, A⁆ ≃* ↥⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ :=
      e1.symm.trans (ecom.trans e2)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eAU.symm hqU

private theorem equiv_of_range {G X : Type} [Group G] [Group X] {A : Subgroup G}
    (ψ : X →* G) (hψ : Function.Injective ψ) (h : ψ.range = A) :
    Nonempty (↥A ≃* X) :=
  ⟨((Subgroup.equivMapOfInjective (⊤ : Subgroup X) ψ hψ).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.map_top, h]))).symm.trans Subgroup.topEquiv⟩

private theorem centerQuot_equiv_pSimple_of_component {S : Type} [Group S] [Finite S]
    {X J : Subgroup S} (hJ : GLAPComponent 3 X J) (hcomp : CFSG.Open.IsComponentOf J X) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* PSimple 3 J) := by
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hO : GLAPPrimeCore 3 ↥J ≤ Subgroup.center ↥J := by
    by_cases htop : GLAPPrimeCore 3 ↥J = ⊤
    · exfalso
      haveI := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hq
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _))
    · exact CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hcomp.2.2
        inferInstance htop
  let π : ↥J →* PQuot 3 J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    exact hO
  exact nonempty_centralQuotient_mulEquiv hcomp.2.2.1 π hπ hπk

private theorem commutator_gl_eq_statedSL {r : ℕ} {K : Type} [Field K] [Finite K]
    (hr : 2 ≤ r) (hcond : 3 ≤ r ∨ ∃ s : Finset K, s.card = 4) :
    ⁅(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin r) K)),
      (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin r) K))⁆ = StatedSL r K := by
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin r) K) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hr hcond
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin r) K) = ⊤ :=
    Group.isPerfect_def.mp hqSL.1
  let θ : Matrix.SpecialLinearGroup (Fin r) K →* Matrix.GeneralLinearGroup (Fin r) K :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin r) K) := by
    refine range_eq_commutator_of_perfect θ hperf
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin r) K →* Kˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin r) (Fin r) K).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  rw [← commutator_def, ← hθ, ← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]

private theorem heldGU_center_scalar {r n : ℕ} {E : Type} [Field E] [Finite E]
    (hE : UnitaryFieldData 2 n E) (hr : 2 ≤ r)
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y} (hτb : (τ : E →+* E) = hE.bar)
    {A : ↥(heldGU r E τ hτ)}
    (hA : A ∈ Subgroup.center ↥(heldGU r E τ hτ)) :
    ∃ c : E, ((A : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = c • 1 := by
  have hq : 2 ≤ 2 ^ n := by
    have := hE.one_le
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
  have hρf : (τ : E → E) = ⇑hE.bar := congrArg (fun f : E →+* E => (f : E → E)) hτb
  refine CFSG.RankThree.PartOne.KCUnitary.exists_smul_one_of_commute_gramSU hE hr hq ?_
  intro B hB
  have hBGU : B ∈ heldGU r E τ hτ := by
    obtain ⟨h1, -⟩ := CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU.mp hB
    show Matrix.transpose ((B : Matrix (Fin r) (Fin r) E).map (τ : E → E)) *
      (B : Matrix (Fin r) (Fin r) E) = 1
    rw [hρf]
    simpa using h1
  have hcomm : (B : Matrix (Fin r) (Fin r) E) *
        ((A : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      ((A : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
        (B : Matrix (Fin r) (Fin r) E) := by
    have h := Subgroup.mem_center_iff.mp hA ⟨B, hBGU⟩
    exact congrArg Units.val (Subtype.ext_iff.mp h)
  exact hcomm

private theorem mem_commutator_iff_map {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {x : G} : x ∈ commutator G ↔ e x ∈ commutator H := by
  have h : (commutator G).map e.toMonoidHom = commutator H := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 e.surjective, ← commutator_def]
  constructor
  · intro hx
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hx
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    rwa [e.injective hyx] at hy

private theorem mem_commutator_subtype_iff {G : Type} [Group G] {A : Subgroup G} {x : G}
    (hx : x ∈ A) : x ∈ ⁅A, A⁆ ↔ (⟨x, hx⟩ : ↥A) ∈ commutator ↥A := by
  have hmap := Subgroup.map_subtype_commutator A
  constructor
  · intro h
    rw [← hmap] at h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
    have hy' : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [hy'] at hy
  · intro h
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ h

private theorem spFactor_cases {s r : ℕ} {K : Type} [Field K] [Finite K]
    {A : Subgroup (StatedSp r K)} (hs : 1 ≤ s) (φ : A ≃* StatedSp s K)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    (s = 1 ∧ 4 ≤ Nat.card K ∧ Nonempty (↥⁅A, A⁆ ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∨
    (2 ≤ s ∧ ¬ (s = 2 ∧ Nat.card K = 2) ∧ Nonempty (↥⁅A, A⁆ ≃* StatedSp s K)) ∨
    (s = 2 ∧ Nat.card K = 2 ∧
      Nonempty (↥⁅A, A⁆ ≃* ↥(commutator (StatedSp 2 K)))) := by
  classical
  haveI := Fintype.ofFinite K
  by_cases hs1 : s = 1
  · subst hs1
    left
    let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSp 1 K :=
      CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
    have h4f : 4 ≤ Fintype.card K := four_le_card_of_equiv_sl_two (φ.trans e1.symm) hQ
    have h4 : 4 ≤ Nat.card K := by rwa [Nat.card_eq_fintype_card]
    have hX := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds K 2 le_rfl
      (fun _ => h4f)
    let θ : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 1 K := e1.toMonoidHom
    have hθ : θ.range = commutator (StatedSp 1 K) := range_equiv_eq_commutator e1 hX.perfect
    let ψ : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K :=
      A.subtype.comp (φ.symm.toMonoidHom.comp θ)
    have hψi : Function.Injective ψ :=
      Subtype.val_injective.comp (φ.symm.injective.comp e1.injective)
    have hψr : ψ.range = ⁅A, A⁆ := range_comp_eq_commutator φ θ hθ
    exact ⟨rfl, h4, equiv_of_range ψ hψi hψr⟩
  · have hs2 : 2 ≤ s := by omega
    by_cases hspecial : s = 2 ∧ Nat.card K = 2
    · right; right
      obtain ⟨rfl, hK2⟩ := hspecial
      have hX := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds K
        (by simpa [Nat.card_eq_fintype_card] using hK2)
      have hθ : (commutator (StatedSp 2 K)).subtype.range =
          commutator (StatedSp 2 K) := Subgroup.range_subtype _
      let ψ : ↥(commutator (StatedSp 2 K)) →* StatedSp r K :=
        A.subtype.comp (φ.symm.toMonoidHom.comp (commutator (StatedSp 2 K)).subtype)
      have hψi : Function.Injective ψ :=
        Subtype.val_injective.comp (φ.symm.injective.comp Subtype.val_injective)
      have hψr : ψ.range = ⁅A, A⁆ := range_comp_eq_commutator φ _ hθ
      exact ⟨rfl, hK2, equiv_of_range ψ hψi hψr⟩
    · right; left
      refine ⟨hs2, hspecial, ?_⟩
      have hne : (s, Nat.card K) ≠ (2, 2) := fun h =>
        hspecial ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      have hne' : (s, Fintype.card K) ≠ (2, 2) := by simpa [Nat.card_eq_fintype_card] using hne
      have hX := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds K s hs2 hne'
      have hθ : (MonoidHom.id (StatedSp s K)).range = commutator (StatedSp s K) := by
        rw [MonoidHom.range_eq_top.2 Function.surjective_id, hX.perfect]
      let ψ : StatedSp s K →* StatedSp r K :=
        A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.id _))
      have hψi : Function.Injective ψ :=
        Subtype.val_injective.comp (φ.symm.injective.comp Function.injective_id)
      have hψr : ψ.range = ⁅A, A⁆ := range_comp_eq_commutator φ _ hθ
      exact equiv_of_range ψ hψi hψr

section SBZGeneric

private noncomputable def sbz_supMulEquiv {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) :
    ↥P × ↥Q ≃* ↥(P ⊔ Q) := by
  let f : ↥P × ↥Q →* G :=
    { toFun := fun z => (z.1 : G) * (z.2 : G)
      map_one' := by simp
      map_mul' := fun x y => by
        have h : ((y.1 : G) * (x.2 : G)) = (x.2 : G) * (y.1 : G) :=
          hcomm y.1 y.1.2 x.2 x.2.2
        calc ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))
            = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by rw [h]
          _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by group }
  let g : ↥P × ↥Q →* ↥(P ⊔ Q) := f.codRestrict (P ⊔ Q)
    (fun z => Subgroup.mul_mem_sup z.1.2 z.2.2)
  have hg : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have h : (x.1 : G) * (x.2 : G) = (y.1 : G) * (y.2 : G) := congrArg Subtype.val hxy
      have hmem : ((x.1 : G))⁻¹ * (y.1 : G) = (x.2 : G) * ((y.2 : G))⁻¹ := by
        have h' := congrArg (fun z : G => ((x.1 : G))⁻¹ * z * ((y.2 : G))⁻¹) h
        simpa [mul_assoc] using h'.symm
      have h1 : ((x.1 : G))⁻¹ * (y.1 : G) ∈ P := P.mul_mem (P.inv_mem x.1.2) y.1.2
      have h2 : (x.2 : G) * ((y.2 : G))⁻¹ ∈ Q := Q.mul_mem x.2.2 (Q.inv_mem y.2.2)
      have hbot : ((x.1 : G))⁻¹ * (y.1 : G) ∈ P ⊓ Q := ⟨h1, hmem ▸ h2⟩
      rw [hdisj, Subgroup.mem_bot] at hbot
      have hxy1 : (x.1 : G) = y.1 := by
        have := congrArg (fun z : G => (x.1 : G) * z) hbot
        simpa [mul_assoc] using this.symm
      have hxy2 : (x.2 : G) = y.2 := by
        have h' : (y.1 : G) * (x.2 : G) = (y.1 : G) * (y.2 : G) := by
          calc (y.1 : G) * (x.2 : G) = (x.1 : G) * (x.2 : G) := by rw [hxy1]
            _ = (y.1 : G) * (y.2 : G) := h
        exact mul_left_cancel h'
      exact Prod.ext (Subtype.ext hxy1) (Subtype.ext hxy2)
    · have hsup : (P.subgroupOf (P ⊔ Q)) ⊔ (Q.subgroupOf (P ⊔ Q)) = ⊤ := by
        apply Subgroup.map_injective (f := (P ⊔ Q).subtype) Subtype.val_injective
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
          Subgroup.map_subgroupOf_eq_of_le le_sup_right, Subgroup.map_top,
          Subgroup.range_subtype]
      have hle1 : P.subgroupOf (P ⊔ Q) ≤ g.range := by
        intro y hy
        exact ⟨(⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩, 1), Subtype.ext (by simp [g, f])⟩
      have hle2 : Q.subgroupOf (P ⊔ Q) ≤ g.range := by
        intro y hy
        exact ⟨(1, ⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩), Subtype.ext (by simp [g, f])⟩
      have hrange : g.range = ⊤ := le_antisymm le_top (hsup ▸ sup_le hle1 hle2)
      exact MonoidHom.range_eq_top.mp hrange
  exact MulEquiv.ofBijective g hg

private theorem sbz_card_le_card_proj {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (F : Subgroup (A × B)) :
    Nat.card F ≤ Nat.card (F.map (MonoidHom.fst A B)) * Nat.card (F.map (MonoidHom.snd A B)) := by
  have hinj : Function.Injective (fun x : F =>
      ((⟨(x : A × B).1, ⟨x, x.2, rfl⟩⟩ : ↥(F.map (MonoidHom.fst A B))),
       (⟨(x : A × B).2, ⟨x, x.2, rfl⟩⟩ : ↥(F.map (MonoidHom.snd A B))))) := by
    intro x y hxy
    have h1 : (x : A × B).1 = (y : A × B).1 :=
      congrArg (fun z => (z.1 : ↥(F.map (MonoidHom.fst A B))).1) hxy
    have h2 : (x : A × B).2 = (y : A × B).2 :=
      congrArg (fun z => (z.2 : ↥(F.map (MonoidHom.snd A B))).1) hxy
    exact Subtype.ext (Prod.ext h1 h2)
  calc Nat.card F
      ≤ Nat.card (↥(F.map (MonoidHom.fst A B)) × ↥(F.map (MonoidHom.snd A B))) :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (F.map (MonoidHom.fst A B)) * Nat.card (F.map (MonoidHom.snd A B)) :=
        Nat.card_prod _ _

private noncomputable def sbz_proj₁ {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) (E : Subgroup G) :
    Subgroup ↥P :=
  ((E.subgroupOf (P ⊔ Q)).map (sbz_supMulEquiv hcomm hdisj).symm.toMonoidHom).map
    (MonoidHom.fst ↥P ↥Q)

private noncomputable def sbz_proj₂ {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) (E : Subgroup G) :
    Subgroup ↥Q :=
  ((E.subgroupOf (P ⊔ Q)).map (sbz_supMulEquiv hcomm hdisj).symm.toMonoidHom).map
    (MonoidHom.snd ↥P ↥Q)

private theorem sbz_card_le_of_prod {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥)
    (E : Subgroup G) (hE : E ≤ P ⊔ Q) {m n : ℕ}
    (h₁ : Nat.card (sbz_proj₁ hcomm hdisj E) ≤ m)
    (h₂ : Nat.card (sbz_proj₂ hcomm hdisj E) ≤ n) :
    Nat.card E ≤ m * n := by
  have hcard1 : Nat.card (E.subgroupOf (P ⊔ Q)) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hcard2 : Nat.card ((E.subgroupOf (P ⊔ Q)).map
      (sbz_supMulEquiv hcomm hdisj).symm.toMonoidHom) = Nat.card (E.subgroupOf (P ⊔ Q)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (E.subgroupOf (P ⊔ Q))
      (sbz_supMulEquiv hcomm hdisj).symm.toMonoidHom
      (sbz_supMulEquiv hcomm hdisj).symm.injective).toEquiv.symm
  have hle := sbz_card_le_card_proj
    ((E.subgroupOf (P ⊔ Q)).map (sbz_supMulEquiv hcomm hdisj).symm.toMonoidHom)
  calc Nat.card E
      = Nat.card ((E.subgroupOf (P ⊔ Q)).map (sbz_supMulEquiv hcomm hdisj).symm.toMonoidHom) := by
        rw [hcard2, hcard1]
    _ ≤ Nat.card (sbz_proj₁ hcomm hdisj E) * Nat.card (sbz_proj₂ hcomm hdisj E) := hle
    _ ≤ m * n := Nat.mul_le_mul h₁ h₂

private theorem sbz_exists_mul_of_mem_sup {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) {g : G}
    (hg : g ∈ P ⊔ Q) : ∃ p ∈ P, ∃ q ∈ Q, p * q = g := by
  obtain ⟨z, hz⟩ := (sbz_supMulEquiv hcomm hdisj).surjective ⟨g, hg⟩
  exact ⟨z.1, z.1.2, z.2, z.2.2, congrArg Subtype.val hz⟩

private theorem sbz_normal_right {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) :
    ∀ g ∈ P ⊔ Q, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
  intro g hg q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := sbz_exists_mul_of_mem_sup hcomm hdisj hg
  have hbq : b * q * b⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hb hq) (Q.inv_mem hb)
  have heq : (a * b) * q * (a * b)⁻¹ = a * (b * q * b⁻¹) * a⁻¹ := by group
  have haq : a * (b * q * b⁻¹) * a⁻¹ = b * q * b⁻¹ := by
    rw [hcomm a ha (b * q * b⁻¹) hbq]; group
  rw [heq, haq]
  exact hbq

end SBZGeneric

private abbrev SympBlockConclusion {K : Type} [Field K] {m : ℕ} (x : StatedSp m K)
    (J : Subgroup (StatedProj (StatedSp m K))) : Prop :=
  (∃ a : ℕ, 2 ≤ a ∧ (3 ∣ Nat.card K - 1 ∨ (a = 2 ∧ 4 ≤ Nat.card K)) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL a K)) ∧
      (3 ∣ a → proj m K x ∈ J) ∧
      (a = 2 → (∀ Q : Subgroup (StatedProj (StatedSp m K)),
          CFSG.Open.IsComponentOf Q (fixSubgroup (MulAut.conj (proj m K x))) → Q = J) →
        ∀ E : Subgroup (StatedSp m K), E ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)) →
          CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)) ∨
  (∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E) (hτ : ∀ y, τ (τ y) = y),
      2 ≤ a ∧ ¬ 3 ∣ Nat.card K - 1 ∧ (Nat.card K = 2 → 4 ≤ a) ∧ (∀ y, τ y = y ^ Nat.card K) ∧
      Nat.card E = Nat.card K ^ 2 ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ)) ∧
      (3 ∣ a → proj m K x ∈ J)) ∨
  (∃ s : ℕ, 2 ≤ s ∧ ¬ (s = 2 ∧ Nat.card K = 2) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp s K))) ∨
  (Nat.card K = 2 ∧ Nat.card (↥J ⧸ Subgroup.center ↥J) = 360)

private theorem sbz_commutator_normal {G : Type*} [Group G] {Q : Subgroup G} :
    (⁅Q, Q⁆.subgroupOf Q).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hQmap : Q.map (MulAut.conj (g : G)).toMonoidHom ≤ Q := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    exact Q.mul_mem (Q.mul_mem g.2 hz) (Q.inv_mem g.2)
  have hmap : (⁅Q, Q⁆ : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom ≤ ⁅Q, Q⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hQmap hQmap
  have := hmap ⟨(n : G), hn, rfl⟩
  simpa [MulAut.conj_apply, Subgroup.coe_mul] using this

private theorem sbz_other_not_quasisimple {K : Type} [Field K] [Finite K] {m : ℕ}
    (hchar : CharP K 2) (hm : 1 ≤ m) {x : StatedSp m K}
    {J : Subgroup (StatedProj (StatedSp m K))} {P Q : Subgroup (StatedSp m K)}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hdisj : P ⊓ Q = ⊥)
    (hjoin : P ⊔ Q = Subgroup.centralizer ({x} : Set (StatedSp m K)))
    (hQp : CFSG.IsQuasisimple ↥⁅P, P⁆)
    (hJeq : J = (⁅P, P⁆).map (proj m K))
    (honly : ∀ R : Subgroup (StatedProj (StatedSp m K)),
      CFSG.Open.IsComponentOf R (fixSubgroup (MulAut.conj (proj m K x))) → R = J) :
    ¬ CFSG.IsQuasisimple ↥⁅Q, Q⁆ := by
  classical
  intro hQq
  haveI : NeZero m := ⟨by omega⟩
  have hbij := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := m) (K := K)
  have hπinj : Function.Injective (proj m K) := hbij.1
  let e : StatedSp m K ≃* StatedProj (StatedSp m K) := MulEquiv.ofBijective (proj m K) hbij
  have hQopen : CFSG.Open.IsQuasisimple ↥⁅Q, Q⁆ := ⟨hQq.1.commutator_eq_top, hQq.2.1⟩
  have hDQsub : CFSG.Open.IsSubnormal (⁅Q, Q⁆)
      (Subgroup.centralizer ({x} : Set (StatedSp m K))) := by
    rw [← hjoin]
    refine CFSG.Open.IsSubnormal.step (commutator_le_self' Q) sbz_commutator_normal ?_
    refine CFSG.Open.IsSubnormal.step le_sup_right ?_ (CFSG.Open.IsSubnormal.refl (P ⊔ Q))
    refine Subgroup.Normal.mk fun n hn g => ?_
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := sbz_normal_right hcomm hdisj (g : StatedSp m K) g.2 (n : StatedSp m K) hn
    simpa [Subgroup.coe_mul] using this
  have hDQC : ⁅Q, Q⁆ ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)) :=
    (commutator_le_self' Q).trans (hjoin ▸ le_sup_right)
  have hcompQ : CFSG.Open.IsComponentOf ⁅Q, Q⁆
      (Subgroup.centralizer ({x} : Set (StatedSp m K))) := ⟨hDQC, hDQsub, hQopen⟩
  have hmapQ := CFSG.isComponentOf_map_mulEquiv e hcompQ
  have he : e.toMonoidHom = proj m K := by ext y; rfl
  have hCmap : (Subgroup.centralizer ({x} : Set (StatedSp m K))).map e.toMonoidHom =
      fixSubgroup (MulAut.conj (proj m K x)) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      have hmap := Subgroup.mem_centralizer_iff.mp hz x rfl
      rw [he, ← map_mul, ← map_mul, hmap]
    · intro hy
      rw [Subgroup.mem_centralizer_iff] at hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e.symm y ∈ Subgroup.centralizer ({x} : Set (StatedSp m K))
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hy (e x) (Set.mem_singleton_iff.mpr rfl)
  have heq : (⁅Q, Q⁆).map (proj m K) = J := by
    rw [hCmap, he] at hmapQ
    exact honly _ hmapQ
  have hD_eq : (⁅Q, Q⁆ : Subgroup (StatedSp m K)) = ⁅P, P⁆ :=
    (Subgroup.map_injective hπinj) (by rw [heq, hJeq])
  have hab : ∀ a ∈ ⁅P, P⁆, ∀ b ∈ ⁅P, P⁆, a * b = b * a := by
    intro a ha b hb
    have haP : a ∈ P := commutator_le_self' P ha
    have hbQ : b ∈ Q := commutator_le_self' Q (hD_eq.symm ▸ hb)
    exact hcomm a haP b hbQ
  have hcenter : Subgroup.center ↥⁅P, P⁆ = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hab (g : StatedSp m K) g.2 (z : StatedSp m K) z.2)
  have hsub : Subsingleton (↥⁅P, P⁆ ⧸ Subgroup.center ↥⁅P, P⁆) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, hcenter]
    trivial
  haveI := hQp.2.1.toNontrivial
  exact not_subsingleton _ hsub

private theorem sba_map_elemAbelian {G H : Type*} [Group G] [Group H] {p : ℕ}
    (f : G →* H) {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨IsMulCommutative.mk ⟨fun x y => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    change (x : H) * (y : H) = (y : H) * (x : H)
    rw [← hax, ← hbx]
    rw [← map_mul, ← map_mul]
    exact congrArg (fun z : ↥E => f (z : G)) (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx
    rw [← hax, ← map_pow, hE.2 a ha, map_one]

private theorem sba_subgroupOf_elemAbelian {G : Type*} [Group G] {p : ℕ} {H E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.subgroupOf H) := by
  refine ⟨IsMulCommutative.mk ⟨fun x y => ?_⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥E => (z : G))
      (hE.1.is_comm.comm ⟨((x : ↥H) : G), Subgroup.mem_subgroupOf.mp x.2⟩
        ⟨((y : ↥H) : G), Subgroup.mem_subgroupOf.mp y.2⟩)
  · have hxE : ((x : ↥H) : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    show ((x : ↥H) : G) ^ p = (1 : G)
    simpa using hE.2 ((x : ↥H) : G) hxE

private theorem sba_elemAbelian_proj₁ {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (sbz_proj₁ hcomm hdisj E) := by
  have h := sba_map_elemAbelian ((MonoidHom.fst ↥P ↥Q).comp
    (sbz_supMulEquiv hcomm hdisj).symm.toMonoidHom) (sba_subgroupOf_elemAbelian hE)
  simpa only [sbz_proj₁, Subgroup.map_map] using h

private theorem sba_elemAbelian_proj₂ {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (sbz_proj₂ hcomm hdisj E) := by
  have h := sba_map_elemAbelian ((MonoidHom.snd ↥P ↥Q).comp
    (sbz_supMulEquiv hcomm hdisj).symm.toMonoidHom) (sba_subgroupOf_elemAbelian hE)
  simpa only [sbz_proj₂, Subgroup.map_map] using h

private theorem sba_three_le_or_card_four {K : Type} [Field K] [Fintype K] {r : ℕ}
    (h4 : 4 ≤ Nat.card K) (hr : 2 ≤ r) : 3 ≤ r ∨ ∃ s : Finset K, s.card = 4 := by
  rcases Nat.lt_or_ge r 3 with h3 | h3
  · right
    have h4' : 4 ≤ (Finset.univ : Finset K).card := by
      simpa [Nat.card_eq_fintype_card] using h4
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4'
    exact ⟨s, hs⟩
  · exact Or.inl h3

private theorem sba_isCyclic_gl_one (K : Type) [Field K] [Finite K] :
    IsCyclic (Matrix.GeneralLinearGroup (Fin 1) K) := by
  haveI : Finite Kˣ := Finite.of_injective Units.val Units.val_injective
  haveI : Finite ↥(⊤ : Subgroup Kˣ) :=
    Finite.of_injective (fun x : ↥(⊤ : Subgroup Kˣ) => (x : Kˣ)) Subtype.val_injective
  have hcycK : IsCyclic Kˣ :=
    (MulEquiv.isCyclic Subgroup.topEquiv).mp (subgroup_units_cyclic (⊤ : Subgroup Kˣ))
  haveI : IsCyclic Kˣ := hcycK
  refine isCyclic_of_injective (Matrix.GeneralLinearGroup.det (n := Fin 1) (R := K)) ?_
  intro A B hAB
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := congrArg (fun u : Kˣ => (u : K)) hAB
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_one, Matrix.det_fin_one] at h
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  rw [hi, hj]
  exact h

private theorem sba_isQuasisimple_gl {r R : ℕ} {K : Type} [Field K] [Finite K]
    {A : Subgroup (StatedSp R K)} (hr : 2 ≤ r)
    (hcond : 3 ≤ r ∨ ∃ s : Finset K, s.card = 4)
    (φ : A ≃* Matrix.GeneralLinearGroup (Fin r) K) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ := by
  classical
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin r) K) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hr hcond
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin r) K) = ⊤ :=
    Group.isPerfect_def.mp hqSL.1
  let θ : Matrix.SpecialLinearGroup (Fin r) K →* Matrix.GeneralLinearGroup (Fin r) K :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin r) K) := by
    refine range_eq_commutator_of_perfect θ hperf
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin r) K →* Kˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin r) (Fin r) K).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  let ψ : Matrix.SpecialLinearGroup (Fin r) K →* StatedSp R K :=
    A.subtype.comp (φ.symm.toMonoidHom.comp θ)
  have hψi : Function.Injective ψ :=
    Subtype.val_injective.comp (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective)
  have hψr : ψ.range = ⁅A, A⁆ := range_comp_eq_commutator φ θ hθ
  have eM : ↥⁅A, A⁆ ≃* Matrix.SpecialLinearGroup (Fin r) K :=
    ((Subgroup.equivMapOfInjective (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin r) K))
        ψ hψi).trans (MulEquiv.subgroupCongr (by rw [Subgroup.map_top, hψr]))).symm.trans
      Subgroup.topEquiv
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eM.symm hqSL

private theorem sba_isQuasisimple_heldGU {r n : ℕ} {K Ef : Type} [Field K] [Finite K]
    [Field Ef] [Finite Ef] {τ : Ef ≃+* Ef} {hτ : ∀ y, τ (τ y) = y}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hEc : Nat.card Ef = Nat.card K ^ 2) (hτQ : ∀ y, τ y = y ^ Nat.card K)
    (hr : 2 ≤ r) (h4 : 4 ≤ Nat.card K)
    {R : ℕ} {A : Subgroup (StatedSp R K)} (φ : A ≃* heldGU r Ef τ hτ) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ := by
  classical
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite Ef
  have h2n : 4 ≤ 2 ^ n := by rw [← hK]; exact h4
  have hE : UnitaryFieldData 2 n Ef :=
    { prime := Nat.prime_two
      one_le := hn
      card := by
        rw [hEc, hK, ← pow_mul, show n * 2 = 2 * n by omega] }
  let ρE : Ef ≃+* Ef :=
    { toFun := hE.bar, invFun := hE.bar, left_inv := hE.bar_bar, right_inv := hE.bar_bar,
      map_mul' := hE.bar.map_mul, map_add' := hE.bar.map_add }
  have hρE : ∀ y, ρE (ρE y) = y := hE.bar_bar
  have hτbar : τ = ρE := by
    refine RingEquiv.ext fun y => ?_
    rw [hτQ y, hK]
    change y ^ 2 ^ n = hE.bar y
    rw [hE.bar_apply]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP Ef 2 := hE.charP
  let B : (Fin r → Ef) →ₛₗ[hE.bar] (Fin r → Ef) →ₗ[Ef] Ef :=
    CFSG.LinearGroups.stdHermForm hE r
  have hB : B.IsSymm := CFSG.LinearGroups.stdHermForm_isSymm hE r
  have hBl : B.SeparatingLeft := CFSG.LinearGroups.stdHermForm_separatingLeft hE r
  let b : Module.Basis (Fin r) Ef (Fin r → Ef) := Pi.basisFun Ef (Fin r)
  have hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    change (CFSG.LinearGroups.stdHermForm hE r (b i)) (b j) = if i = j then 1 else 0
    rw [CFSG.LinearGroups.stdHermForm_apply]
    by_cases h : i = j <;> simp [b, Pi.basisFun_apply, Pi.single_apply, h, eq_comm]
  obtain ⟨eU⟩ := CFSG.LieType.SemisimpleCentralizers.HeldUCD.nonempty_mulEquiv_heldGU
    ρE hρE B b hb
  have eG : heldGU r Ef τ hτ ≃* heldGU r Ef ρE hρE := by
    have h : (heldGU r Ef τ hτ : Subgroup (GL (Fin r) Ef)) = heldGU r Ef ρE hρE := by
      subst hτbar
      rfl
    exact MulEquiv.subgroupCongr h
  let φU : A ≃* sesqUnitaryGroup B := (φ.trans eG).trans eU.symm
  have hfind : Module.finrank Ef (Fin r → Ef) = r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hq : (Module.finrank Ef (Fin r → Ef) = 2 → 4 ≤ 2 ^ n) ∧
      (Module.finrank Ef (Fin r → Ef) = 3 → 3 ≤ 2 ^ n) := by
    constructor <;> intro h <;> rw [hfind] at h <;> omega
  have hqSL : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup B) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
      hE hB hBl (by rw [hfind]; exact hr) hq
  have hker : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitarySpecial (h := hE) B =
      (sesqSpecialUnitaryGroup B).subgroupOf (sesqUnitaryGroup B) := by
    ext δ
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_unitarySpecial (h := hE),
      Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    exact ⟨fun h => ⟨δ.2, h⟩, fun h => h.2⟩
  have hle : ⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ ≤ sesqSpecialUnitaryGroup B := by
    rw [← Subgroup.map_subtype_commutator (sesqUnitaryGroup B)]
    refine Subgroup.map_le_iff_le_comap.2 ?_
    rw [Subgroup.comap_subtype, ← hker]
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.commutator_le_unitarySpecial (h := hE) B
  have hss_eq : (sesqSpecialUnitaryGroup B) =
      ⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ := by
    refine le_antisymm ?_ hle
    have hperf : ⁅(sesqSpecialUnitaryGroup B), (sesqSpecialUnitaryGroup B)⁆ =
        sesqSpecialUnitaryGroup B := Subgroup.isPerfect_iff.mp hqSL.1
    rw [← hperf]
    exact Subgroup.commutator_mono (sesqSpecialUnitaryGroup_le B) (sesqSpecialUnitaryGroup_le B)
  have hqU : CFSG.IsQuasisimple ↥⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hss_eq) hqSL
  obtain ⟨ecom⟩ : Nonempty (↥(commutator ↥A) ≃*
      ↥(commutator ↥(sesqUnitaryGroup B))) := by
    refine ⟨(Subgroup.equivMapOfInjective (commutator ↥A) φU φU.injective).trans
      (MulEquiv.subgroupCongr ?_)⟩
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 φU.surjective, ← commutator_def]
  have e1 : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
    (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
  have e2 : ↥(commutator ↥(sesqUnitaryGroup B)) ≃*
      ↥⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ :=
    (Subgroup.equivMapOfInjective (commutator ↥(sesqUnitaryGroup B))
      (sesqUnitaryGroup B).subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr
        (Subgroup.map_subtype_commutator (sesqUnitaryGroup B)))
  have eAU : ↥⁅A, A⁆ ≃* ↥⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ :=
    e1.symm.trans (ecom.trans e2)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eAU.symm hqU

private theorem sbz_rank_a1 {K : Type} [Field K] [Finite K] {n m : ℕ}
    (hK : Nat.card K = 2 ^ n) (hchar : CharP K 2) (hm : 1 ≤ m) (h4 : 4 ≤ Nat.card K)
    {x : StatedSp m K} {A₁ A₂ : Subgroup (StatedSp m K)}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hjoin : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp m K)))
    (hφ : A₁ ≃* StatedSp 1 K) (hQ : CFSG.IsQuasisimple ↥⁅A₁, A₁⁆)
    (hA2 : (∃ r : ℕ, 1 ≤ r ∧ Nonempty (A₂ ≃* GL (Fin r) K)) ∨
      ∃ (r : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E) (hτ : ∀ y, τ (τ y) = y),
        1 ≤ r ∧ Nat.card E = Nat.card K ^ 2 ∧ (∀ y, τ y = y ^ Nat.card K) ∧
          Nonempty (A₂ ≃* heldGU r E τ hτ))
    {J : Subgroup (StatedProj (StatedSp m K))} (hJeq : J = (⁅A₁, A₁⁆).map (proj m K))
    (huniq : ∀ Q : Subgroup (StatedProj (StatedSp m K)),
      CFSG.Open.IsComponentOf Q (fixSubgroup (MulAut.conj (proj m K x))) → Q = J)
    {E : Subgroup (StatedSp m K)} (hE : E ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)))
    (hEab : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  classical
  haveI := hchar
  haveI : Fintype K := Fintype.ofFinite K
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hK
    omega
  have hdisj : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzcenter : (⟨z, hz.1⟩ : ↥A₁) ∈ Subgroup.center ↥A₁ := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2 z hz.2)
    have hcenter : Subgroup.center ↥A₁ = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have hw' : hφ w ∈ Subgroup.center (StatedSp 1 K) := by
        rw [Subgroup.mem_center_iff] at hw ⊢
        intro y
        obtain ⟨v, rfl⟩ := hφ.surjective y
        rw [← map_mul, ← map_mul, hw v]
      rw [CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := 1) le_rfl]
        at hw'
      exact Subgroup.mem_bot.mpr (hφ.injective (by rw [Subgroup.mem_bot.mp hw', map_one]))
    rw [hcenter] at hzcenter
    exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hzcenter))
  have hnotq : ¬ CFSG.IsQuasisimple ↥⁅A₂, A₂⁆ :=
    sbz_other_not_quasisimple hchar hm hcomm hdisj hjoin hQ hJeq huniq
  have hproj₁_bound : Nat.card (sbz_proj₁ hcomm hdisj E) ≤ 3 := by
    have hEA1 : CFSG.Open.IsElemAbelian 3 (sbz_proj₁ hcomm hdisj E) :=
      sba_elemAbelian_proj₁ hcomm hdisj hEab
    let e1 : ↥A₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      hφ.trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm
    have hSmap : CFSG.Open.IsElemAbelian 3 ((sbz_proj₁ hcomm hdisj E).map e1.toMonoidHom) :=
      sba_map_elemAbelian e1.toMonoidHom hEA1
    have hcard : Nat.card ((sbz_proj₁ hcomm hdisj E).map e1.toMonoidHom) =
        Nat.card (sbz_proj₁ hcomm hdisj E) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ e1.toMonoidHom e1.injective).toEquiv.symm
    have hle := CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof.card_le_three_of_elemAbelian_sl2 hSmap
    rwa [hcard] at hle
  have hproj₂_bound : Nat.card (sbz_proj₂ hcomm hdisj E) ≤ 3 := by
    have hEA2 : CFSG.Open.IsElemAbelian 3 (sbz_proj₂ hcomm hdisj E) :=
      sba_elemAbelian_proj₂ hcomm hdisj hEab
    rcases hA2 with ⟨r, hr1, ⟨eGL⟩⟩ | ⟨r, Ef, hEff, hEfinf, τ, hτ, hr1, hEcf, hτQf, ⟨eGU⟩⟩
    · have hrle : r ≤ 1 := by
        by_contra hcon
        have hr2 : 2 ≤ r := by omega
        exact hnotq (sba_isQuasisimple_gl (K := K) hr2 (sba_three_le_or_card_four h4 hr2) eGL)
      have hr_eq : r = 1 := by omega
      subst hr_eq
      haveI : IsCyclic (Matrix.GeneralLinearGroup (Fin 1) K) := sba_isCyclic_gl_one K
      haveI : IsCyclic ↥A₂ := (MulEquiv.isCyclic eGL).mpr inferInstance
      exact CFSG.HardMathSupport.Solomon.LocalBalance.card_le_of_isCyclic_of_isElemAbelian
        hEA2 (by norm_num) (Subgroup.isCyclic (sbz_proj₂ hcomm hdisj E))
    · have hrle : r ≤ 1 := by
        by_contra hcon
        have hr2 : 2 ≤ r := by omega
        exact hnotq (sba_isQuasisimple_heldGU hK hn hEcf hτQf hr2 h4 eGU)
      have hr_eq : r = 1 := by omega
      subst hr_eq
      haveI : IsCyclic (Matrix.GeneralLinearGroup (Fin 1) Ef) := sba_isCyclic_gl_one Ef
      have hcycGU : IsCyclic ↥(heldGU 1 Ef τ hτ) := Subgroup.isCyclic (heldGU 1 Ef τ hτ)
      haveI : IsCyclic ↥A₂ := (MulEquiv.isCyclic eGU).mpr hcycGU
      exact CFSG.HardMathSupport.Solomon.LocalBalance.card_le_of_isCyclic_of_isElemAbelian
        hEA2 (by norm_num) (Subgroup.isCyclic (sbz_proj₂ hcomm hdisj E))
  have hEsup : E ≤ A₁ ⊔ A₂ := by rw [hjoin]; exact hE
  calc Nat.card E ≤ 3 * 3 := sbz_card_le_of_prod hcomm hdisj E hEsup hproj₁_bound hproj₂_bound
    _ = 9 := by norm_num

private theorem sbg_isQuasisimple_commutator_of_equiv {s r : ℕ} {K : Type} [Field K] [Finite K]
    {A : Subgroup (StatedSp r K)} (hs : 1 ≤ s) (h4 : 4 ≤ Nat.card K) (φ : A ≃* StatedSp s K) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ := by
  have hq : CFSG.IsQuasisimple ↥(commutator (StatedSp s K)) := by
    have h := CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs (Or.inl (Or.inr h4))
    have h1 : commutator (StatedSp s K) = ⊤ := Group.isPerfect_def.mp h.1
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr h1).trans Subgroup.topEquiv).symm h
  obtain ⟨e1⟩ := commutator_equiv_statedSp φ
  have h2 : CFSG.IsQuasisimple ↥(commutator ↥A) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm hq
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))) h2

private theorem sbz_rank_gl {K : Type} [Field K] [Finite K] {n m : ℕ}
    (hK : Nat.card K = 2 ^ n) (hchar : CharP K 2) (hm : 1 ≤ m) (h4 : 4 ≤ Nat.card K)
    {x : StatedSp m K} {A₁ A₂ : Subgroup (StatedSp m K)}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hjoin : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp m K)))
    {s : ℕ} (hsφ : A₁ ≃* StatedSp s K) (hφ : A₂ ≃* GL (Fin 2) K)
    (hQ : CFSG.IsQuasisimple ↥⁅A₂, A₂⁆)
    {J : Subgroup (StatedProj (StatedSp m K))} (hJeq : J = (⁅A₂, A₂⁆).map (proj m K))
    (huniq : ∀ Q : Subgroup (StatedProj (StatedSp m K)),
      CFSG.Open.IsComponentOf Q (fixSubgroup (MulAut.conj (proj m K x))) → Q = J)
    {E : Subgroup (StatedSp m K)} (hE : E ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)))
    (hEab : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  classical
  haveI : CharP K 2 := hchar
  have hdisj : A₂ ⊓ A₁ = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro g hg
    obtain ⟨hgA₂, hgA₁⟩ := hg
    rw [Subgroup.mem_bot]
    have hcenter : hsφ ⟨g, hgA₁⟩ ∈ Subgroup.center (StatedSp s K) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨w, rfl⟩ := hsφ.surjective z
      rw [← map_mul, ← map_mul]
      exact congrArg hsφ (Subtype.ext (hcomm w w.2 g hgA₂))
    have hcenter_bot : Subgroup.center (StatedSp s K) = ⊥ := by
      obtain rfl | hs := Nat.eq_zero_or_pos s
      · refine le_antisymm ?_ bot_le
        intro y _
        rw [Subgroup.mem_bot]
        haveI : Subsingleton (StatedSp 0 K) := by
          have hcard : Nat.card (StatedSp 0 K) = 1 := by
            rw [SymplecticFlag.card_statedSp]
            simp
          exact (Nat.card_eq_one_iff_unique.mp hcard).1
        exact Subsingleton.elim y 1
      · exact CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two
          (by omega : 1 ≤ s)
    rw [hcenter_bot, Subgroup.mem_bot] at hcenter
    have h1 : (⟨g, hgA₁⟩ : ↥A₁) = 1 :=
      hsφ.injective (by rw [hcenter, map_one])
    simpa using congrArg Subtype.val h1
  have hs0 : s = 0 := by
    by_contra hsne
    have hs : 1 ≤ s := by omega
    have hQ1 : CFSG.IsQuasisimple ↥⁅A₁, A₁⁆ :=
      sbg_isQuasisimple_commutator_of_equiv hs h4 hsφ
    exact (sbz_other_not_quasisimple hchar hm (P := A₂) (Q := A₁)
      (fun p hp q hq => (hcomm q hq p hp).symm) hdisj (by rw [sup_comm]; exact hjoin) hQ hJeq huniq) hQ1
  have hA₁le : A₁ ≤ ⊥ := by
    intro g hg
    rw [Subgroup.mem_bot]
    haveI : Subsingleton ↥A₁ := by
      have hcard : Nat.card ↥A₁ = 1 := by
        rw [Nat.card_congr hsφ.toEquiv, hs0, SymplecticFlag.card_statedSp]
        simp
      exact (Nat.card_eq_one_iff_unique.mp hcard).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨g, hg⟩ : ↥A₁) 1)
  have hE_A₂ : E ≤ A₂ := by
    have hEjoin : E ≤ A₁ ⊔ A₂ := by rw [hjoin]; exact hE
    rwa [sup_eq_right.mpr (hA₁le.trans bot_le)] at hEjoin
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hEab' : CFSG.Open.IsElemAbelian 3 ((E.subgroupOf A₂).map hφ.toMonoidHom) :=
    (hEab.subgroupOf A₂).map hφ.toMonoidHom
  have hcardE' : Nat.card ((E.subgroupOf A₂).map hφ.toMonoidHom) = Nat.card E := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective (E.subgroupOf A₂) hφ.toMonoidHom
        hφ.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_A₂).toEquiv]
  calc Nat.card E
      = Nat.card ((E.subgroupOf A₂).map hφ.toMonoidHom) := hcardE'.symm
    _ ≤ 9 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.card_le_nine_of_elemAbelian_GL2
        (K := K) hK3 hEab'

private theorem sbc_card_quot_center_a6 {R F : Type} [Group R] [Field F] [Finite F]
    (hK2 : Nat.card F = 2) (e : ↥(commutator ↥(StatedSp 2 F)) ≃* R) :
    Nat.card (R ⧸ Subgroup.center R) = 360 := by
  let eR : R ≃* alternatingGroup (Fin 6) :=
    e.symm.trans (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK2)
  have hZ : Subgroup.center R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eR z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro a
      obtain ⟨y, rfl⟩ := eR.surjective a
      rw [← map_mul, ← map_mul, hz]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact eR.injective (by simpa using hz')
  calc Nat.card (R ⧸ Subgroup.center R) = Nat.card (R ⧸ (⊥ : Subgroup R)) := by rw [hZ]
    _ = Nat.card R := Nat.card_congr (QuotientGroup.quotientBot (G := R)).toEquiv
    _ = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr eR.toEquiv
    _ = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num

private theorem a1_branch {K : Type} [Field K] [Finite K] {n m : ℕ}
    (hK : Nat.card K = 2 ^ n) (hchar : CharP K 2) (hm : 1 ≤ m) {x : StatedSp m K}
    (hx : x ^ 3 = 1) {J : Subgroup (StatedProj (StatedSp m K))}
    (hcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x))))
    {A₁ A₂ : Subgroup (StatedSp m K)}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hjoin : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp m K)))
    {s : ℕ} (hs : 1 ≤ s) (hφ : A₁ ≃* StatedSp s K)
    (hQ : CFSG.IsQuasisimple ↥⁅A₁, A₁⁆)
    (hA2 : (∃ r : ℕ, 1 ≤ r ∧ Nonempty (A₂ ≃* GL (Fin r) K)) ∨
      ∃ (r : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E) (hτ : ∀ y, τ (τ y) = y),
        1 ≤ r ∧ Nat.card E = Nat.card K ^ 2 ∧ (∀ y, τ y = y ^ Nat.card K) ∧
          Nonempty (A₂ ≃* heldGU r E τ hτ))
    (hJeq : J = (⁅A₁, A₁⁆).map (proj m K)) :
    SympBlockConclusion x J := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hπinj : Function.Injective (proj m K) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo).1
  obtain ⟨eMJ⟩ : Nonempty (↥⁅A₁, A₁⁆ ≃* ↥J) :=
    ⟨(Subgroup.equivMapOfInjective ⁅A₁, A₁⁆ (proj m K) hπinj).trans
      (MulEquiv.subgroupCongr hJeq.symm)⟩
  obtain ⟨eZ⟩ := Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eMJ
  rcases spFactor_cases hs hφ hQ with ⟨rfl, h4, ⟨eSL⟩⟩ | ⟨hs2, hne, ⟨eSp⟩⟩ | ⟨rfl, hK2, ⟨eSp42⟩⟩
  ·
    obtain ⟨eSLZ⟩ := Y10GCenterQuot.nonempty_centerQuot_sl 2 eSL
    refine Or.inl ⟨2, le_rfl, Or.inr ⟨rfl, h4⟩, ⟨eZ.symm.trans eSLZ⟩, ?_, ?_⟩
    · intro h3
      omega
    · intro _ huniq E hE hEab
      exact sbz_rank_a1 hK hchar hm h4 hcomm hjoin hφ hQ hA2 hJeq huniq hE hEab
  ·
    obtain ⟨eSpZ⟩ := Y10GCenterQuot.nonempty_centerQuot_sp hs2 hne hchar eSp
    exact Or.inr (Or.inr (Or.inl ⟨s, hs2, hne, ⟨eZ.symm.trans eSpZ⟩⟩))
  ·
    have h360 : Nat.card (↥⁅A₁, A₁⁆ ⧸ Subgroup.center ↥⁅A₁, A₁⁆) = 360 :=
      sbc_card_quot_center_a6 hK2 eSp42.symm
    have hJZ : Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
      calc Nat.card (↥J ⧸ Subgroup.center ↥J)
          = Nat.card (↥⁅A₁, A₁⁆ ⧸ Subgroup.center ↥⁅A₁, A₁⁆) :=
            (Nat.card_congr eZ.toEquiv).symm
        _ = 360 := h360
    exact Or.inr (Or.inr (Or.inr ⟨hK2, hJZ⟩))

private theorem gl_branch {K : Type} [Field K] [Finite K] {n m : ℕ}
    (hK : Nat.card K = 2 ^ n) (hchar : CharP K 2) (hm : 1 ≤ m) {x : StatedSp m K}
    (hx : x ^ 3 = 1) (hx1 : x ≠ 1) {J : Subgroup (StatedProj (StatedSp m K))}
    (hcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x))))
    {A₁ A₂ : Subgroup (StatedSp m K)}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hjoin : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp m K)))
    (hx2 : x ∈ A₂) {r : ℕ} (hφ : A₂ ≃* Matrix.GeneralLinearGroup (Fin r) K)
    (hQ : CFSG.IsQuasisimple ↥⁅A₂, A₂⁆)
    (hJeq : J = (⁅A₂, A₂⁆).map (proj m K))
    {s : ℕ} (hsφ : A₁ ≃* StatedSp s K) :
    SympBlockConclusion x J := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  haveI := hchar
  have hπinj : Function.Injective (proj m K) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo).1
  obtain ⟨eMJ⟩ : Nonempty (↥⁅A₂, A₂⁆ ≃* ↥J) :=
    ⟨(Subgroup.equivMapOfInjective ⁅A₂, A₂⁆ (proj m K) hπinj).trans
      (MulEquiv.subgroupCongr hJeq.symm)⟩
  obtain ⟨eZ⟩ := Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eMJ
  have hMle : ⁅A₂, A₂⁆ ≤ A₂ := commutator_le_self' A₂
  have hnotSolv : ¬ Group.IsSolvable ↥A₂ := by
    intro hsol
    haveI := hsol
    haveI hMsol : Group.IsSolvable ↥⁅A₂, A₂⁆ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMle)
        (Subgroup.inclusion_injective hMle)
    haveI : Group.IsPerfect ↥⁅A₂, A₂⁆ := hQ.1
    haveI : Nontrivial ↥⁅A₂, A₂⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    exact (Group.IsPerfect.not_isSolvable ↥⁅A₂, A₂⁆) inferInstance
  have hr2 : 2 ≤ r := by
    by_contra hlt
    haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin r) K) :=
      isSolvable_gl_of_le_one (by omega)
    exact hnotSolv (Group.isSolvable_of_surjective (f := hφ.symm.toMonoidHom) hφ.symm.surjective)
  have hcond : 3 ≤ r ∨ ∃ t : Finset K, t.card = 4 := by
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · have hr : r = 2 := by omega
      subst hr
      right
      by_contra hno
      have hle : Nat.card K ≤ 3 := by
        by_contra hlt
        have h4 : 4 ≤ Nat.card K := by omega
        haveI := Fintype.ofFinite K
        have h4' : 4 ≤ (Finset.univ : Finset K).card := by
          simpa [Nat.card_eq_fintype_card] using h4
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
        exact hno ⟨t, ht⟩
      have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
      have hcard : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
      haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K hcard
      exact hnotSolv (Group.isSolvable_of_surjective (f := hφ.symm.toMonoidHom) hφ.symm.surjective)
    · exact Or.inl h3
  have hcommGL := commutator_gl_eq_statedSL (r := r) (K := K) hr2 hcond
  have hθ : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin r) K →* Matrix.GeneralLinearGroup (Fin r) K).range =
      commutator (Matrix.GeneralLinearGroup (Fin r) K) := by
    rw [← commutator_def] at hcommGL
    rw [hcommGL, CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
  let θ : Matrix.SpecialLinearGroup (Fin r) K →* Matrix.GeneralLinearGroup (Fin r) K :=
    Matrix.SpecialLinearGroup.toGL
  let ψ : Matrix.SpecialLinearGroup (Fin r) K →* StatedSp m K :=
    A₂.subtype.comp (hφ.symm.toMonoidHom.comp θ)
  have hψi : Function.Injective ψ :=
    Subtype.val_injective.comp (hφ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective)
  have hψr : ψ.range = ⁅A₂, A₂⁆ := range_comp_eq_commutator hφ θ hθ
  obtain ⟨eM⟩ : Nonempty (↥⁅A₂, A₂⁆ ≃* Matrix.SpecialLinearGroup (Fin r) K) :=
    equiv_of_range ψ hψi hψr
  let xA : ↥A₂ := ⟨x, hx2⟩
  have hxZ : xA ∈ Subgroup.center ↥A₂ := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : (y : StatedSp m K) ∈ Subgroup.centralizer ({x} : Set (StatedSp m K)) := by
      rw [← hjoin]
      exact Subgroup.mem_sup_right y.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hy x (Set.mem_singleton x)
    exact Subtype.ext hcomm.symm
  have hcentGL : hφ xA ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin r) K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨a, rfl⟩ := hφ.surjective y
    have hcomm := Subgroup.mem_center_iff.mp hxZ a
    rw [← map_mul, ← map_mul, hcomm.symm]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcentGL
  obtain ⟨lam, hlam⟩ := hcentGL
  have hxA3 : xA ^ 3 = 1 := Subtype.ext (by simpa using hx)
  haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  have hlam3 : lam ^ 3 = 1 := by
    apply Units.ext
    show (lam : K) ^ 3 = 1
    have h3 : (Matrix.GeneralLinearGroup.scalar (Fin r) lam) ^ 3 = 1 := by
      rw [hlam]
      exact (by rw [← map_pow, hxA3, map_one] : (hφ xA) ^ 3 = 1)
    have hmat : (Matrix.scalar (Fin r) (lam : K)) ^ 3 = 1 := by
      have := congrArg (fun g : GL (Fin r) K => (g : Matrix (Fin r) (Fin r) K)) h3
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
    have hmat' : Matrix.scalar (Fin r) ((lam : K) ^ 3) = Matrix.scalar (Fin r) (1 : K) := by
      rw [map_pow, hmat, map_one]
    exact (Matrix.scalar_inj (n := Fin r)).mp hmat'
  have hlam_ne : lam ≠ 1 := by
    intro h
    apply hx1
    have h1 : hφ xA = 1 := by rw [← hlam, h, map_one]
    have h2 : xA = 1 := hφ.injective (by simpa using h1)
    exact congrArg Subtype.val h2
  have h3dvd : 3 ∣ Nat.card K - 1 := by
    have hord : orderOf lam = 3 := orderOf_eq_prime hlam3 hlam_ne
    have hdvd := orderOf_dvd_natCard lam
    rw [hord, Nat.card_units] at hdvd
    exact hdvd
  have hxJ : 3 ∣ r → proj m K x ∈ J := by
    intro h3r
    have hdet : Matrix.GeneralLinearGroup.det (hφ xA) = 1 := by
      rw [← hlam, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
      obtain ⟨t, rfl⟩ := h3r
      rw [pow_mul, hlam3, one_pow]
    have hxSL : hφ xA ∈ StatedSL r K := by
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
      have := congrArg Units.val hdet
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    have hxM : x ∈ ⁅A₂, A₂⁆ := by
      rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL] at hxSL
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hxSL
      have hψy : ψ y = x := by
        show (A₂.subtype (hφ.symm (θ y)) : StatedSp m K) = x
        rw [show θ y = hφ xA from hy]
        exact congrArg Subtype.val (hφ.symm_apply_apply xA)
      rw [← hψr]
      exact MonoidHom.mem_range.mpr ⟨y, hψy⟩
    rw [hJeq]
    exact Subgroup.mem_map_of_mem _ hxM
  obtain ⟨eSLZ⟩ := Y10GCenterQuot.nonempty_centerQuot_sl r eM
  refine Or.inl ⟨r, hr2, Or.inl h3dvd, ⟨eZ.symm.trans eSLZ⟩, hxJ, ?_⟩
  intro hr2eq huniq E hE hEab
  subst hr2eq
  have h4 : 4 ≤ Nat.card K := by
    have hpos : 0 < Nat.card K - 1 := Nat.sub_pos_of_lt (Finite.one_lt_card (α := K))
    have h3le : 3 ≤ Nat.card K - 1 := Nat.le_of_dvd hpos h3dvd
    clear h3dvd
    omega
  exact sbz_rank_gl hK hchar hm h4 hcomm hjoin hsφ hφ hQ hJeq huniq hE hEab

private theorem commutator_heldGU_eq_of_perfect {r : ℕ} {E : Type} [Field E]
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hperf : Group.IsPerfect ↥(heldSU r E τ hτ)) :
    ⁅(heldGU r E τ hτ : Subgroup (GL (Fin r) E)), heldGU r E τ hτ⁆ =
      heldSU r E τ hτ := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_heldSU hx hy
  · rw [← Subgroup.isPerfect_iff.mp hperf]
    exact Subgroup.commutator_mono inf_le_left inf_le_left

private theorem isSolvable_subgroupOf_heldSU {r : ℕ} {E : Type} [Field E]
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (h : Group.IsSolvable ↥(heldSU r E τ hτ)) :
    Group.IsSolvable ↥((heldSU r E τ hτ).subgroupOf (heldGU r E τ hτ)) := by
  haveI : Group.IsSolvable ↥(heldGU r E τ hτ ⊓ StatedSL r E) := h
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : heldSU r E τ hτ ≤ heldGU r E τ hτ)).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe _).symm.surjective

private theorem sbc_commutator_isSolvable_of_heldSU {r : ℕ} {E : Type} [Field E]
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    {G : Type} [Group G] {A : Subgroup G} (φ : A ≃* heldGU r E τ hτ)
    (hSU : Group.IsSolvable ↥(heldSU r E τ hτ)) :
    Group.IsSolvable ↥⁅A, A⁆ := by
  have e1 : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
    (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
  have ecomm : ↥(commutator ↥A) ≃* ↥(commutator ↥(heldGU r E τ hτ)) :=
    (Subgroup.equivMapOfInjective (commutator ↥A) φ φ.injective).trans
      (MulEquiv.subgroupCongr (by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
          MonoidHom.range_eq_top.2 φ.surjective, ← commutator_def]))
  haveI : Group.IsSolvable ↥(commutator ↥(heldGU r E τ hτ)) := by
    haveI := isSolvable_subgroupOf_heldSU (r := r) hSU
    have hle : commutator ↥(heldGU r E τ hτ) ≤
        (heldSU r E τ hτ).subgroupOf (heldGU r E τ hτ) := by
      intro g hg
      have hg' : (g : GL (Fin r) E) ∈
          ⁅(heldGU r E τ hτ : Subgroup (GL (Fin r) E)), heldGU r E τ hτ⁆ := by
        rw [← Subgroup.map_subtype_commutator]
        exact Subgroup.mem_map_of_mem _ hg
      exact (Subgroup.commutator_le.mpr (fun x hx y hy =>
        CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_heldSU hx hy)) hg'
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Group.IsSolvable ↥(commutator ↥A) :=
    Group.isSolvable_of_surjective (f := ecomm.symm.toMonoidHom) ecomm.symm.surjective
  exact Group.isSolvable_of_surjective (f := e1.toMonoidHom) e1.surjective

private theorem gu_branch {K E : Type} [Field K] [Finite K] [Field E] [Finite E]
    {n m : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hchar : CharP K 2) (hm : 1 ≤ m)
    {x : StatedSp m K} (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    {J : Subgroup (StatedProj (StatedSp m K))}
    (hcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x))))
    {A₁ A₂ : Subgroup (StatedSp m K)}
    (hjoin : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp m K)))
    (hx2 : x ∈ A₂) {r : ℕ} {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hEc : Nat.card E = Nat.card K ^ 2) (hτQ : ∀ y, τ y = y ^ Nat.card K)
    (hφ : A₂ ≃* heldGU r E τ hτ) (hQ : CFSG.IsQuasisimple ↥⁅A₂, A₂⁆)
    (hJeq : J = (⁅A₂, A₂⁆).map (proj m K)) :
    SympBlockConclusion x J := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  haveI := hchar
  have hπinj : Function.Injective (proj m K) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo).1
  obtain ⟨eMJ⟩ : Nonempty (↥⁅A₂, A₂⁆ ≃* ↥J) :=
    ⟨(Subgroup.equivMapOfInjective ⁅A₂, A₂⁆ (proj m K) hπinj).trans
      (MulEquiv.subgroupCongr hJeq.symm)⟩
  obtain ⟨eZ⟩ := Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eMJ
  have hMle : ⁅A₂, A₂⁆ ≤ A₂ := commutator_le_self' A₂
  have hnotSolv : ¬ Group.IsSolvable ↥A₂ := by
    intro hsol
    haveI := hsol
    haveI hMsol : Group.IsSolvable ↥⁅A₂, A₂⁆ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMle)
        (Subgroup.inclusion_injective hMle)
    haveI : Group.IsPerfect ↥⁅A₂, A₂⁆ := hQ.1
    haveI : Nontrivial ↥⁅A₂, A₂⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    exact (Group.IsPerfect.not_isSolvable ↥⁅A₂, A₂⁆) inferInstance
  have hr2 : 2 ≤ r := by
    by_contra hlt
    have hrle : r ≤ 1 := by omega
    haveI : Group.IsSolvable ↥(heldGU r E τ hτ) := by
      have hcomm : ∀ a b : heldGU r E τ hτ, a * b = b * a := by
        intro a b
        exact Subtype.ext (CFSG.LieType.SemisimpleCentralizers.Held.mul_comm_GL_of_le_one
          (M := E) hrle (a : GL (Fin r) E) (b : GL (Fin r) E))
      exact Group.isSolvable_of_comm hcomm
    exact hnotSolv (Group.isSolvable_of_surjective (f := hφ.symm.toMonoidHom) hφ.symm.surjective)
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite E
  have hE : UnitaryFieldData 2 n E :=
    { prime := Nat.prime_two
      one_le := hn
      card := by rw [hEc, hK, ← pow_mul, show n * 2 = 2 * n by omega] }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := hE.charP
  have hbad : ¬ (r ≤ 3 ∧ Nat.card K = 2) := by
    rintro ⟨hrle, hK2⟩
    have hr23 : r = 2 ∨ r = 3 := by omega
    rcases hr23 with rfl | rfl
    · have hEcard : Nat.card E = (2 ^ n) ^ 2 := by rw [hEc, hK]
      have hcard : Nat.card (StatedSU 2 (Nat.card K) E) =
          Nat.card K * (Nat.card K ^ 2 - 1) := by
        rw [hK]
        exact CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E) (r := 2) (f := n) hEcard
      have hsol : Group.IsSolvable ↥(heldSU 2 E τ hτ) := by
        rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ]
        exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
          (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [hcard, hK2]; norm_num)
      have hMsol : Group.IsSolvable ↥⁅A₂, A₂⁆ := sbc_commutator_isSolvable_of_heldSU hφ hsol
      haveI : Group.IsPerfect ↥⁅A₂, A₂⁆ := hQ.1
      haveI : Nontrivial ↥⁅A₂, A₂⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hQ
      exact (Group.IsPerfect.not_isSolvable ↥⁅A₂, A₂⁆) hMsol
    · have hEcard : Nat.card E = (2 ^ 1) ^ 2 := by
        rw [hEc, hK2]; norm_num
      have hcard : Nat.card (StatedSU 3 (2 ^ 1) E) = 216 := by
        rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two hEcard]; norm_num
      haveI hsol : Group.IsSolvable ↥(heldSU 3 E τ hτ) := by
        rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ, hK2]
        exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
          (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
          (by have h216 : Nat.card ↥(StatedSU 3 2 E) = 216 := by simpa using hcard
              rw [h216]; norm_num)
      have hMsol : Group.IsSolvable ↥⁅A₂, A₂⁆ := sbc_commutator_isSolvable_of_heldSU hφ hsol
      haveI : Group.IsPerfect ↥⁅A₂, A₂⁆ := hQ.1
      haveI : Nontrivial ↥⁅A₂, A₂⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hQ
      exact (Group.IsPerfect.not_isSolvable ↥⁅A₂, A₂⁆) hMsol
  have hperfSU : Group.IsPerfect ↥(heldSU r E τ hτ) := by
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · have hr : r = 2 := by omega
      subst hr
      have hq4 : 4 ≤ Nat.card K := by
        by_contra hlt
        have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
        have hQ2 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
        have hEcard : Nat.card E = (2 ^ n) ^ 2 := by rw [hEc, hK]
        have hcard : Nat.card (StatedSU 2 (Nat.card K) E) =
            Nat.card K * (Nat.card K ^ 2 - 1) := by
          rw [hK]
          exact CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E) (r := 2) (f := n) hEcard
        have hsolSU : Group.IsSolvable ↥(heldSU 2 E τ hτ) := by
          rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ]
          rcases hQ2 with h | h
          · exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
              (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
              (by rw [hcard, h]; norm_num)
          · exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
              (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
              (by rw [hcard, h]; norm_num)
        have hMsol : Group.IsSolvable ↥⁅A₂, A₂⁆ := sbc_commutator_isSolvable_of_heldSU hφ hsolSU
        haveI : Group.IsPerfect ↥⁅A₂, A₂⁆ := hQ.1
        haveI : Nontrivial ↥⁅A₂, A₂⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hQ
        exact (Group.IsPerfect.not_isSolvable ↥⁅A₂, A₂⁆) hMsol
      have hEcard : Nat.card E = (2 ^ n) ^ 2 := by rw [hEc, hK]
      rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ, hK]
      exact CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two hEcard (by rwa [← hK])
    · have hEcard : Nat.card E = (2 ^ n) ^ 2 := by rw [hEc, hK]
      rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ, hK]
      exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hEcard hr3
        (fun h => hbad ⟨le_of_eq (congrArg Prod.fst h), by
          have h2 : 2 ^ n = 2 := congrArg Prod.snd h
          rwa [← hK] at h2⟩)
  have hcomm_eq := commutator_heldGU_eq_of_perfect hperfSU
  obtain ⟨eM⟩ : Nonempty (↥⁅A₂, A₂⁆ ≃* ↥(heldSU r E τ hτ)) := by
    have e1 : ↥⁅A₂, A₂⁆ ≃* ↥(commutator ↥A₂) :=
      ((Subgroup.equivMapOfInjective (commutator ↥A₂) A₂.subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A₂))).symm
    have ecomm : ↥(commutator ↥A₂) ≃* ↥(commutator ↥(heldGU r E τ hτ)) :=
      (Subgroup.equivMapOfInjective (commutator ↥A₂) hφ hφ.injective).trans
        (MulEquiv.subgroupCongr (by
          rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
            MonoidHom.range_eq_top.2 hφ.surjective, ← commutator_def]))
    have e2 : ↥(commutator ↥(heldGU r E τ hτ)) ≃* ↥(heldSU r E τ hτ) :=
      (Subgroup.equivMapOfInjective (commutator ↥(heldGU r E τ hτ))
        (heldGU r E τ hτ).subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (by
          rw [Subgroup.map_subtype_commutator]
          exact hcomm_eq))
    exact ⟨e1.trans (ecomm.trans e2)⟩
  let xA : ↥A₂ := ⟨x, hx2⟩
  have hxA3 : xA ^ 3 = 1 := Subtype.ext (by simpa using hx)
  have hτb : (τ : E →+* E) = hE.bar := by
    refine RingHom.ext fun y => ?_
    show τ y = hE.bar y
    rw [hτQ y, hK, hE.bar_apply]
  have hxZ : xA ∈ Subgroup.center ↥A₂ := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : (y : StatedSp m K) ∈ Subgroup.centralizer ({x} : Set (StatedSp m K)) := by
      rw [← hjoin]
      exact Subgroup.mem_sup_right y.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hy x (Set.mem_singleton x)
    exact Subtype.ext hcomm.symm
  have hcent : hφ xA ∈ Subgroup.center ↥(heldGU r E τ hτ) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨a, rfl⟩ := hφ.surjective y
    have hcomm := Subgroup.mem_center_iff.mp hxZ a
    rw [← map_mul, ← map_mul, hcomm.symm]
  obtain ⟨c, hc⟩ := heldGU_center_scalar hE hr2 hτb (A := hφ xA) hcent
  have hφdet : ((Matrix.GeneralLinearGroup.det ((hφ xA : GL (Fin r) E)) : Eˣ) : E) = c ^ r := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hc, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin]
  have hc3 : c ^ 3 = 1 := by
    have h3 : (hφ xA) ^ 3 = 1 := by rw [← map_pow, hxA3, map_one]
    have h3GL : (hφ xA : GL (Fin r) E) ^ 3 = 1 := congrArg Subtype.val h3
    have h3mat : (((hφ xA : GL (Fin r) E)) : Matrix (Fin r) (Fin r) E) ^ 3 = 1 := by
      have := congrArg (fun g : GL (Fin r) E => (g : Matrix (Fin r) (Fin r) E)) h3GL
      simpa using this
    have hcmat : (((hφ xA : GL (Fin r) E)) : Matrix (Fin r) (Fin r) E) =
        Matrix.scalar (Fin r) c := by
      rw [hc]
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar, Matrix.one_apply, h]
    haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
    have hscal : (Matrix.scalar (Fin r) c) ^ 3 = 1 := by
      rw [← hcmat]
      exact h3mat
    have hmat' : Matrix.scalar (Fin r) (c ^ 3) = Matrix.scalar (Fin r) (1 : E) := by
      rw [map_pow, hscal, map_one]
    exact (Matrix.scalar_inj (n := Fin r)).mp hmat'
  have hc_ne : c ≠ 1 := by
    intro h
    apply hx1
    have h1 : hφ xA = 1 := by
      apply Subtype.ext
      apply Units.ext
      change ((hφ xA : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1
      rw [hc, h, one_smul]
    have h2 : xA = 1 := hφ.injective (by simpa using h1)
    exact congrArg Subtype.val h2
  have hcgu : τ c * c = 1 := by
    have hgu := CFSG.LieType.SemisimpleCentralizers.Held.mem_heldGU.mp (hφ xA).2
    rw [show ((hφ xA : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = c • 1 from hc] at hgu
    let i : Fin r := ⟨0, by omega⟩
    have he := congrFun (congrFun hgu i) i
    simp [Matrix.smul_one_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] at he
    exact he
  have hcK1 : c ^ (Nat.card K + 1) = 1 := by
    rw [pow_succ, ← hτQ c]
    exact hcgu
  have h3not : ¬ 3 ∣ Nat.card K - 1 := by
    intro h3
    obtain ⟨t, ht⟩ := h3
    have hKpos : 1 ≤ Nat.card K := le_of_lt (Finite.one_lt_card (α := K))
    have hpow : c ^ (Nat.card K + 1) = c ^ 2 := by
      rw [show Nat.card K + 1 = 3 * t + 2 by omega, pow_add, pow_mul, hc3, one_pow, one_mul]
    have hc2 : c ^ 2 = 1 := by rw [← hpow]; exact hcK1
    have hc1 : c = 1 := by
      have hc3' : c ^ 3 = c ^ 2 * c := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
      calc c = c ^ 2 * c := by rw [hc2, one_mul]
        _ = c ^ 3 := hc3'.symm
        _ = 1 := hc3
    exact hc_ne hc1
  have hxJ : 3 ∣ r → proj m K x ∈ J := by
    intro h3r
    have hdetE : c ^ r = 1 := by
      obtain ⟨t, rfl⟩ := h3r
      rw [pow_mul, hc3, one_pow]
    have hdet : Matrix.GeneralLinearGroup.det ((hφ xA : GL (Fin r) E)) = 1 :=
      Units.ext (by rw [hφdet, hdetE]; rfl)
    have hxSU : ((hφ xA : GL (Fin r) E)) ∈ heldSU r E τ hτ := by
      rw [heldSU, Subgroup.mem_inf]
      refine ⟨(hφ xA).2, ?_⟩
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
      have := congrArg Units.val hdet
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    have hxM : x ∈ ⁅A₂, A₂⁆ := by
      rw [mem_commutator_subtype_iff hx2, mem_commutator_iff_map hφ]
      exact (mem_commutator_subtype_iff (hφ xA).2).1 (by rw [hcomm_eq]; exact hxSU)
    rw [hJeq]
    exact Subgroup.mem_map_of_mem _ hxM
  obtain ⟨eSUZ⟩ := Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eM
  have hr4 : Nat.card K = 2 → 4 ≤ r := by
    intro hK2
    by_contra hlt
    exact hbad ⟨by omega, hK2⟩
  refine Or.inr (Or.inl ⟨r, E, inferInstance, inferInstance, τ, hτ, hr2, h3not, hr4, ?_, ?_,
    ⟨eZ.symm.trans eSUZ⟩, hxJ⟩)
  · intro y
    rw [hτQ, hK]
  · rw [hEc, hK, ← pow_mul, show n * 2 = 2 * n by omega]
theorem k1419ClsSympBlock_sized {K : Type} [Field K] [Finite K] {n m : ℕ} (hK : Nat.card K = 2 ^ n)
    (x : StatedSp m K) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x)))) :
    (∃ a : ℕ, 2 ≤ a ∧ (3 ∣ Nat.card K - 1 ∨ (a = 2 ∧ 4 ≤ Nat.card K)) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL a K)) ∧
        (3 ∣ a → proj m K x ∈ J) ∧
        (a = 2 → (∀ Q : Subgroup (StatedProj (StatedSp m K)),
            CFSG.Open.IsComponentOf Q (fixSubgroup (MulAut.conj (proj m K x))) → Q = J) →
          ∀ E : Subgroup (StatedSp m K), E ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)) →
            CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)) ∨
    (∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E) (hτ : ∀ y, τ (τ y) = y),
        2 ≤ a ∧ ¬ 3 ∣ Nat.card K - 1 ∧ (Nat.card K = 2 → 4 ≤ a) ∧ (∀ y, τ y = y ^ Nat.card K) ∧
        Nat.card E = Nat.card K ^ 2 ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ)) ∧
        (3 ∣ a → proj m K x ∈ J)) ∨
    (∃ s : ℕ, 2 ≤ s ∧ ¬ (s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp s K))) ∨
    (Nat.card K = 2 ∧ Nat.card (↥J ⧸ Subgroup.center ↥J) = 360) := by
  classical
  haveI hchar : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [Fintype.card_eq_nat_card, hK])
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    have h1 : Nat.card K = 1 := by simpa using hK
    have := Finite.one_lt_card (α := K)
    omega
  have hm : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst hm0
    have hcard : Nat.card (StatedSp 0 K) = 1 := by
      rw [SymplecticFlag.card_statedSp]
      simp
    haveI : Subsingleton (StatedSp 0 K) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact hx1 (Subsingleton.elim x 1)
  obtain ⟨A₁, A₂, hcomm, hjoin, hx2, ⟨s, hsφ⟩, hA2⟩ := k1419ClsSympCent hK hn hm x hx hx1
  let F : Fin 2 → Subgroup (StatedSp m K) := ![A₁, A₂]
  have hF0 : F 0 = A₁ := by simp [F]
  have hF1 : F 1 = A₂ := by simp [F]
  have hc : ∀ i j, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, Commute a b := by
    intro i j hij a ha b hb
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm a (by simpa [F] using ha) b (by simpa [F] using hb)
    · exact (hcomm b (by simpa [F] using hb) a (by simpa [F] using ha)).symm
    · exact absurd rfl hij
  have hjoinF : ⨆ i, F i = Subgroup.centralizer ({x} : Set (StatedSp m K)) := by
    have h2 : (⨆ i : Fin 2, F i) = F 0 ⊔ F 1 := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup F 0) (le_iSup F 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    rw [h2, hF0, hF1, hjoin]
  have htame : ∀ i, CFSG.IsQuasisimple ↥⁅F i, F i⁆ ∨ Group.IsSolvable ↥(F i) := by
    intro i
    fin_cases i
    · rcases Nat.eq_zero_or_pos s with hs0 | hs1
      · right
        haveI : Subsingleton ↥A₁ := by
          have hcard : Nat.card ↥A₁ = 1 := by
            rw [Nat.card_congr hsφ.some.toEquiv, hs0, SymplecticFlag.card_statedSp]
            simp
          exact (Nat.card_eq_one_iff_unique.mp hcard).1
        haveI : Group.IsSolvable ↥A₁ := inferInstance
        exact hF0.symm ▸ (inferInstance : Group.IsSolvable ↥A₁)
      · exact (tame_of_mulEquiv_statedSp hs1 hsφ.some).imp (fun h => hF0.symm ▸ h) (fun h => hF0.symm ▸ h)
    · rcases hA2 with ⟨r, hr, ⟨eGL⟩⟩ | ⟨r, E, hEf, hEfin, τ, hτ, hr, hEc, hτQ, ⟨eGU⟩⟩
      · exact (tame_of_mulEquiv_gl (r := r) eGL).imp (fun h => hF1.symm ▸ h) (fun h => hF1.symm ▸ h)
      · exact (tame_of_mulEquiv_heldGU hK hn hEc hτQ eGU).imp (fun h => hF1.symm ▸ h) (fun h => hF1.symm ▸ h)
  have hZc : (proj m K).ker ≤ Subgroup.center (StatedSp m K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hJcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x))) := hJ
  obtain ⟨i, hQ, hJeq⟩ := components_conj_of_orbit_family (proj m K)
    SymplecticHigher.proj_surjective hZc x F hc hjoinF htame J hJcomp
  fin_cases i
  · simp [F] at hQ hJeq
    rcases Nat.eq_zero_or_pos s with hs0 | hs1
    · exfalso
      haveI : Subsingleton ↥A₁ := by
        have hcard : Nat.card ↥A₁ = 1 := by
          rw [Nat.card_congr hsφ.some.toEquiv, hs0, SymplecticFlag.card_statedSp]
          simp
        exact (Nat.card_eq_one_iff_unique.mp hcard).1
      haveI hMsub : Subsingleton ↥⁅A₁, A₁⁆ :=
        (Subgroup.inclusion_injective (commutator_le_self' A₁)).subsingleton
      haveI : Subsingleton (↥⁅A₁, A₁⁆ ⧸ Subgroup.center ↥⁅A₁, A₁⁆) := inferInstance
      haveI : Nontrivial (↥⁅A₁, A₁⁆ ⧸ Subgroup.center ↥⁅A₁, A₁⁆) := hQ.2.1.toNontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥⁅A₁, A₁⁆ ⧸ Subgroup.center ↥⁅A₁, A₁⁆)
      exact hab (Subsingleton.elim a b)
    · exact a1_branch hK hchar hm hx hJ (A₁ := A₁) (A₂ := A₂) hcomm hjoin hs1 hsφ.some
        hQ hA2 hJeq
  · simp [F] at hQ hJeq
    rcases hA2 with ⟨r, hr, ⟨eGL⟩⟩ | ⟨r, E, hEf, hEfin, τ, hτ, hr, hEc, hτQ, ⟨eGU⟩⟩
    · exact gl_branch hK hchar hm hx hx1 hJ (A₁ := A₁) (A₂ := A₂) hcomm hjoin hx2
        eGL hQ hJeq hsφ.some
    · exact gu_branch hK hn hchar hm hx hx1 hJ (A₁ := A₁) (A₂ := A₂) hjoin hx2
        hEc hτQ eGU hQ hJeq

theorem k1419ClsSympBlock {K : Type} [Field K] [Finite K] {n m : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (x : StatedSp m K) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj (proj m K x))) J) :
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
        Nonempty (PSimple 3 J ≃* StatedProj (StatedSL a E)) ∧ (3 ∣ a → proj m K x ∈ J)) ∨
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
        (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ 2 ^ k) ∧ Nat.card E = (2 ^ k) ^ 2 ∧
        Nonempty (PSimple 3 J ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ)) ∧
        (3 ∣ a → proj m K x ∈ J)) ∨
    (∃ s : ℕ, 2 ≤ s ∧ ¬ (s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (PSimple 3 J ≃* StatedProj (StatedSp s K))) ∨
    (Nat.card K = 2 ∧ Nat.card (PSimple 3 J) ≤ 720) := by
  classical
  haveI hchar : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [Fintype.card_eq_nat_card, hK])
  have hPIL : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer (MulAut.conj (proj m K x)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_sp
      Nat.prime_two hn hK hm Nat.prime_three (by norm_num) (by norm_num) x hx
  have hperfJ := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle := hPIL J hJ.1 hperfJ
  obtain ⟨hcomp, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hJle
  obtain ⟨eP⟩ := centerQuot_equiv_pSimple_of_component hJ hcomp
  rcases k1419ClsSympBlock_sized hK x hx hx1 hcomp with
    ⟨a, ha2, hcond, ⟨eSL⟩, hxJ, hrank⟩ |
    ⟨a, E, hEf, hEfin, τ, hτ, ha2, h3, h4, hτQ, hEc, ⟨eSU⟩, hxJ⟩ |
    ⟨s, hs2, hne, ⟨eSp⟩⟩ |
    ⟨hK2, hcard⟩
  · exact Or.inl ⟨a, n, K, inferInstance, inferInstance, ha2, hK, ⟨eP.symm.trans eSL⟩, hxJ⟩
  · refine Or.inr (Or.inl ⟨a, n, E, hEf, hEfin, τ, hτ, ha2, ?_, ?_,
      ⟨eP.symm.trans eSU⟩, hxJ⟩)
    · intro y
      rw [hτQ y, hK]
    · rw [hEc, hK]
  · exact Or.inr (Or.inr (Or.inl ⟨s, hs2, hne, ⟨eP.symm.trans eSp⟩⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨hK2, ?_⟩))
    have h360 : Nat.card (PSimple 3 J) = 360 := by
      calc Nat.card (PSimple 3 J) = Nat.card (↥J ⧸ Subgroup.center ↥J) :=
            (Nat.card_congr eP.toEquiv).symm
        _ = 360 := hcard
    omega

end CFSG.LocalAnalysis.GLTheoremA.K1419
