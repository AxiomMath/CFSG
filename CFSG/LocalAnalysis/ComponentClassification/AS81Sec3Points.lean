module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Points
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Kernel
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Root
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Centr
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.AS81AffinePlane
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull (outerAutomorphismGroup)

namespace G2

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem conj_conj {M : Type*} [Group M] {l₁ l₂ v v' v'' : M} (h₂ : l₂ * v * l₂⁻¹ = v')
    (h₁ : l₁ * v' * l₁⁻¹ = v'') : (l₁ * l₂) * v * (l₁ * l₂)⁻¹ = v'' := by
  rw [← h₁, ← h₂]
  group

theorem exists_conj_eq_g2N_c
    {y z : K} (h : y ≠ 0 ∨ z ≠ 0) :
    ∃ l ∈ g2RankOne K g2ia, l * g2N 0 0 0 0 y z * l⁻¹ = g2N 0 0 0 0 0 1 := by
  have htor : ∀ w : K, w ≠ 0 → ∃ l ∈ g2RankOne K g2ia,
      l * g2N 0 0 0 0 0 w * l⁻¹ = g2N 0 0 0 0 0 1 := by
    intro w hw
    refine ⟨torusElt .G2 K g2ia (Units.mk0 w hw)⁻¹, torusElt_mem_g2RankOne g2ia _, ?_⟩
    have h1 := (actsOnShort_torusElt_a (K := K) (Units.mk0 w hw)⁻¹).2.2 ![0, w]
    refine h1.trans (g2N_eq_g2N rfl rfl rfl rfl ?_ ?_)
    · simp [shDiag]
    · simp [shDiag, hw]
  by_cases hy : y = 0
  · subst hy
    exact htor z (h.resolve_left (not_not.mpr rfl))
  obtain ⟨l, hl, hl1⟩ := htor y hy
  have h1 := (actsOnShort_pinnedX_a (K := K) (z / y)).2.2 ![y, z]
  have h2 := (actsOnShort_weylElt_a (K := K)).2.2 ![y, 0]
  have e1 : X g2a (z / y) * g2N 0 0 0 0 y z * (X g2a (z / y))⁻¹ = g2N 0 0 0 0 y 0 := by
    refine h1.trans (g2N_eq_g2N rfl rfl rfl rfl ?_ ?_)
    · simp [shMa]
    · simp only [shMa, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [mul_div_cancel₀ z hy]
      exact CharTwo.add_self_eq_zero z
  have e2 : weylElt .G2 K g2ia 1 * g2N 0 0 0 0 y 0 * (weylElt .G2 K g2ia 1)⁻¹ =
      g2N 0 0 0 0 0 y := by
    refine h2.trans (g2N_eq_g2N rfl rfl rfl rfl ?_ ?_) <;> simp [shSwap]
  refine ⟨l * (weylElt .G2 K g2ia 1 * X g2a (z / y)),
    mul_mem hl (mul_mem (weylElt_mem_g2RankOne g2ia 1) ?_), ?_⟩
  · rw [← xUnit_g2ia]
    exact xUnit_mem_g2RankOne g2ia _
  · exact conj_conj (conj_conj e1 e2) hl1

theorem exists_conj_eq_of_mem_g2BCGroup
    {w w' : ModGL .G2 K} (hw : w ∈ g2BCGroup K) (hw' : w' ∈ g2BCGroup K) (h1 : w ≠ 1)
    (h1' : w' ≠ 1) : ∃ l ∈ g2RankOne K g2ia, l * w * l⁻¹ = w' := by
  have key : ∀ {w : ModGL .G2 K}, w ∈ g2BCGroup K → w ≠ 1 →
      ∃ l ∈ g2RankOne K g2ia, l * w * l⁻¹ = g2N 0 0 0 0 0 1 := by
    rintro _ ⟨y, z, rfl⟩ hne
    refine exists_conj_eq_g2N_c ?_
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hne g2N_zero
  obtain ⟨l, hl, hlw⟩ := key hw h1
  obtain ⟨l', hl', hlw'⟩ := key hw' h1'
  refine ⟨l'⁻¹ * l, mul_mem (inv_mem hl') hl, ?_⟩
  rw [show (l'⁻¹ * l) * w * (l'⁻¹ * l)⁻¹ = l'⁻¹ * (l * w * l⁻¹) * l' by group, hlw, ← hlw']
  group

end G2

namespace Sec3Model

variable
  {G : Type} [Group G] {A A₁ E F : Subgroup G} {x : G} {K : Type} [Field K] [CharP K 2]
  {f : ↥(adjointGroup .G2 K) →* G}

@[expose] noncomputable def equivA (hM : Sec3Model G A A₁ E F x K f) :
    ↥(adjointGroup .G2 K) ≃* ↥A :=
  (MonoidHom.ofInjective hM.inj).trans (MulEquiv.subgroupCongr hM.range_eq)

theorem coe_equivA (hM : Sec3Model G A A₁ E F x K f) (c : ↥(adjointGroup .G2 K)) :
    (hM.equivA c : G) = f c :=
  rfl

theorem coe_equivA_symm (hM : Sec3Model G A A₁ E F x K f) (a : ↥A) :
    f (hM.equivA.symm a) = a := by
  rw [← coe_equivA hM, MulEquiv.apply_symm_apply]

@[expose] noncomputable def act (hM : Sec3Model G A A₁ E F x K f) :
    normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K) :=
  (MulAut.congr hM.equivA.symm).toMonoidHom.comp A.normalizerMonoidHom

theorem act_of_mem (hM : Sec3Model G A A₁ E F x K f) {a : G} (ha : a ∈ A) :
    hM.act ⟨a, le_normalizer ha⟩ = MulAut.conj (hM.equivA.symm ⟨a, ha⟩) := by
  refine MulEquiv.ext fun c => hM.inj ?_
  change f (hM.equivA.symm (A.normalizerMonoidHom ⟨a, le_normalizer ha⟩ (hM.equivA c))) =
    f (hM.equivA.symm ⟨a, ha⟩ * c * (hM.equivA.symm ⟨a, ha⟩)⁻¹)
  rw [coe_equivA_symm, map_mul, map_mul, map_inv, coe_equivA_symm]
  rfl

theorem isActionHom_act (hM : Sec3Model G A A₁ E F x K f) :
    IsActionHom A (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range
      hM.act := by
  refine ⟨fun a ha => ?_, fun y hy => ?_, fun n => ?_⟩
  · rw [act_of_mem hM ha]
    exact ⟨_, rfl⟩
  · obtain ⟨c, rfl⟩ := hy
    have hc : f c ∈ A := by
      rw [← hM.range_eq]
      exact ⟨c, rfl⟩
    refine ⟨f c, hc, ?_⟩
    rw [act_of_mem hM hc]
    congr 1
    exact hM.equivA.symm_apply_eq.mpr (Subtype.ext rfl)
  · have h1 : hM.act n = 1 ↔ A.normalizerMonoidHom n = 1 := by
      change (MulAut.congr hM.equivA.symm) (A.normalizerMonoidHom n) = 1 ↔ _
      exact MulEquiv.map_eq_one_iff _
    rw [h1, ← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf]

end Sec3Model

end CFSG.ComponentClassification.AS81
