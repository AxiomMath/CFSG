module

public import CFSG.FeitThompson.Representations.PrimeInvariantCharsInnerKernel
import CFSG.FeitThompson.Representations.FixedDegreeCharacterSumVanishing
import CFSG.FeitThompson.Representations.FixedPointFreeActsFreelyOnLinearChars
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
public import CFSG.FeitThompson.OddOrder.TypeIIIVCoreAbelianizationBound
public import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Local.TypeIIHallCoreElementaryAbelian
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
public import CFSG.FeitThompson.OddOrder.PConfigChiefFactorLinearModel
import CFSG.FeitThompson.Representations.PTypeChiefCoreFamilyCoherentSupport
public import CFSG.FeitThompson.Representations.ReducibleChiefModelEqualDegreePair
public import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
public import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Std.Tactic.BVDecide.Normalize.Prop

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

def charConj {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (w : E) (χ : K → ℂ) : K → ℂ :=
  χ ∘ conjOnNormalized K hEN w⁻¹

theorem charConj_apply {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (w : E) (χ : K → ℂ)
    {x y : K} (h : (y : G) = (w : G)⁻¹ * (x : G) * (w : G)) : charConj hEN w χ x = χ y := by
  refine congrArg χ (Subtype.ext ?_)
  rw [conjOnNormalized_apply_coe, h]
  simp only [Subgroup.coe_inv, inv_inv]

@[simp] theorem charConj_apply_one {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (w : E)
    (χ : K → ℂ) : charConj hEN w χ 1 = χ 1 :=
  charConj_apply hEN w χ (by simp)

@[simp] theorem charConj_one {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (χ : K → ℂ) :
    charConj hEN 1 χ = χ := by
  funext x
  exact charConj_apply hEN _ _ (y := x) (by simp)

theorem charConj_mul {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (v w : E) (χ : K → ℂ) :
    charConj hEN (v * w) χ = charConj hEN v (charConj hEN w χ) := by
  funext x
  change χ (conjOnNormalized K hEN (v * w)⁻¹ x)
    = χ (conjOnNormalized K hEN w⁻¹ (conjOnNormalized K hEN v⁻¹ x))
  rw [mul_inv_rev, map_mul]
  rfl

theorem charConj_mem_Irr [Finite G] {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (w : E)
    {χ : K → ℂ} (hχ : χ ∈ Irr K) : charConj hEN w χ ∈ Irr K :=
  mem_Irr_comp_mulAut hχ _

theorem mem_charValueKernel_charConj {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (w : E)
    (χ : K → ℂ) {x y : K} (h : (y : G) = (w : G)⁻¹ * (x : G) * (w : G)) :
    x ∈ charValueKernel (charConj hEN w χ) ↔ y ∈ charValueKernel χ := by
  rw [mem_charValueKernel, mem_charValueKernel, charConj_apply hEN w χ h, charConj_apply_one]

theorem charConj_eq_comp_conjOnNormalized {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G))
    (w : E) (χ : K → ℂ) (x : K) : charConj hEN w χ x = χ (conjOnNormalized K hEN w⁻¹ x) := by
  refine charConj_apply hEN w χ ?_
  rw [conjOnNormalized_apply_coe]
  simp only [Subgroup.coe_inv, inv_inv]

theorem charConj_eq_self_iff_forall {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (w : E)
    (χ : K → ℂ) :
    charConj hEN w χ = χ ↔ ∀ x : K, χ (conjOnNormalized K hEN w⁻¹ x) = χ x := by
  refine ⟨fun h x => ?_, fun h => funext fun x => ?_⟩
  · have hx := congrFun h x
    rwa [charConj_eq_comp_conjOnNormalized] at hx
  · rw [charConj_eq_comp_conjOnNormalized]
    exact h x

theorem charConj_eq_iff {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (χ : K → ℂ)
    (v w : E) : charConj hEN v χ = charConj hEN w χ ↔ charConj hEN (w⁻¹ * v) χ = χ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [charConj_mul, h, ← charConj_mul, inv_mul_cancel, charConj_one]
  · have h2 : charConj hEN w (charConj hEN (w⁻¹ * v) χ) = charConj hEN w χ := by rw [h]
    rwa [← charConj_mul, mul_inv_cancel_left] at h2

theorem charConj_inv_eq_self {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) {χ : K → ℂ}
    {w : E} (hw : charConj hEN w χ = χ) : charConj hEN w⁻¹ χ = χ := by
  have h := (charConj_eq_iff hEN χ 1 w).1 (by rw [charConj_one, hw])
  rwa [mul_one] at h

def charConjStabilizer {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G)) (χ : K → ℂ) :
    Subgroup E where
  carrier := {w | charConj hEN w χ = χ}
  one_mem' := charConj_one hEN χ
  mul_mem' {v w} hv hw := by
    change charConj hEN (v * w) χ = χ
    rw [charConj_mul, show charConj hEN w χ = χ from hw, show charConj hEN v χ = χ from hv]
  inv_mem' {w} hw := charConj_inv_eq_self hEN hw

@[simp] theorem mem_charConjStabilizer {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G))
    {χ : K → ℂ} {w : E} : w ∈ charConjStabilizer hEN χ ↔ charConj hEN w χ = χ := Iff.rfl

theorem charConj_injective_iff [Finite G] {K E : Subgroup G} (hEN : E ≤ normalizer (K : Set G))
    (χ : K → ℂ) :
    (Function.Injective fun w : E => charConj hEN w χ) ↔ charConjStabilizer hEN χ = ⊥ := by
  refine ⟨fun hinj => le_antisymm (fun w hw => ?_) bot_le, fun hbot v w hvw => ?_⟩
  · refine Subgroup.mem_bot.2 (hinj ?_)
    change charConj hEN w χ = charConj hEN 1 χ
    rw [(mem_charConjStabilizer hEN).1 hw, charConj_one]
  · have h : w⁻¹ * v ∈ charConjStabilizer hEN χ :=
      (mem_charConjStabilizer hEN).2 ((charConj_eq_iff hEN χ v w).1 hvw)
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h
    exact h.symm

theorem forall_charConj_eq_of_charConj_eq [Finite G] {K E : Subgroup G}
    (hEN : E ≤ normalizer (K : Set G)) (hE : (Nat.card E).Prime) {χ : K → ℂ} {w : E}
    (hw1 : w ≠ 1) (hw : charConj hEN w χ = χ) (v : E) : charConj hEN v χ = χ := by
  have hne : charConjStabilizer hEN χ ≠ ⊥ := fun hbot =>
    hw1 (Subgroup.mem_bot.1 (hbot ▸ (mem_charConjStabilizer hEN).2 hw))
  have htop : charConjStabilizer hEN χ = ⊤ := by
    rcases hE.eq_one_or_self_of_dvd _
      (Subgroup.card_subgroup_dvd_card (charConjStabilizer hEN χ)) with hone | hcard
    · exact absurd (Subgroup.card_eq_one.1 hone) hne
    · exact Subgroup.eq_top_of_card_eq _ hcard
  exact (mem_charConjStabilizer hEN).1 (htop ▸ Subgroup.mem_top v)

theorem isCyclic_of_le_of_isCyclic {X : Type*} [Group X] {A B : Subgroup X} (hAB : A ≤ B)
    (hB : IsCyclic B) : IsCyclic A := by
  have : IsCyclic (A.subgroupOf B) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAB)
    (Subgroup.subgroupOfEquivOfLe hAB).surjective

theorem isCyclic_subgroupOf {X : Type*} [Group X] {A B : Subgroup X} (h : A ≤ B)
    (hA : IsCyclic A) : IsCyclic (A.subgroupOf B) :=
  isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h).symm
    (Subgroup.subgroupOfEquivOfLe h).symm.surjective

theorem IsFrobeniusType.inf_centralizer_eq_bot_of_isCyclic {X : Type*} [Group X] [Finite X]
    {E : Subgroup X} (h : IsFrobeniusType X E) (hcyc : IsCyclic E) {e : X} (he : e ∈ E)
    (he1 : e ≠ 1) : hallCore X ⊓ centralizer {e} = ⊥ := by
  obtain ⟨E₀, hE₀E, hexp, hcent⟩ := h.exists_exponent_eq
  have hcyc₀ : IsCyclic E₀ := isCyclic_of_le_of_isCyclic hE₀E hcyc
  have hcard : Nat.card E ≤ Nat.card E₀ := by
    rw [← hcyc₀.exponent_eq_card, ← hcyc.exponent_eq_card] at *
    exact hexp.ge
  exact hcent e (Subgroup.eq_of_le_of_card_ge hE₀E hcard ▸ he) he1

theorem inf_centralizer_map_subtype_eq_bot {K : Subgroup G} {A : Subgroup K} {u : G} (hu : u ∈ K)
    (h : A ⊓ centralizer {(⟨u, hu⟩ : K)} = ⊥) : A.map K.subtype ⊓ centralizer {u} = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxc⟩
  obtain ⟨y, hyA, rfl⟩ := hxA
  have hxc' : (y : G) * u = u * (y : G) :=
    Subgroup.mem_centralizer_singleton_iff.1 (by simpa using hxc)
  have hy : y ∈ A ⊓ centralizer {(⟨u, hu⟩ : K)} :=
    ⟨hyA, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hxc')⟩
  rw [h] at hy
  simp only [Subgroup.mem_bot] at hy
  simp [hy]

variable [Finite G] {M U W₁ W₂ : Subgroup G}

def HasEqualDegreeCharacterPair {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) : Prop :=
  ∃ α ∈ Irr (⁅M, M⁆ : Subgroup G), ∃ β ∈ Irr (⁅M, M⁆ : Subgroup G),
    α 1 = β 1 ∧
    (∃ x : ↥(⁅M, M⁆ : Subgroup G),
      (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel α) ∧
    (∃ x : ↥(⁅M, M⁆ : Subgroup G),
      (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel β) ∧
    (∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w α = α) ∧
    Function.Injective fun w : W₁ => charConj hc.le_normalizer_commutator_W₁ w β

theorem hasEqualDegreeCharacterPair_iff (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    HasEqualDegreeCharacterPair hc ↔
      ∃ α ∈ Irr (⁅M, M⁆ : Subgroup G), ∃ β ∈ Irr (⁅M, M⁆ : Subgroup G),
        α 1 = β 1 ∧
        (∃ x : ↥(⁅M, M⁆ : Subgroup G),
          (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel α) ∧
        (∃ x : ↥(⁅M, M⁆ : Subgroup G),
          (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel β) ∧
        (∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w α = α) ∧
        Function.Injective fun w : W₁ => charConj hc.le_normalizer_commutator_W₁ w β :=
  Iff.rfl

theorem IsTypeII.inf_centralizer_hallCore_eq_bot_of_isCyclic (h : IsTypeII M)
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUcyc : IsCyclic U)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    (hallCore M).map M.subtype ⊓ centralizer {u} = ⊥ := by
  obtain ⟨-, -, -, -, hfrob, hhall⟩ := h.clauses_of_isWitnessedPConfiguration hsolv hc
  have hUK : U ≤ (⁅M, M⁆ : Subgroup G) := hc.le_commutator_E
  have hmem : (⟨u, hUK hu⟩ : ↥(⁅M, M⁆ : Subgroup G)) ∈ U.subgroupOf _ := by
    simpa [Subgroup.mem_subgroupOf] using hu
  have hbot := hfrob.inf_centralizer_eq_bot_of_isCyclic (isCyclic_subgroupOf hUK hUcyc) hmem
    (fun hcon => hu1 (by simpa [Subtype.ext_iff] using hcon))
  rw [← hhall]
  exact inf_centralizer_map_subtype_eq_bot (hUK hu) hbot

theorem IsWitnessedPConfiguration.not_natCard_W₁_dvd_natCard_commutator (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ¬ (Nat.card W₁) ∣ Nat.card (⁅M, M⁆ : Subgroup G) := by
  have h := hc.hall_W₁
  rw [hc.relIndex_W₁_eq_natCard_commutator] at h
  intro hd
  have h2 := Nat.eq_one_of_dvd_coprimes h (dvd_refl _) hd
  have h1 : 1 < Nat.card W₁ := Subgroup.one_lt_card_iff_ne_bot W₁ |>.2 hc.ne_bot_W₁
  omega

theorem conjOnNormalized_pow_natCard_eq_one (hc : IsWitnessedPConfiguration M U W₁ W₂) (w : W₁) :
    (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w) ^ Nat.card W₁ = 1 := by
  rw [← map_pow, show w ^ Nat.card (W₁ : Subgroup G) = 1 from pow_card_eq_one', map_one]

theorem conjOnNormalized_eq_self_iff (hc : IsWitnessedPConfiguration M U W₁ W₂) (w : W₁)
    (x : ↥(⁅M, M⁆ : Subgroup G)) :
    conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x = x ↔
      (x : G) ∈ (⁅M, M⁆ : Subgroup G) ⊓ centralizer {(w : G)} := by
  refine ⟨fun hx => ?_, fun hcent => Subtype.ext ?_⟩
  · have h1 : (w : G) * (x : G) * (w : G)⁻¹ = (x : G) := by
      have hx' := congrArg (fun y : ↥(⁅M, M⁆ : Subgroup G) => (y : G)) hx
      rwa [conjOnNormalized_apply_coe] at hx'
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (x : G) * (w : G) = ((w : G) * (x : G) * (w : G)⁻¹) * (w : G) := by rw [h1]
      _ = (w : G) * (x : G) := by group
  · rw [conjOnNormalized_apply_coe,
      ← Subgroup.mem_centralizer_singleton_iff.1 hcent.2]
    group

theorem autFixedSubgroup_conjOnNormalized_eq (hc : IsWitnessedPConfiguration M U W₁ W₂) {w : W₁}
    (hw1 : w ≠ 1) :
    autFixedSubgroup (conjOnNormalized (⁅M, M⁆ : Subgroup G)
      hc.le_normalizer_commutator_W₁ w) = W₂.subgroupOf (⁅M, M⁆ : Subgroup G) := by
  ext x
  rw [mem_autFixedSubgroup, Subgroup.mem_subgroupOf, conjOnNormalized_eq_self_iff hc w x,
    hc.inf_centralizer_eq_W₂ (w : G) w.2 fun hcon => hw1 (Subtype.ext hcon)]

theorem natCard_fixed_irrAut_conjOnNormalized_eq (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {w : W₁} (hw1 : w ≠ 1) :
    Nat.card {χ : Irr ↥(⁅M, M⁆ : Subgroup G) //
      irrAut (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w) χ = χ}
      = Nat.card W₂ := by
  have hW₂K : W₂ ≤ (⁅M, M⁆ : Subgroup G) := hc.le_hallCore_W₂.trans hc.hallCore_le_commutator
  have hcyc : IsCyclic ↥(W₂.subgroupOf (⁅M, M⁆ : Subgroup G)) :=
    isCyclic_subgroupOf hW₂K hc.isCyclic_W₂
  rw [natCard_fixed_Irr_eq_natCard_conjClasses_autFixed hprime (IsWitnessedPConfiguration.not_natCard_W₁_dvd_natCard_commutator hc)
      (conjOnNormalized_pow_natCard_eq_one hc w),
    autFixedSubgroup_conjOnNormalized_eq hc hw1,
    natCard_conjClasses_eq_natCard_of_comm fun x y => mul_comm' x y]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₂K).toEquiv

theorem mapsTo_subgroupOf_hallCore (hc : IsWitnessedPConfiguration M U W₁ W₂) (w : W₁) :
    ∀ x ∈ ((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G),
      conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x ∈
        ((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [conjOnNormalized_apply_coe]
  exact (Subgroup.mem_normalizer_iff.1
    (le_normalizer_map_subtype_hallCore M (hc.le_M_W₁ w.2)) (x : G)).1 hx

theorem mapsTo_subgroupOf_E (hc : IsWitnessedPConfiguration M U W₁ W₂) (w : W₁) :
    ∀ x ∈ U.subgroupOf (⁅M, M⁆ : Subgroup G),
      conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x ∈
        U.subgroupOf (⁅M, M⁆ : Subgroup G) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [conjOnNormalized_apply_coe]
  exact (Subgroup.mem_normalizer_iff.1 (hc.le_normalizer_E w.2) (x : G)).1 hx

theorem eq_one_of_conjOnNormalized_eq_self_of_mem_E (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {w : W₁} (hw1 : w ≠ 1) :
    ∀ u ∈ U.subgroupOf (⁅M, M⁆ : Subgroup G),
      conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w u = u → u = 1 := by
  intro u hu hfix
  rw [Subgroup.mem_subgroupOf] at hu
  have hW₂ : (u : G) ∈ W₂ := by
    rw [← hc.inf_centralizer_eq_W₂ (w : G) w.2 fun hcon => hw1 (Subtype.ext hcon)]
    exact (conjOnNormalized_eq_self_iff hc w u).1 hfix
  exact Subtype.ext (Subgroup.disjoint_def.1 hc.disjoint_hallCore_E (hc.le_hallCore_W₂ hW₂) hu)

theorem exists_notMem_charValueKernel_of_conjOnNormalized_invariant
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime) {w : W₁}
    (hw1 : w ≠ 1) {θ : ↥(⁅M, M⁆ : Subgroup G) → ℂ} (hθ : θ ∈ Irr ↥(⁅M, M⁆ : Subgroup G))
    (hθ1 : θ ≠ 1) (hθfix : ∀ x : ↥(⁅M, M⁆ : Subgroup G),
      θ (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x) = θ x) :
    ∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
      x ∉ charValueKernel θ := by
  have _ : (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hc.hallCore_le_commutator).2
      (commutator_le_normalizer_hallCore M)
  have h := not_subset_charValueKernel_of_fixed_of_ne_one
    (E := ((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
    (U := U.subgroupOf (⁅M, M⁆ : Subgroup G)) hprime (IsWitnessedPConfiguration.not_natCard_W₁_dvd_natCard_commutator hc)
    (conjOnNormalized_pow_natCard_eq_one hc w) hc.isComplement'_subgroupOf_hallCore_E
    (mapsTo_subgroupOf_hallCore hc w) (mapsTo_subgroupOf_E hc w)
    (eq_one_of_conjOnNormalized_eq_self_of_mem_E hc hw1) hθ hθfix hθ1
  rw [Set.not_subset] at h
  obtain ⟨x, hx, hnk⟩ := h
  exact ⟨x, Subgroup.mem_subgroupOf.1 hx, hnk⟩

theorem exists_invariant_mem_Irr_notMem_charValueKernel
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime) :
    ∃ α ∈ Irr (⁅M, M⁆ : Subgroup G), α ≠ 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel α) ∧
      ∀ v : W₁, charConj hc.le_normalizer_commutator_W₁ v α = α := by
  have hnt : Nontrivial W₁ := Subgroup.nontrivial_iff_ne_bot W₁ |>.2 hc.ne_bot_W₁
  obtain ⟨w, hw1⟩ := exists_ne (1 : W₁)
  set b := conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w with hbd
  set p₁ : {χ : Irr ↥(⁅M, M⁆ : Subgroup G) // irrAut b χ = χ} :=
    ⟨⟨1, one_mem_Irr⟩, (irrAut_eq_self_iff b _).2 fun _ => rfl⟩ with hp₁
  have hcard : Nat.card {χ : Irr ↥(⁅M, M⁆ : Subgroup G) // irrAut b χ = χ} ≠ 1 := by
    rw [natCard_fixed_irrAut_conjOnNormalized_eq hc hprime hw1]
    have h1 : 1 < Nat.card W₂ := Subgroup.one_lt_card_iff_ne_bot W₂ |>.2 hc.ne_bot_W₂
    omega
  have hne : ∃ s, s ≠ p₁ := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hcard (Nat.card_eq_one_iff_unique.2 ⟨⟨fun a c => (hcon a).trans (hcon c).symm⟩, ⟨p₁⟩⟩)
  obtain ⟨⟨⟨θ, hθ⟩, hθfix⟩, hθne⟩ := hne
  have hθ1 : θ ≠ 1 := fun hcon => hθne (by subst hcon; rfl)
  have hθinv : ∀ x : ↥(⁅M, M⁆ : Subgroup G), θ (b x) = θ x :=
    (irrAut_eq_self_iff b ⟨θ, hθ⟩).1 hθfix
  have hconj : charConj hc.le_normalizer_commutator_W₁ w⁻¹ θ = θ := by
    rw [charConj_eq_self_iff_forall]
    simpa [hbd] using hθinv
  refine ⟨θ, hθ, hθ1, exists_notMem_charValueKernel_of_conjOnNormalized_invariant hc hprime hw1
    hθ hθ1 hθinv, forall_charConj_eq_of_charConj_eq hc.le_normalizer_commutator_W₁ hprime
      (w := w⁻¹) (fun hcon => hw1 (by simpa using congrArg (·⁻¹) hcon)) hconj⟩

theorem hasEqualDegreeCharacterPair_of_exists_charConj_ne
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime)
    {α β : ↥(⁅M, M⁆ : Subgroup G) → ℂ} (hα : α ∈ Irr (⁅M, M⁆ : Subgroup G))
    (hβ : β ∈ Irr (⁅M, M⁆ : Subgroup G)) (hdeg : α 1 = β 1)
    (hdetα : ∃ x : ↥(⁅M, M⁆ : Subgroup G),
      (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel α)
    (hdetβ : ∃ x : ↥(⁅M, M⁆ : Subgroup G),
      (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel β)
    (hinvα : ∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w α = α)
    (hmovβ : ∃ w : W₁, charConj hc.le_normalizer_commutator_W₁ w β ≠ β) :
    HasEqualDegreeCharacterPair hc := by
  rw [hasEqualDegreeCharacterPair_iff]
  refine ⟨α, hα, β, hβ, hdeg, hdetα, hdetβ, hinvα, ?_⟩
  rw [charConj_injective_iff]
  obtain ⟨w, hw⟩ := hmovβ
  by_contra hne
  obtain ⟨v, hv, hv1⟩ :
      ∃ v : W₁, v ∈ charConjStabilizer hc.le_normalizer_commutator_W₁ β ∧ v ≠ 1 := by
    have hnt : Nontrivial (charConjStabilizer hc.le_normalizer_commutator_W₁ β) :=
      Subgroup.nontrivial_iff_ne_bot _ |>.2 hne
    obtain ⟨v, hv1⟩ := exists_ne (1 : charConjStabilizer hc.le_normalizer_commutator_W₁ β)
    exact ⟨v.1, v.2, fun hcon => hv1 (Subtype.ext hcon)⟩
  exact hw (forall_charConj_eq_of_charConj_eq hc.le_normalizer_commutator_W₁ hprime hv1
    ((mem_charConjStabilizer _).1 hv) w)

theorem exists_monoidHom_apply_ne_one_of_isMulCommutative {Q : Type*} [Group Q]
    [IsMulCommutative Q] [Finite Q] {g : Q} (hg : g ≠ 1) : ∃ ν : Q →* ℂˣ, (ν g : ℂ) ≠ 1 :=
  letI : CommGroup Q := { mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  exists_monoidHom_apply_ne_one hg

theorem eq_one_of_comp_aut_eq_of_fixedPointFree {Q : Type*} [Group Q] [IsMulCommutative Q]
    [Finite Q] {u : MulAut Q} (hu : MonoidHom.FixedPointFree u) {ν : Q →* ℂˣ}
    (hν : ν.comp (u : Q →* Q) = ν) : ν = 1 := by
  letI : CommGroup Q := { mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  have h : linearCharFun ν = 1 := by
    refine eq_one_of_forall_apply_aut_eq hu (linearCharFun_mem_Irr ν) fun x => ?_
    rw [linearCharFun_apply, linearCharFun_apply]
    exact congrArg (fun (f : Q →* ℂˣ) => (f x : ℂ)) hν
  ext x
  have h2 : linearCharFun ν x = (1 : Q → ℂ) x := congrFun h x
  rw [linearCharFun_apply] at h2
  simpa using h2

theorem exists_comp_aut_mul_inv_eq {Q : Type*} [Group Q] [IsMulCommutative Q] [Finite Q]
    {u : MulAut Q} (hu : MonoidHom.FixedPointFree u) (lam : Q →* ℂˣ) :
    ∃ ν : Q →* ℂˣ, (ν.comp (u : Q →* Q)) * ν⁻¹ = lam := by
  set f : (Q →* ℂˣ) → (Q →* ℂˣ) := fun ν => (ν.comp (u : Q →* Q)) * ν⁻¹ with hf
  have hinj : Function.Injective f := by
    intro ν₁ ν₂ h
    have hμ : (ν₁ * ν₂⁻¹).comp (u : Q →* Q) = ν₁ * ν₂⁻¹ := by
      refine MonoidHom.ext fun x => ?_
      have h1 : ν₁ ((u : Q →* Q) x) * (ν₁ x)⁻¹ = ν₂ ((u : Q →* Q) x) * (ν₂ x)⁻¹ := by
        have h0 := congrArg (fun (g : Q →* ℂˣ) => g x) h
        simpa only [hf, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply] using h0
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
      rw [mul_inv_eq_iff_eq_mul] at h1 ⊢
      rw [h1, mul_comm (ν₂ ((u : Q →* Q) x) * (ν₂ x)⁻¹) (ν₁ x), mul_assoc,
        mul_comm (ν₂ x)⁻¹ (ν₂ ((u : Q →* Q) x)), ← mul_assoc]
    have h2 := eq_one_of_comp_aut_eq_of_fixedPointFree hu hμ
    rwa [mul_inv_eq_one] at h2
  exact Finite.injective_iff_surjective.1 hinj lam

theorem isMulCommutative_subgroupOf_of_le {X : Type*} [Group X] {A B : Subgroup X} (hAB : A ≤ B)
    (hA : IsMulCommutative A) : IsMulCommutative ↥(A.subgroupOf B) :=
  ⟨⟨fun a b => (Subgroup.subgroupOfEquivOfLe hAB).injective (by
    rw [map_mul, map_mul, hA.is_comm.comm])⟩⟩

theorem IsWitnessedPConfiguration.isMulCommutative_quotient_hallCore
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUab : IsMulCommutative U) :
    letI := hc.normal_subgroupOf_hallCore
    IsMulCommutative (↥(⁅M, M⁆ : Subgroup G) ⧸
      (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))) :=
  letI := hc.normal_subgroupOf_hallCore
  have hUs : IsMulCommutative ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G)) :=
    isMulCommutative_subgroupOf_of_le hc.le_commutator_E hUab
  ⟨⟨fun a b => (hc.isComplement'_subgroupOf_hallCore_E.symm).QuotientMulEquiv.injective (by
    rw [map_mul, map_mul, hUs.is_comm.comm])⟩⟩

theorem map_conjOnNormalized_subgroupOf_hallCore_eq (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) (w : W₁) :
    Subgroup.map ((conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w :
        MulAut ↥(⁅M, M⁆ : Subgroup G)) : ↥(⁅M, M⁆ : Subgroup G) →* ↥(⁅M, M⁆ : Subgroup G))
      (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
      = ((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G) :=
  map_mulAut_eq_of_mapsTo hprime.pos (conjOnNormalized_pow_natCard_eq_one hc w)
    (mapsTo_subgroupOf_hallCore hc w)

theorem fixedPointFree_quotientAutOfMapEq_conjOnNormalized
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime) {w : W₁}
    (hw1 : w ≠ 1) :
    letI := hc.normal_subgroupOf_hallCore
    MonoidHom.FixedPointFree
      (quotientAutOfMapEq (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
        (map_conjOnNormalized_subgroupOf_hallCore_eq hc hprime w)) :=
  letI := hc.normal_subgroupOf_hallCore
  fun _ ht => eq_one_of_quotientAutOfMapEq_eq_self hc.isComplement'_subgroupOf_hallCore_E _
    (mapsTo_subgroupOf_E hc w) (eq_one_of_conjOnNormalized_eq_self_of_mem_E hc hw1) ht

theorem exists_weakPair_of_mul_monoidHom_of_charConj_ne
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {α : ↥(⁅M, M⁆ : Subgroup G) → ℂ} (hα : α ∈ Irr (⁅M, M⁆ : Subgroup G))
    (hdetα : ∃ x : ↥(⁅M, M⁆ : Subgroup G),
      (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel α)
    (hinvα : ∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w α = α)
    (μ : ↥(⁅M, M⁆ : Subgroup G) →* ℂˣ)
    (hμH : ∀ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype → (μ x : ℂ) = 1)
    (hmov : ∃ w : W₁, charConj hc.le_normalizer_commutator_W₁ w (fun x => (μ x : ℂ) * α x)
      ≠ fun x => (μ x : ℂ) * α x) :
    ∃ a ∈ Irr (⁅M, M⁆ : Subgroup G), ∃ b ∈ Irr (⁅M, M⁆ : Subgroup G),
      a 1 = b 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel a) ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel b) ∧
      (∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w a = a) ∧
      ∃ w : W₁, charConj hc.le_normalizer_commutator_W₁ w b ≠ b := by
  obtain ⟨y, hyH, hy⟩ := hdetα
  refine ⟨α, hα, fun x => (μ x : ℂ) * α x, mul_mem_Irr μ hα, by simp, ⟨y, hyH, hy⟩,
    ⟨y, hyH, ?_⟩, hinvα, hmov⟩
  rw [mem_charValueKernel] at hy ⊢
  simpa [hμH y hyH] using hy

theorem exists_weakPair_of_invariant_of_apply_ne_zero
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime)
    (hUab : IsMulCommutative U)
    {α : ↥(⁅M, M⁆ : Subgroup G) → ℂ} (hα : α ∈ Irr (⁅M, M⁆ : Subgroup G))
    (hinvα : ∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w α = α)
    (hdetα : ∃ x : ↥(⁅M, M⁆ : Subgroup G),
      (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel α)
    {x₀ : ↥(⁅M, M⁆ : Subgroup G)} (hx₀ : (x₀ : G) ∉ (hallCore M).map M.subtype)
    (hx₀0 : α x₀ ≠ 0) :
    ∃ a ∈ Irr (⁅M, M⁆ : Subgroup G), ∃ b ∈ Irr (⁅M, M⁆ : Subgroup G),
      a 1 = b 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel a) ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel b) ∧
      (∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w a = a) ∧
      ∃ w : W₁, charConj hc.le_normalizer_commutator_W₁ w b ≠ b := by
  letI := hc.normal_subgroupOf_hallCore
  letI := hc.isMulCommutative_quotient_hallCore hUab
  have hnt : Nontrivial W₁ := Subgroup.nontrivial_iff_ne_bot W₁ |>.2 hc.ne_bot_W₁
  obtain ⟨w₀, hw₀⟩ := exists_ne (1 : W₁)
  have hv1 : w₀⁻¹ ≠ 1 := fun hcon => hw₀ (by simpa using congrArg (·⁻¹) hcon)
  set a := quotientAutOfMapEq (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
    (map_conjOnNormalized_subgroupOf_hallCore_eq hc hprime w₀⁻¹) with hadef
  have hafree := fixedPointFree_quotientAutOfMapEq_conjOnNormalized hc hprime hv1
  set t₀ := (QuotientGroup.mk x₀ : ↥(⁅M, M⁆ : Subgroup G) ⧸
    ((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) with ht₀
  have ht₀1 : t₀ ≠ 1 := by
    rw [ht₀, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hx₀
  have hst : a t₀ * t₀⁻¹ ≠ 1 := fun hcon =>
    ht₀1 (hafree t₀ (by rwa [mul_inv_eq_one] at hcon))
  obtain ⟨ν, hν⟩ := exists_monoidHom_apply_ne_one_of_isMulCommutative hst
  set μ : ↥(⁅M, M⁆ : Subgroup G) →* ℂˣ :=
    ν.comp (QuotientGroup.mk' (((hallCore M).map M.subtype).subgroupOf
      (⁅M, M⁆ : Subgroup G))) with hμ
  have hμH : ∀ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype →
      (μ x : ℂ) = 1 := by
    intro x hx
    have h1 : (QuotientGroup.mk x : ↥(⁅M, M⁆ : Subgroup G) ⧸
        ((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) = 1 :=
      (QuotientGroup.eq_one_iff x).2 (Subgroup.mem_subgroupOf.2 hx)
    change (ν (QuotientGroup.mk x) : ℂ) = 1
    rw [h1, map_one, Units.val_one]
  refine exists_weakPair_of_mul_monoidHom_of_charConj_ne hc hα hdetα hinvα μ hμH ⟨w₀, ?_⟩
  intro hcon
  have h := congrFun hcon x₀
  rw [charConj_eq_comp_conjOnNormalized] at h
  have hαinv : α (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w₀⁻¹ x₀)
      = α x₀ := by
    have h2 := hinvα w₀
    rw [charConj_eq_self_iff_forall] at h2
    exact h2 x₀
  have hmk : (QuotientGroup.mk (conjOnNormalized (⁅M, M⁆ : Subgroup G)
      hc.le_normalizer_commutator_W₁ w₀⁻¹ x₀) : ↥(⁅M, M⁆ : Subgroup G) ⧸
      ((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) = a t₀ := by
    rw [hadef, ht₀, quotientAutOfMapEq_mk]
  change (ν (QuotientGroup.mk (conjOnNormalized _ _ w₀⁻¹ x₀)) : ℂ) *
    α (conjOnNormalized _ _ w₀⁻¹ x₀) = (ν (QuotientGroup.mk x₀) : ℂ) * α x₀ at h
  rw [hmk, hαinv] at h
  refine hν ?_
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, mul_right_cancel₀ hx₀0 h]
  exact mul_inv_cancel₀ (Units.ne_zero _)

theorem mapsTo_subgroupOf_of_le_normalizer (hc : IsWitnessedPConfiguration M U W₁ W₂) (w : W₁)
    {A : Subgroup G} (hA : W₁ ≤ normalizer (A : Set G)) :
    ∀ x ∈ A.subgroupOf (⁅M, M⁆ : Subgroup G),
      conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x ∈
        A.subgroupOf (⁅M, M⁆ : Subgroup G) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [conjOnNormalized_apply_coe]
  exact (Subgroup.mem_normalizer_iff.1 (hA w.2) (x : G)).1 hx

theorem map_conjOnNormalized_subgroupOf_eq (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) (w : W₁) {A : Subgroup G}
    (hA : W₁ ≤ normalizer (A : Set G)) :
    Subgroup.map ((conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w :
        MulAut ↥(⁅M, M⁆ : Subgroup G)) : ↥(⁅M, M⁆ : Subgroup G) →* ↥(⁅M, M⁆ : Subgroup G))
      (A.subgroupOf (⁅M, M⁆ : Subgroup G)) = A.subgroupOf (⁅M, M⁆ : Subgroup G) :=
  map_mulAut_eq_of_mapsTo hprime.pos (conjOnNormalized_pow_natCard_eq_one hc w)
    (mapsTo_subgroupOf_of_le_normalizer hc w hA)

theorem charConj_comp_mk (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {N : Subgroup ↥(⁅M, M⁆ : Subgroup G)} [N.Normal] (ψ : ↥(⁅M, M⁆ : Subgroup G) ⧸ N → ℂ)
    (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)) :
    charConj hc.le_normalizer_commutator_W₁ w (ψ ∘ QuotientGroup.mk) x
      = ψ (QuotientGroup.mk
          (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w⁻¹ x)) :=
  charConj_eq_comp_conjOnNormalized _ w (ψ ∘ QuotientGroup.mk) x

theorem exists_weakPair_of_comp_mk (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {N : Subgroup ↥(⁅M, M⁆ : Subgroup G)} [N.Normal]
    {a' b' : ↥(⁅M, M⁆ : Subgroup G) ⧸ N → ℂ} (ha' : a' ∈ Irr (↥(⁅M, M⁆ : Subgroup G) ⧸ N))
    (hb' : b' ∈ Irr (↥(⁅M, M⁆ : Subgroup G) ⧸ N)) (hdeg : a' 1 = b' 1)
    (hdeta' : ∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
      (QuotientGroup.mk x : ↥(⁅M, M⁆ : Subgroup G) ⧸ N) ∉ charValueKernel a')
    (hdetb' : ∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
      (QuotientGroup.mk x : ↥(⁅M, M⁆ : Subgroup G) ⧸ N) ∉ charValueKernel b')
    (hinva' : ∀ (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)),
      a' (QuotientGroup.mk
        (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x))
        = a' (QuotientGroup.mk x))
    (hmovb' : ∃ (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)),
      b' (QuotientGroup.mk
        (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x))
        ≠ b' (QuotientGroup.mk x)) :
    ∃ a ∈ Irr (⁅M, M⁆ : Subgroup G), ∃ b ∈ Irr (⁅M, M⁆ : Subgroup G),
      a 1 = b 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel a) ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel b) ∧
      (∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w a = a) ∧
      ∃ w : W₁, charConj hc.le_normalizer_commutator_W₁ w b ≠ b := by
  refine ⟨a' ∘ QuotientGroup.mk, irrTrivialOn_subset_Irr (mem_irrTrivialOn_comp_mk ha'),
    b' ∘ QuotientGroup.mk, irrTrivialOn_subset_Irr (mem_irrTrivialOn_comp_mk hb'),
    by simpa [comp_mk_one] using hdeg, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hxH, hx⟩ := hdeta'
    refine ⟨x, hxH, ?_⟩
    rw [mem_charValueKernel] at hx ⊢
    simpa [comp_mk_one] using hx
  · obtain ⟨x, hxH, hx⟩ := hdetb'
    refine ⟨x, hxH, ?_⟩
    rw [mem_charValueKernel] at hx ⊢
    simpa [comp_mk_one] using hx
  · intro w
    funext x
    rw [charConj_comp_mk hc a' w x]
    exact hinva' w⁻¹ x
  · obtain ⟨w, x, hx⟩ := hmovb'
    refine ⟨w⁻¹, fun hcon => hx ?_⟩
    have h := congrFun hcon x
    rwa [charConj_comp_mk hc b' w⁻¹ x, inv_inv] at h

theorem cfInner_self_resClassFun_of_eq_zero_of_notMem {K : Type*} [Group K] [Fintype K]
    (A : Subgroup K) [Fintype A] (χ : K → ℂ) (hvan : ∀ x : K, x ∉ A → χ x = 0) :
    cfInner (resClassFun A χ) (resClassFun A χ) = (A.index : ℂ) * cfInner χ χ := by
  classical
  have hsum : ∑ y : A, resClassFun A χ y * (starRingEnd ℂ) (resClassFun A χ y)
      = ∑ x : K, χ x * (starRingEnd ℂ) (χ x) := by
    have h1 : ∑ x ∈ Finset.univ.filter (· ∈ A), χ x * (starRingEnd ℂ) (χ x)
        = ∑ y : A, χ (y : K) * (starRingEnd ℂ) (χ (y : K)) :=
      Finset.sum_subtype (p := fun x : K => x ∈ A) (s := Finset.univ.filter (· ∈ A))
        (by intro x; simp) (fun x => χ x * (starRingEnd ℂ) (χ x))
    have h2 : ∑ x ∈ Finset.univ.filter (· ∈ A), χ x * (starRingEnd ℂ) (χ x)
        = ∑ x : K, χ x * (starRingEnd ℂ) (χ x) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro x _ hx
      have : χ x = 0 := hvan x (by simpa using hx)
      simp [this]
    calc ∑ y : A, resClassFun A χ y * (starRingEnd ℂ) (resClassFun A χ y)
        = ∑ y : A, χ (y : K) * (starRingEnd ℂ) (χ (y : K)) := by
          simp [resClassFun_apply]
      _ = ∑ x ∈ Finset.univ.filter (· ∈ A), χ x * (starRingEnd ℂ) (χ x) := h1.symm
      _ = ∑ x : K, χ x * (starRingEnd ℂ) (χ x) := h2
  rw [cfInner_def, cfInner_def, hsum]
  have hcard : (Nat.card K : ℂ) = (A.index : ℂ) * (Nat.card A : ℂ) := by
    rw [← Nat.cast_mul, A.index_mul_card]
  have hAne : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hIne : (A.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  rw [hcard, mul_inv]
  field_simp

theorem cfInner_self_resClassFun_eq_index_of_mem_Irr_of_eq_zero_of_notMem {K : Type*} [Group K]
    [Fintype K] (A : Subgroup K) [Fintype A] {χ : K → ℂ} (hχ : χ ∈ Irr K)
    (hvan : ∀ x : K, x ∉ A → χ x = 0) :
    cfInner (resClassFun A χ) (resClassFun A χ) = (A.index : ℂ) := by
  rw [cfInner_self_resClassFun_of_eq_zero_of_notMem A χ hvan, cfInner_self_of_mem_Irr hχ, mul_one]

theorem IsWitnessedPConfiguration.le_normalizer_hallCore_W₁
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    W₁ ≤ normalizer (((hallCore M).map M.subtype : Subgroup G) : Set G) :=
  hc.le_M_W₁.trans (le_normalizer_map_subtype_hallCore M)

theorem autFixedSubgroup_conjOnNormalized_hallCore_eq (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {w : W₁} (hw1 : w ≠ 1) :
    autFixedSubgroup (conjOnNormalized ((hallCore M).map M.subtype)
        hc.le_normalizer_hallCore_W₁ w)
      = W₂.subgroupOf ((hallCore M).map M.subtype) := by
  have hW₂ := hc.inf_centralizer_eq_W₂ (w : G) w.2 fun hcon => hw1 (Subtype.ext hcon)
  ext x
  rw [mem_autFixedSubgroup, Subgroup.mem_subgroupOf]
  refine ⟨fun hx => ?_, fun hx => Subtype.ext ?_⟩
  · have h1 : (w : G) * (x : G) * (w : G)⁻¹ = (x : G) := by
      have hx' := congrArg (fun y : ↥((hallCore M).map M.subtype) => (y : G)) hx
      rwa [conjOnNormalized_apply_coe] at hx'
    refine hW₂ ▸ ⟨hc.hallCore_le_commutator x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (x : G) * (w : G) = ((w : G) * (x : G) * (w : G)⁻¹) * (w : G) := by rw [h1]
      _ = (w : G) * (x : G) := by group
  · have hcent : (x : G) ∈ centralizer {(w : G)} := (hW₂ ▸ hx : _).2
    rw [conjOnNormalized_apply_coe, ← Subgroup.mem_centralizer_singleton_iff.1 hcent]
    group

theorem natCard_fixed_irrAut_conjOnNormalized_hallCore_eq
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime) {w : W₁}
    (hw1 : w ≠ 1) :
    Nat.card {χ : Irr ↥((hallCore M).map M.subtype) //
      irrAut (conjOnNormalized ((hallCore M).map M.subtype)
        hc.le_normalizer_hallCore_W₁ w) χ = χ} = Nat.card W₂ := by
  have hW₂H : W₂ ≤ (hallCore M).map M.subtype := hc.le_hallCore_W₂
  have hcyc : IsCyclic ↥(W₂.subgroupOf ((hallCore M).map M.subtype)) :=
    isCyclic_subgroupOf hW₂H hc.isCyclic_W₂
  have hnd : ¬ (Nat.card W₁) ∣ Nat.card ((hallCore M).map M.subtype) := fun h =>
    hc.not_natCard_W₁_dvd_natCard_commutator
      (h.trans (Subgroup.card_dvd_of_le hc.hallCore_le_commutator))
  have hpow : (conjOnNormalized ((hallCore M).map M.subtype)
      hc.le_normalizer_hallCore_W₁ w) ^ Nat.card W₁ = 1 := by
    rw [← map_pow, show w ^ Nat.card (W₁ : Subgroup G) = 1 from pow_card_eq_one', map_one]
  rw [natCard_fixed_Irr_eq_natCard_conjClasses_autFixed hprime hnd hpow,
    autFixedSubgroup_conjOnNormalized_hallCore_eq hc hw1,
    natCard_conjClasses_eq_natCard_of_comm fun x y => mul_comm' x y]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₂H).toEquiv

theorem exists_invariant_mem_Irr_hallCore_ne_one (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) :
    ∃ lam ∈ Irr ↥((hallCore M).map M.subtype), lam ≠ 1 ∧
      ∀ v : W₁, charConj hc.le_normalizer_hallCore_W₁ v lam = lam := by
  have hnt : Nontrivial W₁ := Subgroup.nontrivial_iff_ne_bot W₁ |>.2 hc.ne_bot_W₁
  obtain ⟨w, hw1⟩ := exists_ne (1 : W₁)
  set b := conjOnNormalized ((hallCore M).map M.subtype) hc.le_normalizer_hallCore_W₁ w with hbd
  set p₁ : {χ : Irr ↥((hallCore M).map M.subtype) // irrAut b χ = χ} :=
    ⟨⟨1, one_mem_Irr⟩, (irrAut_eq_self_iff b _).2 fun _ => rfl⟩ with hp₁
  have hcard : Nat.card {χ : Irr ↥((hallCore M).map M.subtype) // irrAut b χ = χ} ≠ 1 := by
    rw [natCard_fixed_irrAut_conjOnNormalized_hallCore_eq hc hprime hw1]
    have h1 : 1 < Nat.card W₂ := Subgroup.one_lt_card_iff_ne_bot W₂ |>.2 hc.ne_bot_W₂
    omega
  have hne : ∃ s, s ≠ p₁ := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hcard (Nat.card_eq_one_iff_unique.2 ⟨⟨fun a c => (hcon a).trans (hcon c).symm⟩, ⟨p₁⟩⟩)
  obtain ⟨⟨⟨lam, hlam⟩, hlamfix⟩, hlamne⟩ := hne
  have hlam1 : lam ≠ 1 := fun hcon => hlamne (by subst hcon; rfl)
  have hlaminv : ∀ x, lam (b x) = lam x := (irrAut_eq_self_iff b ⟨lam, hlam⟩).1 hlamfix
  have hconj : charConj hc.le_normalizer_hallCore_W₁ w⁻¹ lam = lam := by
    rw [charConj_eq_self_iff_forall]
    simpa [hbd] using hlaminv
  exact ⟨lam, hlam, hlam1, forall_charConj_eq_of_charConj_eq hc.le_normalizer_hallCore_W₁ hprime
    (w := w⁻¹) (fun hcon => hw1 (by simpa using congrArg (·⁻¹) hcon)) hconj⟩

theorem normal_subgroupOf_commutator_of_le_normalizer (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hAM : M ≤ normalizer (A : Set G)) :
    (A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (hAH.trans hc.hallCore_le_commutator)).2
    fun _ hx => hAM (Subgroup.commutator_le_self M hx)

omit [Finite G] in
theorem map_topEquiv_subgroupOf_top {X : Type*} [Group X] (A : Subgroup X) :
    Subgroup.map (Subgroup.topEquiv (G := X) : _ →* X) (A.subgroupOf (⊤ : Subgroup X)) = A := by
  ext x
  simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

noncomputable def semidirectQuotientEquiv (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] :
    letI := hc.normal_subgroupOf_hallCore
    (↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
        (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
          (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
      ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
        ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))
      ≃* (↥(⁅M, M⁆ : Subgroup G) ⧸ A.subgroupOf (⁅M, M⁆ : Subgroup G)) :=
  letI := hc.normal_subgroupOf_hallCore
  have hcomp := hc.isComplement'_subgroupOf_hallCore_E
  (SemidirectProduct.congr (MulEquiv.refl _)
      (quotientBotSubgroupOfEquiv (U.subgroupOf (⁅M, M⁆ : Subgroup G))).symm (fun _ => by
        refine MulEquiv.ext fun z => ?_
        simp only [MulEquiv.trans_apply, MulEquiv.refl_apply,
          quotientBotSubgroupOfEquiv_symm_apply, quotConjAut_mk,
          conjQuotAutRestrict_apply])).trans
    (((quotientEquivSemidirectProduct _ _ _ bot_le (Subgroup.subgroupOf_mono _ hAH) bot_le
        hcomp.sup_eq_top hcomp.disjoint le_top le_top).trans
      (QuotientGroup.quotientMulEquivOfEq (by rw [sup_bot_eq]))).trans
      (QuotientGroup.congr _ _ Subgroup.topEquiv (map_topEquiv_subgroupOf_top _)))

theorem semidirectQuotientEquiv_inl (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal]
    (h : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientEquiv hc hAH (SemidirectProduct.inl (QuotientGroup.mk h))
      = QuotientGroup.mk (h : ↥(⁅M, M⁆ : Subgroup G)) := by
  letI := hc.normal_subgroupOf_hallCore
  simp only [semidirectQuotientEquiv, MulEquiv.trans_apply]
  rw [show (SemidirectProduct.congr (MulEquiv.refl _)
      (quotientBotSubgroupOfEquiv (U.subgroupOf (⁅M, M⁆ : Subgroup G))).symm _)
      (SemidirectProduct.inl (QuotientGroup.mk h))
      = SemidirectProduct.inl (QuotientGroup.mk h) from
    SemidirectProduct.ext (by simp [SemidirectProduct.congr_apply_left])
      (by simp [SemidirectProduct.congr_apply_right])]
  rw [quotientEquivSemidirectProduct_inl, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.congr_mk]
  rfl

theorem semidirectQuotientEquiv_inr (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal]
    (u : ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientEquiv hc hAH (SemidirectProduct.inr u)
      = QuotientGroup.mk (u : ↥(⁅M, M⁆ : Subgroup G)) := by
  letI := hc.normal_subgroupOf_hallCore
  simp only [semidirectQuotientEquiv, MulEquiv.trans_apply]
  rw [show (SemidirectProduct.congr (MulEquiv.refl _)
      (quotientBotSubgroupOfEquiv (U.subgroupOf (⁅M, M⁆ : Subgroup G))).symm _)
      (SemidirectProduct.inr u) = SemidirectProduct.inr (QuotientGroup.mk u) from
    SemidirectProduct.ext (by simp [SemidirectProduct.congr_apply_left])
      (by
        simp only [SemidirectProduct.congr_apply_right, SemidirectProduct.right_inr]
        exact quotientBotSubgroupOfEquiv_symm_apply _ u)]
  rw [quotientEquivSemidirectProduct_inr, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.congr_mk]
  rfl

theorem exists_weakPair_of_mulEquiv (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {N : Subgroup ↥(⁅M, M⁆ : Subgroup G)} [N.Normal] {X : Type*} [Group X]
    (f : X ≃* (↥(⁅M, M⁆ : Subgroup G) ⧸ N)) {a' b' : X → ℂ} (ha' : a' ∈ Irr X)
    (hb' : b' ∈ Irr X) (hdeg : a' 1 = b' 1)
    (hdeta' : ∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
      a' (f.symm (QuotientGroup.mk x)) ≠ a' 1)
    (hdetb' : ∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
      b' (f.symm (QuotientGroup.mk x)) ≠ b' 1)
    (hinva' : ∀ (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)),
      a' (f.symm (QuotientGroup.mk (conjOnNormalized (⁅M, M⁆ : Subgroup G)
          hc.le_normalizer_commutator_W₁ w x))) = a' (f.symm (QuotientGroup.mk x)))
    (hmovb' : ∃ (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)),
      b' (f.symm (QuotientGroup.mk (conjOnNormalized (⁅M, M⁆ : Subgroup G)
          hc.le_normalizer_commutator_W₁ w x))) ≠ b' (f.symm (QuotientGroup.mk x))) :
    ∃ a ∈ Irr (⁅M, M⁆ : Subgroup G), ∃ b ∈ Irr (⁅M, M⁆ : Subgroup G),
      a 1 = b 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel a) ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel b) ∧
      (∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w a = a) ∧
      ∃ w : W₁, charConj hc.le_normalizer_commutator_W₁ w b ≠ b := by
  have hA : a' ∘ f.symm ∈ Irr (↥(⁅M, M⁆ : Subgroup G) ⧸ N) :=
    mem_Irr_of_comp_mulEquiv f (by
      have h : (a' ∘ f.symm) ∘ f = a' := by funext x; simp
      rwa [h])
  have hB : b' ∘ f.symm ∈ Irr (↥(⁅M, M⁆ : Subgroup G) ⧸ N) :=
    mem_Irr_of_comp_mulEquiv f (by
      have h : (b' ∘ f.symm) ∘ f = b' := by funext x; simp
      rwa [h])
  refine exists_weakPair_of_comp_mk hc hA hB (by simpa using hdeg) ?_ ?_ (fun w x => hinva' w x) ?_
  · obtain ⟨x, hxH, hx⟩ := hdeta'
    exact ⟨x, hxH, by simpa [mem_charValueKernel] using hx⟩
  · obtain ⟨x, hxH, hx⟩ := hdetb'
    exact ⟨x, hxH, by simpa [mem_charValueKernel] using hx⟩
  · obtain ⟨w, x, hx⟩ := hmovb'
    exact ⟨w, x, hx⟩

theorem semidirectQuotientEquiv_symm_mk_coe_inl (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal]
    (h : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    (semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk (h : ↥(⁅M, M⁆ : Subgroup G)))
      = SemidirectProduct.inl (QuotientGroup.mk h) := by
  letI := hc.normal_subgroupOf_hallCore
  rw [← semidirectQuotientEquiv_inl hc hAH h, MulEquiv.symm_apply_apply]

theorem semidirectQuotientEquiv_symm_mk_coe_inr (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal]
    (u : ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    (semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk (u : ↥(⁅M, M⁆ : Subgroup G)))
      = SemidirectProduct.inr u := by
  letI := hc.normal_subgroupOf_hallCore
  rw [← semidirectQuotientEquiv_inr hc hAH u, MulEquiv.symm_apply_apply]

noncomputable def semidirectQuotientConjAut (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] (w : W₁) :
    letI := hc.normal_subgroupOf_hallCore
    MulAut ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
        (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
          (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
      ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
        ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))) :=
  letI := hc.normal_subgroupOf_hallCore
  (semidirectQuotientEquiv hc hAH).trans
    ((quotientAutOfMapEq (A.subgroupOf (⁅M, M⁆ : Subgroup G))
        (map_conjOnNormalized_subgroupOf_eq hc hprime w hA)).trans
      (semidirectQuotientEquiv hc hAH).symm)

theorem semidirectQuotientConjAut_symm_mk (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] (w : W₁)
    (x : ↥(⁅M, M⁆ : Subgroup G)) :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientConjAut hc hprime hAH hA w
        ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x))
      = (semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk
          (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x)) := by
  letI := hc.normal_subgroupOf_hallCore
  simp only [semidirectQuotientConjAut, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [quotientAutOfMapEq_mk]

theorem semidirectQuotientConjAut_pow_symm_mk (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] (w : W₁)
    (n : ℕ) (x : ↥(⁅M, M⁆ : Subgroup G)) :
    letI := hc.normal_subgroupOf_hallCore
    (semidirectQuotientConjAut hc hprime hAH hA w ^ n)
        ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x))
      = (semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk
          ((conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w ^ n) x)) := by
  letI := hc.normal_subgroupOf_hallCore
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, semidirectQuotientConjAut_symm_mk hc hprime hAH hA w x, ih,
        pow_succ, MulAut.mul_apply]

theorem semidirectQuotientConjAut_pow_natCard_eq_one (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] (w : W₁) :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientConjAut hc hprime hAH hA w ^ Nat.card W₁ = 1 := by
  letI := hc.normal_subgroupOf_hallCore
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (semidirectQuotientEquiv hc hAH y)
  have hyx : y = (semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x) := by
    rw [hx, MulEquiv.symm_apply_apply]
  rw [hyx, semidirectQuotientConjAut_pow_symm_mk hc hprime hAH hA w,
    conjOnNormalized_pow_natCard_eq_one hc w]
  rfl

@[simp] theorem semidirectQuotientConjAut_one (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientConjAut hc hprime hAH hA 1 = 1 := by
  letI := hc.normal_subgroupOf_hallCore
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (semidirectQuotientEquiv hc hAH y)
  have hyx : y = (semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x) := by
    rw [hx, MulEquiv.symm_apply_apply]
  rw [hyx, semidirectQuotientConjAut_symm_mk hc hprime hAH hA 1 x, map_one]
  rfl

theorem exists_weakPairSemidirect_of_comp_semidirectQuotientConjAut
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal]
    {a' b' : letI := hc.normal_subgroupOf_hallCore
      ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))) → ℂ}
    (ha' : letI := hc.normal_subgroupOf_hallCore
      a' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))))
    (hb' : letI := hc.normal_subgroupOf_hallCore
      b' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))))
    (hdeg : a' 1 = b' 1)
    (hdeta' : letI := hc.normal_subgroupOf_hallCore
      ∃ h : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        a' (SemidirectProduct.inl (QuotientGroup.mk h)) ≠ a' 1)
    (hdetb' : letI := hc.normal_subgroupOf_hallCore
      ∃ h : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        b' (SemidirectProduct.inl (QuotientGroup.mk h)) ≠ b' 1)
    (hinva' : ∀ w : W₁, a' ∘ semidirectQuotientConjAut hc hprime hAH hA w = a')
    (hmovb' : ∃ w : W₁, b' ∘ semidirectQuotientConjAut hc hprime hAH hA w ≠ b') :
    letI := hc.normal_subgroupOf_hallCore
    ∃ a'' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      ∃ b'' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      a'' 1 = b'' 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
        a'' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x)) ≠ a'' 1) ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
        b'' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x)) ≠ b'' 1) ∧
      (∀ (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)),
        a'' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk
            (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x)))
          = a'' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x))) ∧
      ∃ (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)),
        b'' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk
            (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x)))
          ≠ b'' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x)) := by
  letI := hc.normal_subgroupOf_hallCore
  refine ⟨a', ha', b', hb', hdeg, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h, hh⟩ := hdeta'
    exact ⟨(h : ↥(⁅M, M⁆ : Subgroup G)), Subgroup.mem_subgroupOf.1 h.2,
      by rwa [semidirectQuotientEquiv_symm_mk_coe_inl hc hAH h]⟩
  · obtain ⟨h, hh⟩ := hdetb'
    exact ⟨(h : ↥(⁅M, M⁆ : Subgroup G)), Subgroup.mem_subgroupOf.1 h.2,
      by rwa [semidirectQuotientEquiv_symm_mk_coe_inl hc hAH h]⟩
  · intro w x
    have h := congrFun (hinva' w) ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x))
    rwa [Function.comp_apply, semidirectQuotientConjAut_symm_mk hc hprime hAH hA w x] at h
  · obtain ⟨w, hw⟩ := hmovb'
    obtain ⟨y, hy⟩ : ∃ y, b' (semidirectQuotientConjAut hc hprime hAH hA w y) ≠ b' y := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hw (funext fun y => hcon y)
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (semidirectQuotientEquiv hc hAH y)
    refine ⟨w, x, ?_⟩
    have hyx : y = (semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x) := by
      rw [hx, MulEquiv.symm_apply_apply]
    rwa [hyx, semidirectQuotientConjAut_symm_mk hc hprime hAH hA w x] at hy

theorem isCyclic_of_isIrreducible_of_actionKernel_eq_bot {X : Type*} [Group X]
    {H H₀ D₀ : Subgroup X} [H.Normal] [H₀.Normal] {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V)
    [IsMulCommutative ↥(ChiefFactorFaithfulImage.factorLinearImage p H H₀ D₀ e)]
    [(linearGroupRep (ChiefFactorFaithfulImage.factorLinearImage p H H₀ D₀ e)).IsIrreducible]
    (hker : ChiefFactorFaithfulImage.actionKernel p H H₀ D₀ e = ⊥) : IsCyclic ↥D₀ := by
  have hD : IsCyclic ↥(ChiefFactorFaithfulImage.factorLinearImage p H H₀ D₀ e) :=
    isCyclic_of_isMulCommutative_of_isIrreducible
  have hinj : Function.Injective
      ((ChiefFactorFaithfulImage.factorLinearAut p H H₀ e).comp D₀.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← actionKernel_eq_ker]
    exact hker
  have hsub : IsCyclic
      ↥((ChiefFactorFaithfulImage.factorLinearAut p H H₀ e).comp D₀.subtype).range := by
    rw [range_comp_subtype_eq_factorLinearImage]; exact hD
  exact isCyclic_of_surjective
    (((ChiefFactorFaithfulImage.factorLinearAut p H H₀ e).comp D₀.subtype).ofInjective
      hinj).symm.toMonoidHom
    (((ChiefFactorFaithfulImage.factorLinearAut p H H₀ e).comp D₀.subtype).ofInjective
      hinj).symm.surjective

theorem exists_actsReducibly_or_isIrreducible_actionKernel_ne_bot (h : IsTypeII M)
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUnc : ¬ IsCyclic U)
    {H₀ : Subgroup ↥M} [H₀.Normal] (hchief : IsChiefFactor (hallCore ↥M) H₀)
    (hCU : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ H₀) :
    ∃ (p : ℕ) (_ : Fact p.Prime)
      (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃*
        Multiplicative (Fin (Nat.card W₁) → ZMod p)),
      ActsReducibly
          (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀ (U.subgroupOf M) e) ∨
        ((linearGroupRep (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀
            (U.subgroupOf M) e)).IsIrreducible ∧
          ChiefFactorFaithfulImage.actionKernel p (hallCore ↥M) H₀ (U.subgroupOf M) e ≠ ⊥) := by
  obtain ⟨hpc, hUne, -, -, -, -⟩ := h.clauses_of_isWitnessedPConfiguration hsolv hc
  have hq : (Nat.card W₁).Prime := hpc.prime_natCard_W₁
  have hptype := hc.isPTypeConfig hsolv hq hUne
  letI := hchief.normal_num
  letI := hchief.normal_den
  have hqcard : Nat.card (W₁.subgroupOf M) = Nat.card W₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le_M_W₁).toEquiv
  have hfq : Fact (Nat.card W₁).Prime := Fact.mk hq
  obtain ⟨p, d, hp, -, ⟨e⟩⟩ :=
    ChiefFactorLinearAction.exists_prime_nonempty_mulEquiv_of_isChiefFactor hchief
  have hfp := Fact.mk hp
  obtain ⟨b, hbB, hb1, -⟩ := exists_zpowers_eq_of_prime_natCard hptype.prime_natCard_B
  have hs := hptype.isFaithfulImageSetup hqcard hchief hCU hbB hb1
  have hdq : d = Nat.card W₁ := by
    have hh := hs.finrank_eq p e hp
    rwa [Module.finrank_fin_fun] at hh
  subst hdq
  refine ⟨p, hfp, e, ?_⟩
  set Dm := hptype.linearModel (p := p) hqcard hchief hCU hbB hb1 e with hDm
  have hA : Dm.A =
      ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀ (U.subgroupOf M) e :=
    hptype.linearModel_A hqcard hchief hCU hbB hb1 e
  rcases Dm.xor_actsReducibly_isIrreducible with ⟨hred, -⟩ | ⟨hirr, -⟩
  · exact Or.inl (hA ▸ hred)
  · refine Or.inr ⟨hA ▸ hirr, fun hker => ?_⟩
    letI : IsMulCommutative ↥(ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀
        (U.subgroupOf M) e) := hA ▸ Dm.isMulCommutative_A
    letI : (linearGroupRep (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀
        (U.subgroupOf M) e)).IsIrreducible := hA ▸ hirr
    have hUsc : IsCyclic ↥(U.subgroupOf M) :=
      isCyclic_of_isIrreducible_of_actionKernel_eq_bot e hker
    exact hUnc (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hc.le_M_E)
      (Subgroup.subgroupOfEquivOfLe hc.le_M_E).surjective)

noncomputable def hallCoreSubgroupOfEquiv (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ≃* ↥(hallCore ↥M) :=
  (Subgroup.subgroupOfEquivOfLe hc.hallCore_le_commutator).trans
    ((hallCore ↥M).equivMapOfInjective M.subtype M.subtype_injective).symm

theorem coe_hallCoreSubgroupOfEquiv (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (h : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))) :
    ((hallCoreSubgroupOfEquiv hc h : ↥M) : G) = ((h : ↥(⁅M, M⁆ : Subgroup G)) : G) :=
  congrArg (fun z : ↥((hallCore ↥M).map M.subtype) => (z : G))
    (((hallCore ↥M).equivMapOfInjective M.subtype M.subtype_injective).apply_symm_apply
      (Subgroup.subgroupOfEquivOfLe hc.hallCore_le_commutator h))

theorem hallCoreSubgroupOfEquiv_eq (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {h : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))} {m : ↥(hallCore ↥M)}
    (hm : ((m : ↥M) : G) = ((h : ↥(⁅M, M⁆ : Subgroup G)) : G)) :
    hallCoreSubgroupOfEquiv hc h = m :=
  Subtype.ext (Subtype.ext ((coe_hallCoreSubgroupOfEquiv hc h).trans hm.symm))

theorem map_hallCoreSubgroupOfEquiv_subgroupOf (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} {A : Subgroup G} (hAeq : A = H₀.map M.subtype) :
    Subgroup.map ((hallCoreSubgroupOfEquiv hc) : _ →* ↥(hallCore ↥M))
        ((A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
          (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
      = H₀.subgroupOf (hallCore ↥M) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxA : ((x : ↥(⁅M, M⁆ : Subgroup G)) : G) ∈ A := hx
    rw [hAeq] at hxA
    obtain ⟨z, hz, hzeq⟩ := hxA
    have hzz : (hallCoreSubgroupOfEquiv hc x : ↥M) = z :=
      Subtype.ext ((coe_hallCoreSubgroupOfEquiv hc x).trans hzeq.symm)
    change (hallCoreSubgroupOfEquiv hc x : ↥M) ∈ H₀
    rw [hzz]
    exact hz
  · intro hy
    refine ⟨(hallCoreSubgroupOfEquiv hc).symm y, ?_, by simp⟩
    have hco := coe_hallCoreSubgroupOfEquiv hc ((hallCoreSubgroupOfEquiv hc).symm y)
    rw [MulEquiv.apply_symm_apply] at hco
    rw [hAeq]
    exact ⟨(y : ↥M), hy, hco⟩

noncomputable def hallCoreQuotientEquiv (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G)) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    (↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
        (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
          (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
      ≃* (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) :=
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  QuotientGroup.congr _ _ (hallCoreSubgroupOfEquiv hc)
    (map_hallCoreSubgroupOfEquiv_subgroupOf hc hAeq)

theorem hallCoreQuotientEquiv_mk (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G))
    (x : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
    {m : ↥(hallCore ↥M)} (hm : ((m : ↥M) : G) = ((x : ↥(⁅M, M⁆ : Subgroup G)) : G)) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    hallCoreQuotientEquiv hc hAeq hAH hAM (QuotientGroup.mk x) = QuotientGroup.mk m := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  simp only [hallCoreQuotientEquiv, QuotientGroup.congr_mk]
  rw [hallCoreSubgroupOfEquiv_eq hc hm]

noncomputable def subgroupOfCommutatorEquivSubgroupOfM (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G)) ≃* ↥(U.subgroupOf M) :=
  (Subgroup.subgroupOfEquivOfLe hc.le_commutator_E).trans
    (Subgroup.subgroupOfEquivOfLe hc.le_M_E).symm

theorem coe_subgroupOfCommutatorEquivSubgroupOfM (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (u : ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))) :
    ((subgroupOfCommutatorEquivSubgroupOfM hc u : ↥M) : G) = ((u : ↥(⁅M, M⁆ : Subgroup G)) : G) :=
  congrArg (fun z : ↥U => (z : G))
    ((Subgroup.subgroupOfEquivOfLe hc.le_M_E).apply_symm_apply
      (Subgroup.subgroupOfEquivOfLe hc.le_commutator_E u))

theorem le_normalizer_subgroupOf_E_W₁ (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    W₁.subgroupOf M ≤ normalizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf] at hw
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv]
  exact Subgroup.mem_normalizer_iff.1 (hc.le_normalizer_E hw) (x : G)

theorem hallCoreQuotientEquiv_conj (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G)) (w : W₁)
    (x x' : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
    (hx' : ((x' : ↥(⁅M, M⁆ : Subgroup G)) : G)
      = (w : G) * ((x : ↥(⁅M, M⁆ : Subgroup G)) : G) * (w : G)⁻¹) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    hallCoreQuotientEquiv hc hAeq hAH hAM (QuotientGroup.mk x')
      = ChiefFactorLinearAction.factorConjAut (hallCore ↥M) H₀ ⟨(w : G), hc.le_M_W₁ w.2⟩
          (hallCoreQuotientEquiv hc hAeq hAH hAM (QuotientGroup.mk x)) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  rw [hallCoreQuotientEquiv_mk hc hAeq hAH hAM x (m := hallCoreSubgroupOfEquiv hc x)
      (coe_hallCoreSubgroupOfEquiv hc x),
    ChiefFactorLinearAction.factorConjAut_mk,
    hallCoreQuotientEquiv_mk hc hAeq hAH hAM x'
      (m := MulAut.conjNormal (⟨(w : G), hc.le_M_W₁ w.2⟩ : ↥M) (hallCoreSubgroupOfEquiv hc x)) ?_]
  have h1 : ((MulAut.conjNormal (⟨(w : G), hc.le_M_W₁ w.2⟩ : ↥M)
      (hallCoreSubgroupOfEquiv hc x) : ↥(hallCore ↥M)) : ↥M)
      = (⟨(w : G), hc.le_M_W₁ w.2⟩ : ↥M) * (hallCoreSubgroupOfEquiv hc x : ↥M) *
        (⟨(w : G), hc.le_M_W₁ w.2⟩ : ↥M)⁻¹ := rfl
  rw [h1]
  push_cast
  rw [coe_hallCoreSubgroupOfEquiv hc x, hx']

theorem hallCoreQuotientEquiv_conj_of_mem_M (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G))
    {g : G} (hg : g ∈ M)
    (x x' : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
    (hx' : ((x' : ↥(⁅M, M⁆ : Subgroup G)) : G)
      = g * ((x : ↥(⁅M, M⁆ : Subgroup G)) : G) * g⁻¹) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    hallCoreQuotientEquiv hc hAeq hAH hAM (QuotientGroup.mk x')
      = ChiefFactorLinearAction.factorConjAut (hallCore ↥M) H₀ ⟨g, hg⟩
          (hallCoreQuotientEquiv hc hAeq hAH hAM (QuotientGroup.mk x)) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  rw [hallCoreQuotientEquiv_mk hc hAeq hAH hAM x (m := hallCoreSubgroupOfEquiv hc x)
      (coe_hallCoreSubgroupOfEquiv hc x),
    ChiefFactorLinearAction.factorConjAut_mk,
    hallCoreQuotientEquiv_mk hc hAeq hAH hAM x'
      (m := MulAut.conjNormal (⟨g, hg⟩ : ↥M) (hallCoreSubgroupOfEquiv hc x)) ?_]
  have h1 : ((MulAut.conjNormal (⟨g, hg⟩ : ↥M)
      (hallCoreSubgroupOfEquiv hc x) : ↥(hallCore ↥M)) : ↥M)
      = (⟨g, hg⟩ : ↥M) * (hallCoreSubgroupOfEquiv hc x : ↥M) * (⟨g, hg⟩ : ↥M)⁻¹ := rfl
  rw [h1]
  push_cast
  rw [coe_hallCoreSubgroupOfEquiv hc x, hx']

noncomputable def factorConjAutRestrictM (M : Subgroup G) (U : Subgroup G) (H₀ : Subgroup ↥M)
    [H₀.Normal] :
    ↥(U.subgroupOf M) →* MulAut (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) :=
  (ChiefFactorLinearAction.factorConjAut (hallCore ↥M) H₀).comp (U.subgroupOf M).subtype

omit [Finite G] in
@[simp] theorem factorConjAutRestrictM_apply (M U : Subgroup G) (H₀ : Subgroup ↥M) [H₀.Normal]
    (u : ↥(U.subgroupOf M)) :
    factorConjAutRestrictM M U H₀ u
      = ChiefFactorLinearAction.factorConjAut (hallCore ↥M) H₀ (u : ↥M) := (rfl)

theorem hallCoreQuotientEquiv_conjQuotAutRestrict (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G))
    (u : ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G)))
    (y : letI := hc.normal_subgroupOf_hallCore
      ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
        (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
          (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    hallCoreQuotientEquiv hc hAeq hAH hAM
        (conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G)) u y)
      = factorConjAutRestrictM M U H₀ (subgroupOfCommutatorEquivSubgroupOfM hc u)
          (hallCoreQuotientEquiv hc hAeq hAH hAM y) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  induction y using QuotientGroup.induction_on with
  | _ x =>
    rw [conjQuotAutRestrict_apply, conjQuotientAut_apply_mk, factorConjAutRestrictM_apply]
    have hmem : ((subgroupOfCommutatorEquivSubgroupOfM hc u : ↥M) : G) ∈ M :=
      (subgroupOfCommutatorEquivSubgroupOfM hc u : ↥M).2
    have hx' : ((MulAut.conjNormal (u : ↥(⁅M, M⁆ : Subgroup G)) x :
        ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))) :
          ↥(⁅M, M⁆ : Subgroup G)) = ((subgroupOfCommutatorEquivSubgroupOfM hc u : ↥M) : G) *
        ((x : ↥(⁅M, M⁆ : Subgroup G)) : G) *
        ((subgroupOfCommutatorEquivSubgroupOfM hc u : ↥M) : G)⁻¹ := by
      rw [coe_subgroupOfCommutatorEquivSubgroupOfM hc u]
      rfl
    have hkey := hallCoreQuotientEquiv_conj_of_mem_M hc hAeq hAH hAM hmem x
      (MulAut.conjNormal (u : ↥(⁅M, M⁆ : Subgroup G)) x) hx'
    convert hkey using 3

noncomputable def modelEquivM (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G)) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
        (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
          (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
      ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
        ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G)))
      ≃* ((↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M))
        ⋊[factorConjAutRestrictM M U H₀] ↥(U.subgroupOf M)) :=
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  SemidirectProduct.congr (hallCoreQuotientEquiv hc hAeq hAH hAM)
    (subgroupOfCommutatorEquivSubgroupOfM hc)
    (fun u => MulEquiv.ext fun y => hallCoreQuotientEquiv_conjQuotAutRestrict hc hAeq hAH hAM u y)

theorem modelEquivM_inl (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G))
    (y : letI := hc.normal_subgroupOf_hallCore
      letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
      ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
        (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
          (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    modelEquivM hc hAeq hAH hAM (SemidirectProduct.inl y)
      = SemidirectProduct.inl (hallCoreQuotientEquiv hc hAeq hAH hAM y) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  refine SemidirectProduct.ext ?_ ?_
  · exact SemidirectProduct.congr_apply_left _ _ _ (SemidirectProduct.inl y)
  · refine (SemidirectProduct.congr_apply_right _ _ _ (SemidirectProduct.inl y)).trans ?_
    rw [SemidirectProduct.right_inl, map_one, SemidirectProduct.right_inl]

theorem modelEquivM_inr (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G))
    (u : ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    modelEquivM hc hAeq hAH hAM (SemidirectProduct.inr u)
      = SemidirectProduct.inr (subgroupOfCommutatorEquivSubgroupOfM hc u) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  refine SemidirectProduct.ext ?_ ?_
  · refine (SemidirectProduct.congr_apply_left _ _ _ (SemidirectProduct.inr u)).trans ?_
    rw [SemidirectProduct.left_inr, map_one, SemidirectProduct.left_inr]
  · exact SemidirectProduct.congr_apply_right _ _ _ (SemidirectProduct.inr u)

theorem subgroupOfCommutatorEquivSubgroupOfM_conj (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (w : W₁) (u u' : ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G)))
    (hu' : ((u' : ↥(⁅M, M⁆ : Subgroup G)) : G)
      = (w : G) * ((u : ↥(⁅M, M⁆ : Subgroup G)) : G) * (w : G)⁻¹) :
    subgroupOfCommutatorEquivSubgroupOfM hc u'
      = conjOnNormalized (U.subgroupOf M) (le_normalizer_subgroupOf_E_W₁ hc)
          ⟨⟨(w : G), hc.le_M_W₁ w.2⟩, (Subgroup.mem_subgroupOf).2 w.2⟩
          (subgroupOfCommutatorEquivSubgroupOfM hc u) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [conjOnNormalized_apply_coe]
  push_cast
  rw [coe_subgroupOfCommutatorEquivSubgroupOfM hc u, coe_subgroupOfCommutatorEquivSubgroupOfM hc u',
    hu']

theorem semidirectQuotientConjAut_inl (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] (w : W₁)
    (x x' : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
    (hval : (x' : ↥(⁅M, M⁆ : Subgroup G))
      = conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w
          (x : ↥(⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientConjAut hc hprime hAH hA w (SemidirectProduct.inl (QuotientGroup.mk x))
      = SemidirectProduct.inl (QuotientGroup.mk x') := by
  letI := hc.normal_subgroupOf_hallCore
  rw [← semidirectQuotientEquiv_symm_mk_coe_inl hc hAH x,
    semidirectQuotientConjAut_symm_mk hc hprime hAH hA w, ← hval]
  exact semidirectQuotientEquiv_symm_mk_coe_inl hc hAH x'

theorem semidirectQuotientConjAut_inr (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] (w : W₁)
    (u u' : ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G)))
    (hval : (u' : ↥(⁅M, M⁆ : Subgroup G))
      = conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w
          (u : ↥(⁅M, M⁆ : Subgroup G))) :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientConjAut hc hprime hAH hA w (SemidirectProduct.inr u)
      = SemidirectProduct.inr u' := by
  letI := hc.normal_subgroupOf_hallCore
  rw [← semidirectQuotientEquiv_symm_mk_coe_inr hc hAH u,
    semidirectQuotientConjAut_symm_mk hc hprime hAH hA w, ← hval]
  exact semidirectQuotientEquiv_symm_mk_coe_inr hc hAH u'

omit [Finite G] in
theorem comp_mulAut_pow_eq_self {X : Type*} [Group X] {f : MulAut X} {a : X → ℂ}
    (ha : a ∘ f = a) (n : ℕ) : a ∘ (f ^ n) = a := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
      funext y
      have h1 : ((f ^ (n + 1)) y) = (f ^ n) (f y) := by rw [pow_succ, MulAut.mul_apply]
      change a ((f ^ (n + 1)) y) = a y
      rw [h1]
      have h2 := congrFun ih (f y)
      have h3 := congrFun ha y
      simp only [Function.comp_apply] at h2 h3
      rw [h2, h3]

theorem semidirectQuotientConjAut_mul (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] (v w : W₁) :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientConjAut hc hprime hAH hA (v * w)
      = semidirectQuotientConjAut hc hprime hAH hA v *
        semidirectQuotientConjAut hc hprime hAH hA w := by
  letI := hc.normal_subgroupOf_hallCore
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (semidirectQuotientEquiv hc hAH y)
  have hyx : y = (semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x) := by
    rw [hx, MulEquiv.symm_apply_apply]
  rw [hyx, semidirectQuotientConjAut_symm_mk hc hprime hAH hA (v * w) x, MulAut.mul_apply,
    semidirectQuotientConjAut_symm_mk hc hprime hAH hA w x,
    semidirectQuotientConjAut_symm_mk hc hprime hAH hA v, map_mul, MulAut.mul_apply]

theorem semidirectQuotientConjAut_pow (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal] (w : W₁)
    (n : ℕ) :
    letI := hc.normal_subgroupOf_hallCore
    semidirectQuotientConjAut hc hprime hAH hA (w ^ n)
      = semidirectQuotientConjAut hc hprime hAH hA w ^ n := by
  letI := hc.normal_subgroupOf_hallCore
  induction n with
  | zero => simp [semidirectQuotientConjAut_one hc hprime hAH hA]
  | succ n ih => rw [pow_succ, semidirectQuotientConjAut_mul hc hprime hAH hA, ih, pow_succ]

theorem forall_comp_semidirectQuotientConjAut_eq_of_ne_one
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal]
    {w₀ : W₁} (hw₀ : w₀ ≠ 1)
    {a' : letI := hc.normal_subgroupOf_hallCore
      ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))) → ℂ}
    (hinv : a' ∘ semidirectQuotientConjAut hc hprime hAH hA w₀ = a') (w : W₁) :
    a' ∘ semidirectQuotientConjAut hc hprime hAH hA w = a' := by
  letI := hc.normal_subgroupOf_hallCore
  letI : Fact (Nat.card W₁).Prime := ⟨hprime⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff w w₀).1 (mem_powers_of_prime_card rfl hw₀)
  rw [← hn, semidirectQuotientConjAut_pow hc hprime hAH hA w₀ n]
  exact comp_mulAut_pow_eq_self hinv n

theorem exists_modelPair_of_mulEquiv_of_comp
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₁).Prime)
    {A : Subgroup G} (hAH : A ≤ (hallCore M).map M.subtype)
    (hA : W₁ ≤ normalizer (A : Set G)) [(A.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal]
    {w₀ : W₁} (hw₀ : w₀ ≠ 1)
    {X : Type*} [Group X]
    (f : letI := hc.normal_subgroupOf_hallCore
      X ≃* ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))))
    (τ : MulAut X)
    (hτ : letI := hc.normal_subgroupOf_hallCore
      ∀ x : X, f (τ x) = semidirectQuotientConjAut hc hprime hAH hA w₀ (f x))
    {α β : X → ℂ} (hα : α ∈ Irr X) (hβ : β ∈ Irr X) (hdeg : α 1 = β 1)
    (hdetα : letI := hc.normal_subgroupOf_hallCore
      ∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        α (f.symm (SemidirectProduct.inl (QuotientGroup.mk hh))) ≠ α 1)
    (hdetβ : letI := hc.normal_subgroupOf_hallCore
      ∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        β (f.symm (SemidirectProduct.inl (QuotientGroup.mk hh))) ≠ β 1)
    (hinvα : α ∘ τ = α) (hmovβ : β ∘ τ ≠ β) :
    letI := hc.normal_subgroupOf_hallCore
    ∃ a' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      ∃ b' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      a' 1 = b' 1 ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        a' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ a' 1) ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        b' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ b' 1) ∧
      (∀ w : W₁, a' ∘ semidirectQuotientConjAut hc hprime hAH hA w = a') ∧
      ∃ w : W₁, b' ∘ semidirectQuotientConjAut hc hprime hAH hA w ≠ b' := by
  letI := hc.normal_subgroupOf_hallCore
  refine ⟨α ∘ f.symm, FrobeniusInduction.mem_Irr_comp_mulEquiv hα f.symm,
    β ∘ f.symm, FrobeniusInduction.mem_Irr_comp_mulEquiv hβ f.symm, by simpa using hdeg,
    ?_, ?_, ?_, ?_⟩
  · obtain ⟨hh, hhh⟩ := hdetα
    exact ⟨hh, by simpa using hhh⟩
  · obtain ⟨hh, hhh⟩ := hdetβ
    exact ⟨hh, by simpa using hhh⟩
  · refine forall_comp_semidirectQuotientConjAut_eq_of_ne_one hc hprime hAH hA hw₀ ?_
    funext y
    have h1 : f.symm (semidirectQuotientConjAut hc hprime hAH hA w₀ y) = τ (f.symm y) := by
      have hh := hτ (f.symm y)
      rw [MulEquiv.apply_symm_apply] at hh
      rw [← hh, MulEquiv.symm_apply_apply]
    have h2 := congrFun hinvα (f.symm y)
    simp only [Function.comp_apply] at h2 ⊢
    rw [h1, h2]
  · refine ⟨w₀, fun hcon => hmovβ ?_⟩
    funext x
    have hh := congrFun hcon (f x)
    simp only [Function.comp_apply, MulEquiv.symm_apply_apply] at hh
    rw [← hτ x, MulEquiv.symm_apply_apply] at hh
    simpa using hh

noncomputable def modelConjAutM (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G}
    (hAeq : A = H₀.map M.subtype) (hAH : A ≤ (hallCore M).map M.subtype)
    (hAM : M ≤ normalizer (A : Set G)) (w : W₁) :
    MulAut ((↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M))
      ⋊[factorConjAutRestrictM M U H₀] ↥(U.subgroupOf M)) :=
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  (modelEquivM hc hAeq hAH hAM).symm.trans
    ((semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w).trans
      (modelEquivM hc hAeq hAH hAM))

theorem modelEquivM_semidirectQuotientConjAut (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G}
    (hAeq : A = H₀.map M.subtype) (hAH : A ≤ (hallCore M).map M.subtype)
    (hAM : M ≤ normalizer (A : Set G)) (w : W₁)
    (x : letI := hc.normal_subgroupOf_hallCore
      letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
      ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G)))) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    modelEquivM hc hAeq hAH hAM
        (semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w x)
      = modelConjAutM hc hprime hAeq hAH hAM w (modelEquivM hc hAeq hAH hAM x) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  simp only [modelConjAutM, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem modelConjAutM_inl (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G}
    (hAeq : A = H₀.map M.subtype) (hAH : A ≤ (hallCore M).map M.subtype)
    (hAM : M ≤ normalizer (A : Set G)) (w : W₁)
    (y : ↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) :
    modelConjAutM hc hprime hAeq hAH hAM w (SemidirectProduct.inl y)
      = SemidirectProduct.inl (ChiefFactorLinearAction.factorConjAut (hallCore ↥M) H₀
          ⟨(w : G), hc.le_M_W₁ w.2⟩ y) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  obtain ⟨z, hz⟩ := (hallCoreQuotientEquiv hc hAeq hAH hAM).surjective y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective z
  subst hz
  subst hx
  rw [← modelEquivM_inl hc hAeq hAH hAM, ← modelEquivM_semidirectQuotientConjAut hc hprime hAeq
    hAH hAM w (SemidirectProduct.inl (QuotientGroup.mk x)),
    semidirectQuotientConjAut_inl hc hprime hAH (hc.le_M_W₁.trans hAM) w x
      ⟨conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w
        (x : ↥(⁅M, M⁆ : Subgroup G)), mapsTo_subgroupOf_hallCore hc w _ x.2⟩ rfl,
    modelEquivM_inl hc hAeq hAH hAM]
  rw [hallCoreQuotientEquiv_conj hc hAeq hAH hAM w x _ (conjOnNormalized_apply_coe _ w _)]

theorem modelConjAutM_inr (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G}
    (hAeq : A = H₀.map M.subtype) (hAH : A ≤ (hallCore M).map M.subtype)
    (hAM : M ≤ normalizer (A : Set G)) (w : W₁) (u : ↥(U.subgroupOf M)) :
    modelConjAutM hc hprime hAeq hAH hAM w (SemidirectProduct.inr u)
      = SemidirectProduct.inr (conjOnNormalized (U.subgroupOf M)
          (le_normalizer_subgroupOf_E_W₁ hc)
          ⟨⟨(w : G), hc.le_M_W₁ w.2⟩, (Subgroup.mem_subgroupOf).2 w.2⟩ u) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  obtain ⟨v, hv⟩ := (subgroupOfCommutatorEquivSubgroupOfM hc).surjective u
  subst hv
  rw [← modelEquivM_inr hc hAeq hAH hAM, ← modelEquivM_semidirectQuotientConjAut hc hprime hAeq
    hAH hAM w (SemidirectProduct.inr v),
    semidirectQuotientConjAut_inr hc hprime hAH (hc.le_M_W₁.trans hAM) w v
      ⟨conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w
        (v : ↥(⁅M, M⁆ : Subgroup G)), mapsTo_subgroupOf_E hc w _ v.2⟩ rfl,
    modelEquivM_inr hc hAeq hAH hAM]
  rw [subgroupOfCommutatorEquivSubgroupOfM_conj hc w v _ (conjOnNormalized_apply_coe _ w _)]

theorem exists_modelPair_of_modelM (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime) {H₀ : Subgroup ↥M} [H₀.Normal] {A : Subgroup G}
    (hAeq : A = H₀.map M.subtype) (hAH : A ≤ (hallCore M).map M.subtype)
    (hAM : M ≤ normalizer (A : Set G)) {w₀ : W₁} (hw₀ : w₀ ≠ 1)
    {α β : ((↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M))
      ⋊[factorConjAutRestrictM M U H₀] ↥(U.subgroupOf M)) → ℂ}
    (hα : α ∈ Irr ((↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M))
      ⋊[factorConjAutRestrictM M U H₀] ↥(U.subgroupOf M)))
    (hβ : β ∈ Irr ((↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M))
      ⋊[factorConjAutRestrictM M U H₀] ↥(U.subgroupOf M)))
    (hdeg : α 1 = β 1)
    (hdetα : ∃ y : ↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M),
      α (SemidirectProduct.inl y) ≠ α 1)
    (hdetβ : ∃ y : ↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M),
      β (SemidirectProduct.inl y) ≠ β 1)
    (hinvα : α ∘ modelConjAutM hc hprime hAeq hAH hAM w₀ = α)
    (hmovβ : β ∘ modelConjAutM hc hprime hAeq hAH hAM w₀ ≠ β) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    ∃ a' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      ∃ b' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      a' 1 = b' 1 ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        a' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ a' 1) ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        b' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ b' 1) ∧
      (∀ w : W₁,
        a' ∘ semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w = a') ∧
      ∃ w : W₁,
        b' ∘ semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w ≠ b' := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  refine exists_modelPair_of_mulEquiv_of_comp hc hprime hAH (hc.le_M_W₁.trans hAM) hw₀
    (modelEquivM hc hAeq hAH hAM).symm (modelConjAutM hc hprime hAeq hAH hAM w₀) (fun x => ?_)
    hα hβ hdeg ?_ ?_ hinvα hmovβ
  · rw [MulEquiv.symm_apply_eq, modelEquivM_semidirectQuotientConjAut hc hprime hAeq hAH hAM w₀,
      MulEquiv.apply_symm_apply]
  · obtain ⟨y, hy⟩ := hdetα
    obtain ⟨hh, hhh⟩ := QuotientGroup.mk_surjective
      ((hallCoreQuotientEquiv hc hAeq hAH hAM).symm y)
    refine ⟨hh, ?_⟩
    rwa [MulEquiv.symm_symm, modelEquivM_inl hc hAeq hAH hAM, hhh, MulEquiv.apply_symm_apply]
  · obtain ⟨y, hy⟩ := hdetβ
    obtain ⟨hh, hhh⟩ := QuotientGroup.mk_surjective
      ((hallCoreQuotientEquiv hc hAeq hAH hAM).symm y)
    refine ⟨hh, ?_⟩
    rwa [MulEquiv.symm_symm, modelEquivM_inl hc hAeq hAH hAM, hhh, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem mulAutMultiplicative_factorLinearAut (p : ℕ) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {H H₀ : Subgroup ↥M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (g : ↥M)
    (y : ↥H ⧸ H₀.subgroupOf H) :
    FixedFreeImage.mulAutMultiplicative
        (ChiefFactorFaithfulImage.factorLinearAut p H H₀ e g) (e y)
      = e (ChiefFactorLinearAction.factorConjAut H H₀ g y) := by
  rw [FixedFreeImage.mulAutMultiplicative_apply,
    ChiefFactorFaithfulImage.factorLinearAut_apply']
  simp

noncomputable def modelEquivLinear (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (M U : Subgroup G) {H₀ : Subgroup ↥M} [H₀.Normal]
    (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃* Multiplicative V) :
    ((↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M))
        ⋊[factorConjAutRestrictM M U H₀] ↥(U.subgroupOf M))
      ≃* (Multiplicative V
        ⋊[FixedFreeImage.mulAutMultiplicative.comp
            ((ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e).comp
              (U.subgroupOf M).subtype)]
          ↥(U.subgroupOf M)) :=
  SemidirectProduct.congr e (MulEquiv.refl _) (fun u => MulEquiv.ext fun y => by
    simp only [MulEquiv.coe_trans, Function.comp_apply, MulEquiv.refl_apply,
      factorConjAutRestrictM_apply, MonoidHom.coe_comp]
    exact (mulAutMultiplicative_factorLinearAut p e (u : ↥M) y).symm)

omit [Finite G] in
theorem modelEquivLinear_inl (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (M U : Subgroup G) {H₀ : Subgroup ↥M} [H₀.Normal]
    (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃* Multiplicative V)
    (y : ↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) :
    modelEquivLinear p M U e (SemidirectProduct.inl y) = SemidirectProduct.inl (e y) := by
  refine SemidirectProduct.ext ?_ ?_
  · exact SemidirectProduct.congr_apply_left _ _ _ (SemidirectProduct.inl y)
  · refine (SemidirectProduct.congr_apply_right _ _ _ (SemidirectProduct.inl y)).trans ?_
    rw [SemidirectProduct.right_inl, MulEquiv.refl_apply, SemidirectProduct.right_inl]

omit [Finite G] in
theorem modelEquivLinear_inr (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (M U : Subgroup G) {H₀ : Subgroup ↥M} [H₀.Normal]
    (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃* Multiplicative V)
    (u : ↥(U.subgroupOf M)) :
    modelEquivLinear p M U e (SemidirectProduct.inr u) = SemidirectProduct.inr u := by
  refine SemidirectProduct.ext ?_ ?_
  · refine (SemidirectProduct.congr_apply_left _ _ _ (SemidirectProduct.inr u)).trans ?_
    rw [SemidirectProduct.left_inr, map_one, SemidirectProduct.left_inr]
  · exact SemidirectProduct.congr_apply_right _ _ _ (SemidirectProduct.inr u)

omit [Finite G] in
theorem modelEquivLinear_symm_inl (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (M U : Subgroup G) {H₀ : Subgroup ↥M} [H₀.Normal]
    (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃* Multiplicative V)
    (m : Multiplicative V) :
    (modelEquivLinear p M U e).symm (SemidirectProduct.inl m)
      = SemidirectProduct.inl (e.symm m) := by
  rw [MulEquiv.symm_apply_eq, modelEquivLinear_inl, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem modelEquivLinear_symm_inr (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (M U : Subgroup G) {H₀ : Subgroup ↥M} [H₀.Normal]
    (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃* Multiplicative V)
    (u : ↥(U.subgroupOf M)) :
    (modelEquivLinear p M U e).symm (SemidirectProduct.inr u) = SemidirectProduct.inr u := by
  rw [MulEquiv.symm_apply_eq, modelEquivLinear_inr]

theorem exists_pair_of_mulEquiv_semi {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Finite E] [Nontrivial E]
    {V : Type*} [Group V] [IsMulCommutative V] [Finite V] (hqV : ¬ q ∣ Nat.card V)
    (b : E ≃ₗ[ZMod p] E) (hbq : b ^ q = 1) {s : E} (hs : s ≠ 0) (hbs : b s = s)
    (σ : MulAut V) (hσq : σ ^ q = 1) (hσ1 : σ ≠ 1) (hσfix : ∀ w : V, σ w = w → w = 1)
    (r : V →* (E ≃ₗ[ZMod p] E)) (hr : ∀ w : V, r (σ w) = b * r w * b⁻¹)
    (hC : MonoidHom.ker r ≠ ⊥)
    (hD : ∀ d ∈ MonoidHom.range r, d ≠ 1 → ∀ v : E, d v = v → v = 0)
    {X : Type*} [Group X]
    (f : X ≃* (Multiplicative E ⋊[FixedFreeImage.mulAutMultiplicative.comp r] V)) (τ : MulAut X)
    (hτl : ∀ v : E, f (τ (f.symm (SemidirectProduct.inl (Multiplicative.ofAdd v))))
      = SemidirectProduct.inl (Multiplicative.ofAdd (b v)))
    (hτr : ∀ u : V, f (τ (f.symm (SemidirectProduct.inr u))) = SemidirectProduct.inr (σ u)) :
    ∃ α ∈ Irr X, ∃ β ∈ Irr X, α 1 = β 1 ∧
      (∃ v : E, α (f.symm (SemidirectProduct.inl (Multiplicative.ofAdd v))) ≠ α 1) ∧
      (∃ v : E, β (f.symm (SemidirectProduct.inl (Multiplicative.ofAdd v))) ≠ β 1) ∧
      α ∘ τ = α ∧ β ∘ τ ≠ β := by
  classical
  let _ : Fintype E := Fintype.ofFinite E
  let _ : CommGroup V := IsMulCommutative.instCommGroup
  have : Small.{0} V := inferInstance
  set ι : Shrink.{0} V ≃* V := Shrink.mulEquiv with hι
  have : Finite (Shrink.{0} V) := Finite.of_equiv V ι.toEquiv.symm
  let _ : Fintype (Shrink.{0} V) := Fintype.ofFinite _
  set r₀ : Shrink.{0} V →* (E ≃ₗ[ZMod p] E) := r.comp ι.toMonoidHom with hr₀def
  set σ₀ : MulAut (Shrink.{0} V) := MulAut.congr ι.symm σ with hσ₀def
  have hσ₀ : ∀ w : Shrink.{0} V, σ₀ w = ι.symm (σ (ι w)) := fun w => rfl
  have hισ₀ : ∀ w : Shrink.{0} V, ι (σ₀ w) = σ (ι w) := fun w => by rw [hσ₀ w]; simp
  have hσ₀q : σ₀ ^ q = 1 := by rw [hσ₀def, ← map_pow, hσq, map_one]
  have hσ₀1 : σ₀ ≠ 1 := by
    intro hcon
    refine hσ1 (MulEquiv.injective (MulAut.congr ι.symm) ?_)
    rw [← hσ₀def, hcon, map_one]
  have hσ₀fix : ∀ w : Shrink.{0} V, σ₀ w = w → w = 1 := by
    intro w hw
    have h1 : σ (ι w) = ι w := by rw [← hισ₀ w, hw]
    simpa using hσfix _ h1
  have hr₀ : ∀ w : Shrink.{0} V, r₀ (σ₀ w) = b * r₀ w * b⁻¹ := by
    intro w
    change r (ι (σ₀ w)) = b * r (ι w) * b⁻¹
    rw [hισ₀ w, hr]
  have hqV₀ : ¬ q ∣ Nat.card (Shrink.{0} V) := by rw [Nat.card_congr ι.toEquiv]; exact hqV
  have hC₀ : MonoidHom.ker r₀ ≠ ⊥ := by
    intro hcon
    refine hC (le_antisymm (fun u hu => ?_) bot_le)
    have hmem : ι.symm u ∈ MonoidHom.ker r₀ := by
      rw [MonoidHom.mem_ker]
      change r (ι (ι.symm u)) = 1
      simpa using MonoidHom.mem_ker.1 hu
    rw [hcon, Subgroup.mem_bot] at hmem
    simpa using congrArg ι hmem
  have hD₀ : ∀ d ∈ MonoidHom.range r₀, d ≠ 1 → ∀ v : E, d v = v → v = 0 := by
    intro d hd
    obtain ⟨u, hu⟩ := hd
    exact hD d ⟨ι u, hu⟩
  obtain ⟨α₀, β₀, -, -, hα₀, hβ₀, -, -, hdα₀, hdβ₀, hEα₀, hEβ₀, hinvα₀, hmovβ₀⟩ :=
    exists_moving_character_pair hp hq hpq hqV₀ b hbq s hs hbs σ₀ hσ₀q hσ₀1 hσ₀fix r₀ hr₀ hC₀ hD₀
  have hcompat : ∀ w : Shrink.{0} V,
      ((FixedFreeImage.mulAutMultiplicative.comp r₀) w).trans (MulEquiv.refl (Multiplicative E))
      = (MulEquiv.refl (Multiplicative E)).trans
          ((FixedFreeImage.mulAutMultiplicative.comp r) (ι w)) :=
    fun w => MulEquiv.ext fun x => rfl
  set g : FixedFreeImage.Semi r₀
      ≃* (Multiplicative E ⋊[FixedFreeImage.mulAutMultiplicative.comp r] V) :=
    SemidirectProduct.congr (MulEquiv.refl _) ι hcompat with hgdef
  have hginl : ∀ m : Multiplicative E, g (SemidirectProduct.inl m) = SemidirectProduct.inl m := by
    intro m
    refine SemidirectProduct.ext ?_ ?_
    · exact SemidirectProduct.congr_apply_left _ _ _ (SemidirectProduct.inl m)
    · refine (SemidirectProduct.congr_apply_right _ _ _ (SemidirectProduct.inl m)).trans ?_
      rw [SemidirectProduct.right_inl, map_one, SemidirectProduct.right_inl]
  have hginr : ∀ w : Shrink.{0} V,
      g (SemidirectProduct.inr w) = SemidirectProduct.inr (ι w) := by
    intro w
    refine SemidirectProduct.ext ?_ ?_
    · refine (SemidirectProduct.congr_apply_left _ _ _ (SemidirectProduct.inr w)).trans ?_
      rw [SemidirectProduct.left_inr, map_one, SemidirectProduct.left_inr]
    · exact SemidirectProduct.congr_apply_right _ _ _ (SemidirectProduct.inr w)
  set h : X ≃* FixedFreeImage.Semi r₀ := f.trans g.symm with hhdef
  have hsymm_inl : ∀ m : Multiplicative E,
      h.symm (SemidirectProduct.inl m) = f.symm (SemidirectProduct.inl m) := by
    intro m
    rw [hhdef, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, hginl]
  have happly : ∀ x : X, h x = g.symm (f x) := fun x => rfl
  have hsymm_inr : ∀ w : Shrink.{0} V,
      h.symm (SemidirectProduct.inr w) = f.symm (SemidirectProduct.inr (ι w)) := by
    intro w
    rw [hhdef, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, hginr]
  have key : ∀ y : FixedFreeImage.Semi r₀,
      h (τ (h.symm y)) = FixedFreeImage.qAut r₀ b σ₀ hr₀ y := by
    have hext := SemidirectProduct.hom_ext
      (f := (h.toMonoidHom.comp (τ.toMonoidHom.comp h.symm.toMonoidHom)))
      (g := (FixedFreeImage.qAut r₀ b σ₀ hr₀).toMonoidHom) ?_ ?_
    · intro y
      exact congrFun (congrArg (fun m : FixedFreeImage.Semi r₀ →* FixedFreeImage.Semi r₀ =>
        (m : FixedFreeImage.Semi r₀ → FixedFreeImage.Semi r₀)) hext) y
    · refine MonoidHom.ext fun m => ?_
      change h (τ (h.symm (SemidirectProduct.inl
          (Multiplicative.ofAdd (Multiplicative.toAdd m)))))
        = FixedFreeImage.qAut r₀ b σ₀ hr₀
            (SemidirectProduct.inl (Multiplicative.ofAdd (Multiplicative.toAdd m)))
      rw [hsymm_inl, happly, hτl (Multiplicative.toAdd m), FixedFreeImage.qAut_inl,
        ← hginl (Multiplicative.ofAdd (b (Multiplicative.toAdd m))), MulEquiv.symm_apply_apply]
    · refine MonoidHom.ext fun w => ?_
      change h (τ (h.symm (SemidirectProduct.inr w)))
        = FixedFreeImage.qAut r₀ b σ₀ hr₀ (SemidirectProduct.inr w)
      rw [hsymm_inr, happly, hτr (ι w), FixedFreeImage.qAut_inr, ← hισ₀ w, ← hginr (σ₀ w),
        MulEquiv.symm_apply_apply]
  have keyx : ∀ x : X, h (τ x) = FixedFreeImage.qAut r₀ b σ₀ hr₀ (h x) := by
    intro x
    have hk := key (h x)
    rwa [MulEquiv.symm_apply_apply] at hk
  have hfsymm : ∀ m : Multiplicative E,
      h (f.symm (SemidirectProduct.inl m)) = SemidirectProduct.inl m := by
    intro m
    rw [happly, MulEquiv.apply_symm_apply, ← hginl m, MulEquiv.symm_apply_apply]
  refine ⟨α₀ ∘ h, FrobeniusInduction.mem_Irr_comp_mulEquiv hα₀ h,
    β₀ ∘ h, FrobeniusInduction.mem_Irr_comp_mulEquiv hβ₀ h, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, map_one, hdα₀, hdβ₀]
  · obtain ⟨x, hxm, hx⟩ := hEα₀
    obtain ⟨v, rfl⟩ := (FixedFreeImage.mem_basePart r₀).1 hxm
    refine ⟨v, ?_⟩
    simp only [Function.comp_apply, map_one]
    rw [hfsymm (Multiplicative.ofAdd v)]
    exact hx
  · obtain ⟨x, hxm, hx⟩ := hEβ₀
    obtain ⟨v, rfl⟩ := (FixedFreeImage.mem_basePart r₀).1 hxm
    refine ⟨v, ?_⟩
    simp only [Function.comp_apply, map_one]
    rw [hfsymm (Multiplicative.ofAdd v)]
    exact hx
  · funext x
    simp only [Function.comp_apply]
    rw [keyx x]
    exact congrFun hinvα₀ (h x)
  · intro hcon
    refine absurd (hmovβ₀ 0 1 hq.pos hq.one_lt ?_) (by norm_num)
    funext y
    simp only [Function.comp_apply, pow_zero, pow_one, MulAut.one_apply]
    have h1 := congrFun hcon (h.symm y)
    simp only [Function.comp_apply] at h1
    rw [key y, MulEquiv.apply_symm_apply] at h1
    exact h1.symm

theorem eq_one_of_conjOnNormalized_subgroupOf_M_eq_self (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {w : W₁} (hw1 : w ≠ 1) (u : ↥(U.subgroupOf M))
    (hfix : conjOnNormalized (U.subgroupOf M) (le_normalizer_subgroupOf_E_W₁ hc)
      ⟨⟨(w : G), hc.le_M_W₁ w.2⟩, (Subgroup.mem_subgroupOf).2 w.2⟩ u = u) : u = 1 := by
  have hcoe : (w : G) * ((u : ↥M) : G) * (w : G)⁻¹ = ((u : ↥M) : G) := by
    have h1 := conjOnNormalized_apply_coe (le_normalizer_subgroupOf_E_W₁ hc)
      (⟨⟨(w : G), hc.le_M_W₁ w.2⟩, (Subgroup.mem_subgroupOf).2 w.2⟩ : ↥(W₁.subgroupOf M)) u
    rw [hfix] at h1
    have h2 := congrArg (fun z : ↥M => (z : G)) h1
    push_cast at h2
    exact h2.symm
  have huU : ((u : ↥M) : G) ∈ U := (Subgroup.mem_subgroupOf).1 u.2
  have hmem : ((u : ↥M) : G) ∈ (⁅M, M⁆ : Subgroup G) ⊓ centralizer {(w : G)} := by
    refine ⟨hc.le_commutator_E huU, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc ((u : ↥M) : G) * (w : G) = ((w : G) * ((u : ↥M) : G) * (w : G)⁻¹) * (w : G) := by
          rw [hcoe]
      _ = (w : G) * ((u : ↥M) : G) := by group
  rw [hc.inf_centralizer_eq_W₂ (w : G) w.2 (fun hcon => hw1 (Subtype.ext hcon))] at hmem
  exact Subtype.ext (Subtype.ext
    (Subgroup.disjoint_def.1 hc.disjoint_hallCore_E (hc.le_hallCore_W₂ hmem) huU))

theorem not_natCard_W₁_dvd_natCard_subgroupOf_E (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ¬ (Nat.card W₁) ∣ Nat.card ↥(U.subgroupOf M) := by
  intro hd
  refine hc.not_natCard_W₁_dvd_natCard_commutator ?_
  have h1 : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le_M_E).toEquiv
  have h2 : Nat.card ↥U = Nat.card ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le_commutator_E).toEquiv).symm
  rw [h1, h2] at hd
  exact hd.trans (Subgroup.card_subgroup_dvd_card _)

theorem exists_modelPairM_of_isIrreducible (h : IsTypeII M)
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hprime : (Nat.card W₁).Prime)
    {H₀ : Subgroup ↥M} [H₀.Normal] (hchief : IsChiefFactor (hallCore ↥M) H₀)
    (hCU : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ H₀)
    {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G))
    {p : ℕ} (hp : Fact p.Prime)
    (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃*
      Multiplicative (Fin (Nat.card W₁) → ZMod p))
    (hirr : (linearGroupRep (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀
      (U.subgroupOf M) e)).IsIrreducible)
    (hker : ChiefFactorFaithfulImage.actionKernel p (hallCore ↥M) H₀ (U.subgroupOf M) e ≠ ⊥) :
    ∃ w₀ : W₁, w₀ ≠ 1 ∧
      ∃ α ∈ Irr ((↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M))
        ⋊[factorConjAutRestrictM M U H₀] ↥(U.subgroupOf M)),
      ∃ β ∈ Irr ((↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M))
        ⋊[factorConjAutRestrictM M U H₀] ↥(U.subgroupOf M)),
      α 1 = β 1 ∧
      (∃ y : ↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M),
        α (SemidirectProduct.inl y) ≠ α 1) ∧
      (∃ y : ↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M),
        β (SemidirectProduct.inl y) ≠ β 1) ∧
      α ∘ modelConjAutM hc hprime hAeq hAH hAM w₀ = α ∧
      β ∘ modelConjAutM hc hprime hAeq hAH hAM w₀ ≠ β := by
  obtain ⟨-, hUne, hUab, -, -, -⟩ := h.clauses_of_isWitnessedPConfiguration hsolv hc
  have hptype := hc.isPTypeConfig hsolv hprime hUne
  let _ := hchief.normal_num
  let _ := hp
  let _ : Fact (Nat.card W₁).Prime := ⟨hprime⟩
  have hqcard : Nat.card ↥(W₁.subgroupOf M) = Nat.card W₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le_M_W₁).toEquiv
  obtain ⟨b, hbB, hb1, -⟩ := exists_zpowers_eq_of_prime_natCard hptype.prime_natCard_B
  set D := hptype.linearModel (p := p) hqcard hchief hCU hbB hb1 e with hDdef
  have hDA : D.A = ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀
      (U.subgroupOf M) e := hptype.linearModel_A hqcard hchief hCU hbB hb1 e
  have hDb : D.b = ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b :=
    hptype.linearModel_b hqcard hchief hCU hbB hb1 e
  obtain ⟨s, hs0, hsfix⟩ := D.exists_ne_zero_fixed
  rw [hDb] at hsfix
  have hpq : p ≠ (Nat.card W₁) := (D.ne_char).symm
  have : Nontrivial (Fin (Nat.card W₁) → ZMod p) := D.nontrivial
  set w₀ : ↥W₁ := ⟨(b : G), (Subgroup.mem_subgroupOf).1 hbB⟩ with hw₀def
  have hw₀ : w₀ ≠ 1 := fun hcon => hb1 (Subtype.ext (by
    have hz := congrArg (fun z : ↥W₁ => (z : G)) hcon
    simpa [hw₀def] using hz))
  have hw₀b : (⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩ : ↥M) = b := Subtype.ext rfl
  have hbcard : b ^ (Nat.card W₁) = 1 := by
    have hb' : (⟨b, hbB⟩ : ↥(W₁.subgroupOf M)) ^ (Nat.card ↥(W₁.subgroupOf M)) = 1 :=
      pow_card_eq_one'
    rw [hqcard] at hb'
    simpa [Subtype.ext_iff] using hb'
  have hbq : (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b) ^ (Nat.card W₁)
      = 1 := by rw [← map_pow, hbcard, map_one]
  have : IsMulCommutative ↥(U.subgroupOf M) := isMulCommutative_subgroupOf_of_le hc.le_M_E hUab
  set σ : MulAut ↥(U.subgroupOf M) := conjOnNormalized (U.subgroupOf M)
    (le_normalizer_subgroupOf_E_W₁ hc) ⟨⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩,
      (Subgroup.mem_subgroupOf).2 w₀.2⟩ with hσdef
  set r : ↥(U.subgroupOf M) →*
      ((Fin (Nat.card W₁) → ZMod p) ≃ₗ[ZMod p] (Fin (Nat.card W₁) → ZMod p)) :=
    (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e).comp
      (U.subgroupOf M).subtype with hrdef
  have hC : MonoidHom.ker r ≠ ⊥ := by rwa [hrdef, ← actionKernel_eq_ker p e]
  have hrange : MonoidHom.range r = D.A := by
    rw [hrdef, range_comp_subtype_eq_factorLinearImage, hDA]
  have : IsMulCommutative ↥D.A := D.isMulCommutative_A
  have : (linearGroupRep D.A).IsIrreducible := hDA ▸ hirr
  have hDfpf : ∀ d ∈ MonoidHom.range r, d ≠ 1 →
      ∀ v : (Fin (Nat.card W₁) → ZMod p), d v = v → v = 0 := by
    intro d hd hd1 v hv
    rw [hrange] at hd
    exact eq_zero_of_apply_eq_of_isIrreducible hd hd1 hv
  have hσq : σ ^ (Nat.card W₁) = 1 := by
    rw [hσdef, ← map_pow]
    have hb' : (⟨⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩, (Subgroup.mem_subgroupOf).2 w₀.2⟩ :
        ↥(W₁.subgroupOf M)) ^ (Nat.card W₁) = 1 := by
      rw [← hqcard]; exact pow_card_eq_one'
    rw [hb', map_one]
  have hσfix : ∀ u : ↥(U.subgroupOf M), σ u = u → u = 1 := fun u hu =>
    eq_one_of_conjOnNormalized_subgroupOf_M_eq_self hc hw₀ u hu
  have hσ1 : σ ≠ 1 := by
    intro hcon
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUne
    set u : ↥(U.subgroupOf M) :=
      ⟨⟨(x : G), hc.le_M_E x.2⟩, (Subgroup.mem_subgroupOf).2 x.2⟩ with hudef
    have hu1 : u ≠ 1 := by
      intro hcon2
      refine hx1 (Subtype.ext ?_)
      have hz := congrArg (fun z : ↥(U.subgroupOf M) => ((z : ↥M) : G)) hcon2
      simpa [hudef] using hz
    exact hu1 (hσfix u (by rw [hcon]; rfl))
  have hrcompat : ∀ u : ↥(U.subgroupOf M),
      r (σ u) = (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b) * r u *
        (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b)⁻¹ := by
    intro u
    have hcoe : ((σ u : ↥(U.subgroupOf M)) : ↥M)
        = (⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩ : ↥M) * (u : ↥M)
          * (⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩ : ↥M)⁻¹ :=
      conjOnNormalized_apply_coe (le_normalizer_subgroupOf_E_W₁ hc)
        (⟨⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩, (Subgroup.mem_subgroupOf).2 w₀.2⟩ :
          ↥(W₁.subgroupOf M)) u
    change ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e
      ((σ u : ↥(U.subgroupOf M)) : ↥M) = _
    rw [hcoe, map_mul, map_mul, map_inv, hw₀b]
    rfl
  obtain ⟨α, hα, β, hβ, hdeg, hdα, hdβ, hinvα, hmovβ⟩ :=
    exists_pair_of_mulEquiv_semi hp.out hprime hpq (not_natCard_W₁_dvd_natCard_subgroupOf_E hc)
      (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b) hbq hs0 hsfix
      σ hσq hσ1 hσfix r hrcompat hC hDfpf
      (modelEquivLinear p M U e) (modelConjAutM hc hprime hAeq hAH hAM w₀)
      (fun v => by
        rw [modelEquivLinear_symm_inl, modelConjAutM_inl, modelEquivLinear_inl, hw₀b,
          ChiefFactorFaithfulImage.factorLinearAut_apply' p e b v]
        rfl)
      (fun u => by rw [modelEquivLinear_symm_inr, modelConjAutM_inr, modelEquivLinear_inr, hσdef])
  refine ⟨w₀, hw₀, α, hα, β, hβ, hdeg, ?_, ?_, hinvα, hmovβ⟩
  · obtain ⟨v, hv⟩ := hdα
    exact ⟨e.symm (Multiplicative.ofAdd v), by rwa [← modelEquivLinear_symm_inl p M U e]⟩
  · obtain ⟨v, hv⟩ := hdβ
    exact ⟨e.symm (Multiplicative.ofAdd v), by rwa [← modelEquivLinear_symm_inl p M U e]⟩

omit [Finite G] in
theorem exists_basis_succ_eq_of_isInternal {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] {q : ℕ} [NeZero q] {b : V ≃ₗ[k] V} (hbq : b ^ q = 1)
    {L : ZMod q → Submodule k V} (hL1 : ∀ i, Module.finrank k (L i) = 1)
    (hLint : DirectSum.IsInternal L)
    (hLb : ∀ i, (L i).map (b : V →ₗ[k] V) = L (i + 1)) :
    ∃ eb : Module.Basis (ZMod q) k V, (∀ i, eb (i + 1) = b (eb i)) ∧ ∀ i, eb i ∈ L i := by
  classical
  have hL0 : L 0 ≠ ⊥ := by
    intro h; have := hL1 0; rw [h, finrank_bot] at this; exact zero_ne_one this
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  have hmem : ∀ n : ℕ, (b ^ n) v₀ ∈ L (n : ZMod q) := by
    intro n
    induction n with
    | zero => simpa using hv₀
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, Nat.cast_succ, ← hLb]
      exact ⟨_, ih, rfl⟩
  set w : ZMod q → V := fun i => (b ^ i.val) v₀ with hw
  have hwmem : ∀ i, w i ∈ L i := fun i => by
    have := hmem i.val; rwa [ZMod.natCast_zmod_val] at this
  have hwne : ∀ i, w i ≠ 0 := fun i h =>
    hv₀0 ((LinearEquiv.map_eq_zero_iff (b ^ i.val)).1 h)
  have hli : LinearIndependent k w :=
    iSupIndep.linearIndependent L hLint.submodule_iSupIndep hwmem hwne
  have hspan : (⊤ : Submodule k V) ≤ Submodule.span k (Set.range w) := by
    rw [← hLint.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    rw [eq_span_singleton_of_mem_of_finrank_eq_one (hL1 i) (hwmem i) (hwne i)]
    exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨i, rfl⟩)
  refine ⟨Module.Basis.mk hli hspan, fun i => ?_,
    fun i => by rw [Module.Basis.mk_apply]; exact hwmem i⟩
  rw [Module.Basis.mk_apply, Module.Basis.mk_apply, hw]
  simp only
  rw [← LinearEquiv.mul_apply, ← pow_succ', pow_eq_pow_mod (i + 1).val hbq,
    pow_eq_pow_mod (i.val + 1) hbq, ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_mod,
    Nat.add_mod i.val, Nat.mod_mod, ← Nat.add_mod]

omit [Finite G] in
theorem shift_eq_of_basis_succ_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {q : ℕ} {b : V ≃ₗ[k] V} {eb : Module.Basis (ZMod q) k V}
    (h : ∀ i, eb (i + 1) = b (eb i)) : shift eb = b :=
  eb.ext' fun i => by rw [shift_basis, h]

omit [Finite G] in
theorem mem_diagAutSubgroup_of_map_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {q : ℕ} {eb : Module.Basis (ZMod q) k V} {L : ZMod q → Submodule k V}
    (hL1 : ∀ i, Module.finrank k (L i) = 1) (hmem : ∀ i, eb i ∈ L i) {d : V ≃ₗ[k] V}
    (hd : ∀ i, (L i).map (d : V →ₗ[k] V) = L i) : d ∈ diagAutSubgroup eb := by
  refine mem_diagAutSubgroup_iff.2 fun i => ?_
  have hne : eb i ≠ 0 := eb.ne_zero i
  have h1 : d (eb i) ∈ L i := by rw [← hd i]; exact ⟨_, hmem i, rfl⟩
  rw [eq_span_singleton_of_mem_of_finrank_eq_one (hL1 i) (hmem i) hne,
    Submodule.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, hc.symm⟩

omit [Finite G] in
theorem exists_pair_of_mulEquiv_diagonal {p q : ℕ} [Fact p.Prime] (hp : Odd p) (hq : q.Prime)
    {E : Type*} [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    {V : Type*} [Group V] [Finite V] (hVodd : Odd (Nat.card V)) (hqV : ¬ q ∣ Nat.card V)
    (eb : Module.Basis (ZMod q) (ZMod p) E) (b : E ≃ₗ[ZMod p] E) (hb : shift eb = b)
    (σ : MulAut V) (hσq : σ ^ q = 1)
    (r : V →* (E ≃ₗ[ZMod p] E)) (hr : ∀ w : V, r (σ w) = b * r w * b⁻¹)
    (hD : r.range ≤ diagAutSubgroup eb)
    (hcent : ∀ d ∈ r.range, d * b = b * d → d = 1)
    {X : Type*} [Group X]
    (f : X ≃* (Multiplicative E ⋊[FixedFreeImage.mulAutMultiplicative.comp r] V)) (τ : MulAut X)
    (hτl : ∀ v : E, f (τ (f.symm (SemidirectProduct.inl (Multiplicative.ofAdd v))))
      = SemidirectProduct.inl (Multiplicative.ofAdd (b v)))
    (hτr : ∀ u : V, f (τ (f.symm (SemidirectProduct.inr u))) = SemidirectProduct.inr (σ u)) :
    ∃ α ∈ Irr X, ∃ β ∈ Irr X, α 1 = β 1 ∧
      (∃ v : E, α (f.symm (SemidirectProduct.inl (Multiplicative.ofAdd v))) ≠ α 1) ∧
      (∃ v : E, β (f.symm (SemidirectProduct.inl (Multiplicative.ofAdd v))) ≠ β 1) ∧
      α ∘ τ = α ∧ β ∘ τ ≠ β := by
  classical
  have hq0 : NeZero q := ⟨hq.ne_zero⟩
  have : Fact (1 < q) := ⟨hq.one_lt⟩
  let _ : Fintype E := Fintype.ofFinite E
  let _ : Fintype V := Fintype.ofFinite V
  have hbq : b ^ q = 1 := by rw [← hb]; exact shift_pow_eq_one eb
  have hσpow : ∀ (n : ℕ) (w : V), r ((σ ^ n) w) = b ^ n * r w * (b ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih => intro w; rw [pow_succ' σ, MulAut.mul_apply, hr, ih, pow_succ' b]; group
  set bh := zmodPowHom hbq with hbh
  set σh := zmodPowHom hσq with hσh
  have hbh1 : bh (Multiplicative.ofAdd 1) = b := zmodPowHom_one_gen hq.one_lt hbq
  have hσh1 : σh (Multiplicative.ofAdd 1) = σ := zmodPowHom_one_gen hq.one_lt hσq
  have hr' : ∀ g : DiagonalCore.Cyc q, ((r.range.subtype).comp r.rangeRestrict).comp
      (σh g).toMonoidHom
      = (MulAut.conj (bh g)).toMonoidHom.comp ((r.range.subtype).comp r.rangeRestrict) := by
    intro g
    refine MonoidHom.ext fun w => ?_
    have h1 : σh g = σ ^ (Multiplicative.toAdd g).val := zmodPowHom_apply hσq _
    have h2 : bh g = b ^ (Multiplicative.toAdd g).val := zmodPowHom_apply hbq _
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, h1, h2,
      Subgroup.coe_subtype, MonoidHom.coe_rangeRestrict]
    rw [hσpow, MulAut.conj_apply]
  have hDodd : Odd (Nat.card r.range) := hVodd.of_dvd_nat (Subgroup.card_range_dvd r)
  have hqD : ¬ q ∣ Nat.card r.range := fun h => hqV (h.trans (Subgroup.card_range_dvd r))
  have hcent' : ∀ d : r.range, (d : E ≃ₗ[ZMod p] E) * shift eb = shift eb * d → d = 1 :=
    fun d hd => Subtype.ext (hcent d d.2 (hb ▸ hd))
  obtain ⟨ψα, ψβ, -, -, -, -, -, hrest⟩ :=
    DiagonalCore.exists_equal_degree_invariant_and_moving_pair eb hD hp hq hDodd hqD hcent'
      hVodd hqV r.rangeRestrict_surjective (b := bh) (by rw [hbh1, hb]) hr'
  obtain ⟨hαI, hβI, hdα, hdβ, hEα, hEβ, hinv, hinj, -⟩ := hrest
  have hcompat : ∀ g : V, (MonoidHom.id (Multiplicative E)).comp
      ((FixedFreeImage.mulAutMultiplicative.comp r) g).toMonoidHom
      = (DiagonalCore.semidirectAut r.rangeRestrict bh hr'
          ((SemidirectProduct.inl : V →* V ⋊[σh] DiagonalCore.Cyc q) g)).toMonoidHom.comp
          (MonoidHom.id _) := by
    intro g
    refine MonoidHom.ext fun m => ?_
    change FixedFreeImage.mulAutMultiplicative (r g) m
      = DiagonalCore.semidirectAut r.rangeRestrict bh hr' (SemidirectProduct.inl g)
          (Multiplicative.ofAdd (Multiplicative.toAdd m))
    rw [DiagonalCore.semidirectAut_apply, DiagonalCore.toGL_inl,
      FixedFreeImage.mulAutMultiplicative_apply]
    rfl
  set Φ := SemidirectProduct.map (MonoidHom.id (Multiplicative E))
    (SemidirectProduct.inl : V →* V ⋊[σh] DiagonalCore.Cyc q) hcompat with hΦ
  have hΦmem : ∀ x, Φ x ∈ DiagonalCore.coreSub r.rangeRestrict bh hr' := fun x => by
    rw [DiagonalCore.mem_coreSub_iff, SemidirectProduct.map_right]
    rfl
  have hΦinj : Function.Injective (Φ.codRestrict _ hΦmem) := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    simp only [MonoidHom.codRestrict_apply] at h
    have h1 := congrArg SemidirectProduct.left h
    have h2 := congrArg (fun z => z.right.left) h
    simp only [hΦ, SemidirectProduct.map_left, SemidirectProduct.map_right,
      SemidirectProduct.left_inl, MonoidHom.id_apply] at h1 h2
    exact SemidirectProduct.ext h1 h2
  have hΦsurj : Function.Surjective (Φ.codRestrict _ hΦmem) := by
    intro k
    refine ⟨⟨(k : DiagonalCore.Amb r.rangeRestrict bh hr').left,
      (k : DiagonalCore.Amb r.rangeRestrict bh hr').right.left⟩, Subtype.ext ?_⟩
    have hk : (k : DiagonalCore.Amb r.rangeRestrict bh hr').right.right = 1 :=
      DiagonalCore.mem_coreSub_iff.1 k.2
    simp only [MonoidHom.codRestrict_apply]
    refine SemidirectProduct.ext ?_ ?_
    · rw [hΦ, SemidirectProduct.map_left]; rfl
    · rw [hΦ, SemidirectProduct.map_right]
      exact SemidirectProduct.ext rfl (by rw [hk]; rfl)
  set Ψ := MulEquiv.ofBijective (Φ.codRestrict _ hΦmem) ⟨hΦinj, hΦsurj⟩ with hΨdef
  have hΨ : ∀ x, ((Ψ x : DiagonalCore.coreSub r.rangeRestrict bh hr') :
      DiagonalCore.Amb r.rangeRestrict bh hr') = Φ x := fun x => rfl
  set t : DiagonalCore.Amb r.rangeRestrict bh hr' :=
    SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd 1)) with ht
  have keyy : ∀ y, Ψ (f (τ (f.symm y))) = MulAut.conjNormal t (Ψ y) := by
    have hext := SemidirectProduct.hom_ext
      (f := Ψ.toMonoidHom.comp (f.toMonoidHom.comp (τ.toMonoidHom.comp f.symm.toMonoidHom)))
      (g := (MulAut.conjNormal t).toMonoidHom.comp Ψ.toMonoidHom) ?_ ?_
    · intro y
      exact DFunLike.congr_fun hext y
    · refine MonoidHom.ext fun m => Subtype.ext ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [show m = Multiplicative.ofAdd (Multiplicative.toAdd m) from rfl, hτl, hΨ,
        MulAut.conjNormal_apply, hΨ, hΦ, SemidirectProduct.map_inl, SemidirectProduct.map_inl,
        ht, ← map_inv, ← SemidirectProduct.inl_aut]
      congr 1
      change _ = DiagonalCore.semidirectAut r.rangeRestrict bh hr' _
        (Multiplicative.ofAdd (Multiplicative.toAdd m))
      rw [DiagonalCore.semidirectAut_apply, DiagonalCore.toGL_inr, hbh1]
      rfl
    · refine MonoidHom.ext fun u => Subtype.ext ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hτr, hΨ, MulAut.conjNormal_apply, hΨ, hΦ, SemidirectProduct.map_inr,
        SemidirectProduct.map_inr, ht, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [← map_inv, ← SemidirectProduct.inl_aut, hσh1]
  have key : ∀ x : X, (f.trans Ψ) (τ x) = MulAut.conjNormal t ((f.trans Ψ) x) := by
    intro x
    have h := keyy (f x)
    rwa [MulEquiv.symm_apply_apply] at h
  set αK := indClassFun ((DiagonalCore.tSub r.rangeRestrict bh hr').subgroupOf
    (DiagonalCore.coreSub r.rangeRestrict bh hr')) ψα with hαK
  set βK := indClassFun ((DiagonalCore.tSub r.rangeRestrict bh hr').subgroupOf
    (DiagonalCore.coreSub r.rangeRestrict bh hr')) ψβ with hβK
  have hsymm_inl : ∀ v : E, (f.trans Ψ) (f.symm (SemidirectProduct.inl (Multiplicative.ofAdd v)))
      = Ψ (SemidirectProduct.inl (Multiplicative.ofAdd v)) := fun v => by
    simp
  have hEsub : ∀ x : DiagonalCore.coreSub r.rangeRestrict bh hr',
      (x : DiagonalCore.Amb r.rangeRestrict bh hr') ∈ DiagonalCore.eSub r.rangeRestrict bh hr' →
      Ψ (SemidirectProduct.inl (Multiplicative.ofAdd (Multiplicative.toAdd
        (x : DiagonalCore.Amb r.rangeRestrict bh hr').left))) = x := by
    intro x hx
    have h1 := DiagonalCore.mem_eSub_iff.1 hx
    refine Subtype.ext (SemidirectProduct.ext ?_ ?_)
    · rw [hΨ, hΦ, SemidirectProduct.map_inl]; rfl
    · rw [hΨ, hΦ, SemidirectProduct.map_inl, h1]; rfl
  have hconjinv : ∀ χ : DiagonalCore.coreSub r.rangeRestrict bh hr' → ℂ,
      NormalInduction.conjClassFun _ t⁻¹ χ = χ ∘ MulAut.conjNormal t := by
    intro χ
    funext k
    rw [NormalInduction.conjClassFun_apply, inv_inv]
    rfl
  refine ⟨αK ∘ (f.trans Ψ), FrobeniusInduction.mem_Irr_comp_mulEquiv hαI _,
    βK ∘ (f.trans Ψ), FrobeniusInduction.mem_Irr_comp_mulEquiv hβI _, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, map_one, hdα, hdβ]
  · obtain ⟨x, hxm, hx⟩ := hEα
    refine ⟨Multiplicative.toAdd (x : DiagonalCore.Amb r.rangeRestrict bh hr').left, ?_⟩
    simp only [Function.comp_apply, map_one, hsymm_inl]
    rw [hEsub x hxm]
    exact hx
  · obtain ⟨x, hxm, hx⟩ := hEβ
    refine ⟨Multiplicative.toAdd (x : DiagonalCore.Amb r.rangeRestrict bh hr').left, ?_⟩
    simp only [Function.comp_apply, map_one, hsymm_inl]
    rw [hEsub x hxm]
    exact hx
  · funext x
    simp only [Function.comp_apply]
    rw [key x]
    have h := congrFun (hinv t⁻¹) ((f.trans Ψ) x)
    rw [hconjinv] at h
    exact h
  · intro hcon
    have h01 : (Multiplicative.ofAdd (-1 : ZMod q) : DiagonalCore.Cyc q)
        = (Multiplicative.ofAdd 1)⁻¹ := rfl
    have hne : (-1 : ZMod q) ≠ 0 := neg_ne_zero.2 one_ne_zero
    refine hne (hinj ?_)
    simp only
    rw [h01, map_inv, map_inv, ← ht, hconjinv]
    funext k
    obtain ⟨x, rfl⟩ := (f.trans Ψ).surjective k
    have h1 := congrFun hcon x
    simp only [Function.comp_apply] at h1
    rw [key x] at h1
    rw [Function.comp_apply, h1]
    have h0 : (Multiplicative.ofAdd (0 : ZMod q) : DiagonalCore.Cyc q) = 1 := rfl
    rw [h0, map_one, map_one, NormalInduction.conjClassFun_apply, inv_one, map_one]
    rfl

theorem exists_modelPair_of_actsReducibly (h : IsTypeII M) (hodd : Odd (Nat.card G))
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUnc : ¬ IsCyclic U)
    (hprime : (Nat.card W₁).Prime)
    {H₀ : Subgroup ↥M} [H₀.Normal] (hchief : IsChiefFactor (hallCore ↥M) H₀)
    (hCU : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ H₀)
    {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G))
    {p : ℕ} (hp : Fact p.Prime)
    (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃*
      Multiplicative (Fin (Nat.card W₁) → ZMod p))
    (hred : ActsReducibly
      (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀ (U.subgroupOf M) e)) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    ∃ a' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      ∃ b' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      a' 1 = b' 1 ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        a' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ a' 1) ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        b' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ b' 1) ∧
      (∀ w : W₁,
        a' ∘ semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w = a') ∧
      ∃ w : W₁,
        b' ∘ semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w ≠ b' := by
  obtain ⟨-, hUne, hUab, -, -, -⟩ := h.clauses_of_isWitnessedPConfiguration hsolv hc
  have hptype := hc.isPTypeConfig hsolv hprime hUne
  let _ := hchief.normal_num
  let _ := hp
  let _ : Fact (Nat.card W₁).Prime := ⟨hprime⟩
  have : NeZero (Nat.card W₁) := ⟨hprime.ne_zero⟩
  have hqcard : Nat.card ↥(W₁.subgroupOf M) = Nat.card W₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le_M_W₁).toEquiv
  obtain ⟨b, hbB, hb1, -⟩ := exists_zpowers_eq_of_prime_natCard hptype.prime_natCard_B
  set D := hptype.linearModel (p := p) hqcard hchief hCU hbB hb1 e with hDdef
  have hDA : D.A = ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀
      (U.subgroupOf M) e := hptype.linearModel_A hqcard hchief hCU hbB hb1 e
  have hDb : D.b = ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b :=
    hptype.linearModel_b hqcard hchief hCU hbB hb1 e
  obtain ⟨L, -, hL1, hLA, hLb, hLint, -⟩ := D.reducible_model (hDA ▸ hred)
  have hDbq : D.b ^ (Nat.card W₁) = 1 := by
    have h := pow_orderOf_eq_one D.b
    rwa [D.orderOf_b] at h
  obtain ⟨eb, hebsucc, hebmem⟩ := exists_basis_succ_eq_of_isInternal hDbq hL1 hLint hLb
  have hshift : shift eb = ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b := by
    rw [← hDb]; exact shift_eq_of_basis_succ_eq hebsucc
  have hpodd : Odd p := by
    refine hodd.of_dvd_nat ?_
    have h1 : Nat.card (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) = p ^ Nat.card W₁ := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin (Nat.card W₁) → ZMod p) = _
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h2 : p ∣ Nat.card (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) := by
      rw [h1]; exact dvd_pow_self p hprime.ne_zero
    exact h2.trans ((Subgroup.card_quotient_dvd_card _).trans
      ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card M)))
  have hUodd : Odd (Nat.card ↥(U.subgroupOf M)) :=
    hodd.of_dvd_nat ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card M))
  set w₀ : ↥W₁ := ⟨(b : G), (Subgroup.mem_subgroupOf).1 hbB⟩ with hw₀def
  have hw₀ : w₀ ≠ 1 := fun hcon => hb1 (Subtype.ext (by
    have hz := congrArg (fun z : ↥W₁ => (z : G)) hcon
    simpa [hw₀def] using hz))
  have hw₀b : (⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩ : ↥M) = b := Subtype.ext rfl
  set σ : MulAut ↥(U.subgroupOf M) := conjOnNormalized (U.subgroupOf M)
    (le_normalizer_subgroupOf_E_W₁ hc) ⟨⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩,
      (Subgroup.mem_subgroupOf).2 w₀.2⟩ with hσdef
  set r : ↥(U.subgroupOf M) →*
      ((Fin (Nat.card W₁) → ZMod p) ≃ₗ[ZMod p] (Fin (Nat.card W₁) → ZMod p)) :=
    (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e).comp
      (U.subgroupOf M).subtype with hrdef
  have hrange : MonoidHom.range r = D.A := by
    rw [hrdef, range_comp_subtype_eq_factorLinearImage, hDA]
  have hσq : σ ^ (Nat.card W₁) = 1 := by
    rw [hσdef, ← map_pow]
    have hb' : (⟨⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩, (Subgroup.mem_subgroupOf).2 w₀.2⟩ :
        ↥(W₁.subgroupOf M)) ^ (Nat.card W₁) = 1 := by
      rw [← hqcard]; exact pow_card_eq_one'
    rw [hb', map_one]
  have hrcompat : ∀ u : ↥(U.subgroupOf M),
      r (σ u) = (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b) * r u *
        (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b)⁻¹ := by
    intro u
    have hcoe : ((σ u : ↥(U.subgroupOf M)) : ↥M)
        = (⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩ : ↥M) * (u : ↥M)
          * (⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩ : ↥M)⁻¹ :=
      conjOnNormalized_apply_coe (le_normalizer_subgroupOf_E_W₁ hc)
        (⟨⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩, (Subgroup.mem_subgroupOf).2 w₀.2⟩ :
          ↥(W₁.subgroupOf M)) u
    change ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e
      ((σ u : ↥(U.subgroupOf M)) : ↥M) = _
    rw [hcoe, map_mul, map_mul, map_inv, hw₀b]
    rfl
  have hDdiag : MonoidHom.range r ≤ diagAutSubgroup eb := by
    intro d hd
    rw [hrange] at hd
    exact mem_diagAutSubgroup_of_map_eq hL1 hebmem (hLA d hd)
  have hcent : ∀ d ∈ MonoidHom.range r,
      d * ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b
        = ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b * d → d = 1 := by
    intro d hd hdb
    rw [hrange] at hd
    rw [← hDb] at hdb
    exact D.eq_one_of_commute hd hdb
  obtain ⟨α, hα, β, hβ, hdeg, hdα, hdβ, hinvα, hmovβ⟩ :=
    exists_pair_of_mulEquiv_diagonal hpodd hprime hUodd (not_natCard_W₁_dvd_natCard_subgroupOf_E hc)
      eb (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H₀ e b) hshift
      σ hσq r hrcompat hDdiag hcent
      (modelEquivLinear p M U e) (modelConjAutM hc hprime hAeq hAH hAM w₀)
      (fun v => by
        rw [modelEquivLinear_symm_inl, modelConjAutM_inl, modelEquivLinear_inl, hw₀b,
          ChiefFactorFaithfulImage.factorLinearAut_apply' p e b v]
        rfl)
      (fun u => by rw [modelEquivLinear_symm_inr, modelConjAutM_inr, modelEquivLinear_inr, hσdef])
  refine exists_modelPair_of_modelM hc hprime hAeq hAH hAM hw₀ hα hβ hdeg ?_ ?_ hinvα hmovβ
  · obtain ⟨v, hv⟩ := hdα
    exact ⟨e.symm (Multiplicative.ofAdd v), by rwa [← modelEquivLinear_symm_inl p M U e]⟩
  · obtain ⟨v, hv⟩ := hdβ
    exact ⟨e.symm (Multiplicative.ofAdd v), by rwa [← modelEquivLinear_symm_inl p M U e]⟩

theorem exists_modelPair_of_isIrreducible (h : IsTypeII M)
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUnc : ¬ IsCyclic U)
    (hprime : (Nat.card W₁).Prime)
    {H₀ : Subgroup ↥M} [H₀.Normal] (hchief : IsChiefFactor (hallCore ↥M) H₀)
    (hCU : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ H₀)
    {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G))
    {p : ℕ} (hp : Fact p.Prime)
    (e : (↥(hallCore ↥M) ⧸ H₀.subgroupOf (hallCore ↥M)) ≃*
      Multiplicative (Fin (Nat.card W₁) → ZMod p))
    (hirr : (linearGroupRep (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H₀
      (U.subgroupOf M) e)).IsIrreducible)
    (hker : ChiefFactorFaithfulImage.actionKernel p (hallCore ↥M) H₀ (U.subgroupOf M) e ≠ ⊥) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    ∃ a' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      ∃ b' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      a' 1 = b' 1 ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        a' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ a' 1) ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        b' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ b' 1) ∧
      (∀ w : W₁,
        a' ∘ semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w = a') ∧
      ∃ w : W₁,
        b' ∘ semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w ≠ b' := by
  obtain ⟨w₀, hw₀, α, hα, β, hβ, hdeg, hdα, hdβ, hinvα, hmovβ⟩ :=
    exists_modelPairM_of_isIrreducible h hsolv hc hprime hchief hCU hAeq hAH hAM hp e hirr hker
  exact exists_modelPair_of_modelM hc hprime hAeq hAH hAM hw₀ hα hβ hdeg hdα hdβ hinvα hmovβ

theorem exists_modelPair_of_isChiefFactor (h : IsTypeII M) (hodd : Odd (Nat.card G))
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUnc : ¬ IsCyclic U)
    (hprime : (Nat.card W₁).Prime)
    {H₀ : Subgroup ↥M} [H₀.Normal] (hchief : IsChiefFactor (hallCore ↥M) H₀)
    (hCU : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ H₀)
    {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G)) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    ∃ a' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      ∃ b' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      a' 1 = b' 1 ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        a' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ a' 1) ∧
      (∃ hh : ↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)),
        b' (SemidirectProduct.inl (QuotientGroup.mk hh)) ≠ b' 1) ∧
      (∀ w : W₁,
        a' ∘ semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w = a') ∧
      ∃ w : W₁,
        b' ∘ semidirectQuotientConjAut hc hprime hAH (hc.le_M_W₁.trans hAM) w ≠ b' := by
  obtain ⟨p, hp, e, hcase⟩ :=
    exists_actsReducibly_or_isIrreducible_actionKernel_ne_bot h hsolv hc hUnc hchief hCU
  rcases hcase with hred | ⟨hirr, hker⟩
  · exact exists_modelPair_of_actsReducibly h hodd hsolv hc hUnc hprime hchief hCU hAeq hAH hAM hp
      e hred
  · exact exists_modelPair_of_isIrreducible h hsolv hc hUnc hprime hchief hCU hAeq hAH hAM hp e
      hirr hker

theorem exists_weakPairSemidirect_of_isChiefFactor (h : IsTypeII M) (hodd : Odd (Nat.card G))
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUnc : ¬ IsCyclic U)
    {H₀ : Subgroup ↥M} [H₀.Normal] (hchief : IsChiefFactor (hallCore ↥M) H₀)
    (hCU : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ H₀)
    {A : Subgroup G} (hAeq : A = H₀.map M.subtype)
    (hAH : A ≤ (hallCore M).map M.subtype) (hAM : M ≤ normalizer (A : Set G)) :
    letI := hc.normal_subgroupOf_hallCore
    letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
    ∃ a' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      ∃ b' ∈ Irr ((↥(((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)) ⧸
          (A.subgroupOf (⁅M, M⁆ : Subgroup G)).subgroupOf
            (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)))
        ⋊[conjQuotAutRestrict (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G))
            (A.subgroupOf (⁅M, M⁆ : Subgroup G)) (U.subgroupOf (⁅M, M⁆ : Subgroup G))]
          ↥(U.subgroupOf (⁅M, M⁆ : Subgroup G))),
      a' 1 = b' 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
        a' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x)) ≠ a' 1) ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∈ (hallCore M).map M.subtype ∧
        b' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x)) ≠ b' 1) ∧
      (∀ (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)),
        a' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk
            (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x)))
          = a' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x))) ∧
      ∃ (w : W₁) (x : ↥(⁅M, M⁆ : Subgroup G)),
        b' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk
            (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁ w x)))
          ≠ b' ((semidirectQuotientEquiv hc hAH).symm (QuotientGroup.mk x)) := by
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  have hprime : (Nat.card W₁).Prime :=
    (h.clauses_of_isWitnessedPConfiguration hsolv hc).1.prime_natCard_W₁
  obtain ⟨a', ha', b', hb', hdeg, hdeta', hdetb', hinva', hmovb'⟩ :=
    exists_modelPair_of_isChiefFactor h hodd hsolv hc hUnc hprime hchief hCU hAeq hAH hAM
  exact exists_weakPairSemidirect_of_comp_semidirectQuotientConjAut hc hprime hAH
    (hc.le_M_W₁.trans hAM) ha' hb' hdeg hdeta' hdetb' hinva' hmovb'

theorem exists_weakEqualDegreeCharacterPair_of_forall_apply_eq_zero (h : IsTypeII M)
    (hodd : Odd (Nat.card G))
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUnc : ¬ IsCyclic U)
    {α : ↥(⁅M, M⁆ : Subgroup G) → ℂ} (hα : α ∈ Irr (⁅M, M⁆ : Subgroup G)) (hα1 : α ≠ 1)
    (hdetα : ∃ x : ↥(⁅M, M⁆ : Subgroup G),
      (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel α)
    (hinvα : ∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w α = α)
    (hvan : ∀ x : ↥(⁅M, M⁆ : Subgroup G), (x : G) ∉ (hallCore M).map M.subtype → α x = 0) :
    ∃ a ∈ Irr (⁅M, M⁆ : Subgroup G), ∃ b ∈ Irr (⁅M, M⁆ : Subgroup G),
      a 1 = b 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel a) ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel b) ∧
      (∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w a = a) ∧
      ∃ w : W₁, charConj hc.le_normalizer_commutator_W₁ w b ≠ b := by
  obtain ⟨hpc, hUne, -, -, -, -⟩ := h.clauses_of_isWitnessedPConfiguration hsolv hc
  obtain ⟨H₀, hchief, hCU⟩ :=
    (hc.isPTypeConfig hsolv hpc.prime_natCard_W₁ hUne).exists_isChiefFactor
  letI := hchief.normal_den
  have hAH : H₀.map M.subtype ≤ (hallCore M).map M.subtype := Subgroup.map_mono hchief.le
  have hAM : M ≤ normalizer ((H₀.map M.subtype : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_of_normal ‹H₀.Normal›
  letI := hc.normal_subgroupOf_hallCore
  letI := normal_subgroupOf_commutator_of_le_normalizer hc hAH hAM
  obtain ⟨a', ha', b', hb', hdeg, hdeta', hdetb', hinva', hmovb'⟩ :=
    exists_weakPairSemidirect_of_isChiefFactor h hodd hsolv hc hUnc hchief hCU rfl hAH hAM
  exact exists_weakPair_of_mulEquiv hc (semidirectQuotientEquiv hc hAH)
    ha' hb' hdeg hdeta' hdetb' hinva' hmovb'

theorem exists_weakEqualDegreeCharacterPair_of_not_isCyclic (h : IsTypeII M)
    (hodd : Odd (Nat.card G))
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUnc : ¬ IsCyclic U) :
    ∃ α ∈ Irr (⁅M, M⁆ : Subgroup G), ∃ β ∈ Irr (⁅M, M⁆ : Subgroup G),
      α 1 = β 1 ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel α) ∧
      (∃ x : ↥(⁅M, M⁆ : Subgroup G),
        (x : G) ∈ (hallCore M).map M.subtype ∧ x ∉ charValueKernel β) ∧
      (∀ w : W₁, charConj hc.le_normalizer_commutator_W₁ w α = α) ∧
      ∃ w : W₁, charConj hc.le_normalizer_commutator_W₁ w β ≠ β := by
  obtain ⟨hpc, -, hUab, -, -, -⟩ := h.clauses_of_isWitnessedPConfiguration hsolv hc
  have hprime := hpc.prime_natCard_W₁
  obtain ⟨α, hα, hα1, hdetα, hinvα⟩ :=
    exists_invariant_mem_Irr_notMem_charValueKernel hc hprime
  by_cases hvan : ∃ x₀ : ↥(⁅M, M⁆ : Subgroup G),
      (x₀ : G) ∉ (hallCore M).map M.subtype ∧ α x₀ ≠ 0
  · obtain ⟨x₀, hx₀, hx₀0⟩ := hvan
    exact exists_weakPair_of_invariant_of_apply_ne_zero hc hprime hUab hα hinvα hdetα hx₀ hx₀0
  · refine exists_weakEqualDegreeCharacterPair_of_forall_apply_eq_zero h hodd hsolv hc hUnc hα hα1
      hdetα hinvα fun x hx => ?_
    by_contra hcon
    exact hvan ⟨x, hx, hcon⟩

theorem exists_equalDegreeCharacterPair_of_not_isCyclic (h : IsTypeII M)
    (hodd : Odd (Nat.card G))
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) (hUnc : ¬ IsCyclic U) :
    HasEqualDegreeCharacterPair hc := by
  obtain ⟨α, hα, β, hβ, hdeg, hdetα, hdetβ, hinvα, hmovβ⟩ :=
    exists_weakEqualDegreeCharacterPair_of_not_isCyclic h hodd hsolv hc hUnc
  exact hasEqualDegreeCharacterPair_of_exists_charConj_ne hc
    (h.clauses_of_isWitnessedPConfiguration hsolv hc).1.prime_natCard_W₁ hα hβ hdeg hdetα hdetβ
    hinvα hmovβ

theorem IsTypeII.frobenius_or_equalDegreeCharacterPair (h : IsTypeII M)
    (hodd : Odd (Nat.card G))
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (∀ u ∈ U, u ≠ 1 → (hallCore M).map M.subtype ⊓ centralizer {u} = ⊥) ∨
      HasEqualDegreeCharacterPair hc := by
  by_cases hUcyc : IsCyclic U
  · exact Or.inl fun u hu hu1 =>
      h.inf_centralizer_hallCore_eq_bot_of_isCyclic hsolv hc hUcyc hu hu1
  · exact Or.inr (exists_equalDegreeCharacterPair_of_not_isCyclic h hodd hsolv hc hUcyc)

theorem IsTypeII.frobenius_or_equalDegreeCharacterPair_of_minimalSimple
    (_hsimple : IsSimpleGroup G) (_hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (∀ u ∈ U, u ≠ 1 → (hallCore M).map M.subtype ⊓ centralizer {u} = ⊥) ∨
      HasEqualDegreeCharacterPair hc :=
  h.frobenius_or_equalDegreeCharacterPair hodd (hsolv M hM.1) hc

end

end CFSG.FeitThompson
