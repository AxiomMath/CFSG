module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
public import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.OddOrder.CoprimeNilpotentSubgroupsCommute

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct Subgroup

variable {H Q : Type*} [Group H] [Group Q] {ρ : Q →* MulAut H} {M : Subgroup H}

theorem apply_inv_apply (ρ : Q →* MulAut H) (q : Q) (v : H) : ρ q (ρ q⁻¹ v) = v := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem isInvariantSubgroup_of_forall_apply_mem (h : ∀ q : Q, ∀ v ∈ M, ρ q v ∈ M) :
    IsInvariantSubgroup ρ M := by
  refine isInvariantSubgroup_iff_forall_map_eq.2 fun q => le_antisymm ?_ fun v hv => ?_
  · rintro x ⟨v, hv, rfl⟩
    exact h q v hv
  · exact ⟨ρ q⁻¹ v, h q⁻¹ v hv, apply_inv_apply ρ q v⟩

theorem IsInvariantSubgroup.apply_mem_iff (hM : IsInvariantSubgroup ρ M) (q : Q) {v : H} :
    ρ q v ∈ M ↔ v ∈ M := by
  refine ⟨fun h => ?_, hM.apply_mem q⟩
  have h2 := hM.apply_mem q⁻¹ h
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2

theorem IsInvariantSubgroup.normalizer (hM : IsInvariantSubgroup ρ M) :
    IsInvariantSubgroup ρ (Subgroup.normalizer (M : Set H)) := by
  refine isInvariantSubgroup_of_forall_apply_mem fun q n hn => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ρ q n * h * (ρ q n)⁻¹ = ρ q (n * ρ q⁻¹ h * n⁻¹) := by
    rw [map_mul, map_mul, apply_inv_apply, map_inv]
  rw [key, hM.apply_mem_iff, ← Subgroup.mem_normalizer_iff.1 hn (ρ q⁻¹ h), hM.apply_mem_iff]

theorem isInvariantSubgroup_fixedPoints_range (ρ : Q →* MulAut H) :
    IsInvariantSubgroup ρ (FixedPoints.subgroup ρ.range H) := by
  refine isInvariantSubgroup_of_forall_apply_mem fun q v hv => ?_
  rw [mem_fixedPoints_range_iff] at hv ⊢
  intro q'
  rw [hv q, hv q']

theorem fixedPoints_range_eq_top_iff (ρ : Q →* MulAut H) :
    FixedPoints.subgroup ρ.range H = ⊤ ↔ ρ = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun q => MulEquiv.ext fun v => ?_
    have hv : v ∈ FixedPoints.subgroup ρ.range H := h ▸ mem_top v
    rw [mem_fixedPoints_range_iff] at hv
    rw [hv q]
    simp
  · intro h
    rw [eq_top_iff]
    intro v _
    rw [mem_fixedPoints_range_iff]
    simp [h]

theorem range_inl_sup_range_inr (ρ : Q →* MulAut H) :
    (inl : H →* H ⋊[ρ] Q).range ⊔ (inr : Q →* H ⋊[ρ] Q).range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← inl_left_mul_inr_right x]
  exact mul_mem (mem_sup_left ⟨x.left, rfl⟩) (mem_sup_right ⟨x.right, rfl⟩)

theorem range_inl_inf_range_inr (ρ : Q →* MulAut H) :
    (inl : H →* H ⋊[ρ] Q).range ⊓ (inr : Q →* H ⋊[ρ] Q).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨h, rfl⟩, ⟨q, hq⟩⟩
  have h1 : q = 1 := by simpa using congrArg SemidirectProduct.right hq
  rw [h1, map_one] at hq
  rw [Subgroup.mem_bot, ← hq]

def IsInvariantSubgroup.semidirectSubgroup (hM : IsInvariantSubgroup ρ M) :
    Subgroup (H ⋊[ρ] Q) where
  carrier := {x | x.left ∈ M}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, SemidirectProduct.mul_left] at *
    exact M.mul_mem ha (hM.apply_mem _ hb)
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, SemidirectProduct.inv_left] at *
    exact hM.apply_mem _ (M.inv_mem ha)

@[simp]
theorem IsInvariantSubgroup.mem_semidirectSubgroup (hM : IsInvariantSubgroup ρ M)
    {x : H ⋊[ρ] Q} : x ∈ hM.semidirectSubgroup ↔ x.left ∈ M := Iff.rfl

theorem IsInvariantSubgroup.semidirectSubgroup_eq_sup (hM : IsInvariantSubgroup ρ M) :
    hM.semidirectSubgroup = M.map (inl : H →* H ⋊[ρ] Q) ⊔ (inr : Q →* H ⋊[ρ] Q).range := by
  refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
  · rw [hM.mem_semidirectSubgroup] at hx
    rw [← inl_left_mul_inr_right x]
    exact mul_mem (mem_sup_left ⟨x.left, hx, rfl⟩) (mem_sup_right ⟨x.right, rfl⟩)
  · rintro z ⟨m, hm, rfl⟩
    simpa using hm
  · rintro z ⟨q, rfl⟩
    simp

def fixedPointsNormalizer (ρ : Q →* MulAut H) : Subgroup H :=
  Subgroup.normalizer ((FixedPoints.subgroup ρ.range H : Subgroup H) : Set H)

theorem fixedPointsNormalizer_eq_normalizer (ρ : Q →* MulAut H) :
    fixedPointsNormalizer ρ
      = Subgroup.normalizer ((FixedPoints.subgroup ρ.range H : Subgroup H) : Set H) := (rfl)

theorem mem_fixedPointsNormalizer {n : H} :
    n ∈ fixedPointsNormalizer ρ ↔
      ∀ u : H, u ∈ FixedPoints.subgroup ρ.range H ↔
        n * u * n⁻¹ ∈ FixedPoints.subgroup ρ.range H := Subgroup.mem_normalizer_iff

theorem isInvariantSubgroup_fixedPointsNormalizer (ρ : Q →* MulAut H) :
    IsInvariantSubgroup ρ (fixedPointsNormalizer ρ) :=
  (isInvariantSubgroup_fixedPoints_range ρ).normalizer

theorem fixedPoints_range_le_fixedPointsNormalizer (ρ : Q →* MulAut H) :
    FixedPoints.subgroup ρ.range H ≤ fixedPointsNormalizer ρ := le_normalizer

instance fixedPoints_normal_subgroupOf :
    ((FixedPoints.subgroup ρ.range H).subgroupOf (fixedPointsNormalizer ρ)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer le_rfl

def fixedPointsNormalizerSemidirect (ρ : Q →* MulAut H) : Subgroup (H ⋊[ρ] Q) :=
  (isInvariantSubgroup_fixedPointsNormalizer ρ).semidirectSubgroup

@[simp]
theorem mem_fixedPointsNormalizerSemidirect {x : H ⋊[ρ] Q} :
    x ∈ fixedPointsNormalizerSemidirect ρ ↔ x.left ∈ fixedPointsNormalizer ρ := Iff.rfl

theorem fixedPointsNormalizerSemidirect_eq_sup (ρ : Q →* MulAut H) :
    fixedPointsNormalizerSemidirect ρ
      = (fixedPointsNormalizer ρ).map (inl : H →* H ⋊[ρ] Q) ⊔ (inr : Q →* H ⋊[ρ] Q).range :=
  (isInvariantSubgroup_fixedPointsNormalizer ρ).semidirectSubgroup_eq_sup

def fixedPointsInSemidirect (ρ : Q →* MulAut H) :
    Subgroup ↥(fixedPointsNormalizerSemidirect ρ) :=
  ((FixedPoints.subgroup ρ.range H).map (inl : H →* H ⋊[ρ] Q)).subgroupOf
    (fixedPointsNormalizerSemidirect ρ)

theorem mem_fixedPointsInSemidirect {x : ↥(fixedPointsNormalizerSemidirect ρ)} :
    x ∈ fixedPointsInSemidirect ρ ↔
      (x : H ⋊[ρ] Q) ∈ (FixedPoints.subgroup ρ.range H).map (inl : H →* H ⋊[ρ] Q) := Iff.rfl

instance fixedPointsInSemidirect_normal : (fixedPointsInSemidirect ρ).Normal := by
  constructor
  intro x hx y
  rw [mem_fixedPointsInSemidirect] at hx ⊢
  obtain ⟨u, hu, hux⟩ := hx
  have hy : (y : H ⋊[ρ] Q).left ∈ fixedPointsNormalizer ρ := y.2
  refine ⟨(y : H ⋊[ρ] Q).left * u * (y : H ⋊[ρ] Q).left⁻¹,
    (Subgroup.mem_normalizer_iff.1 hy u).1 hu, ?_⟩
  push_cast
  rw [← hux, conj_inl]
  congr 1
  rw [(mem_fixedPoints_range_iff ρ).1 hu]

theorem isInvariantSubgroup_fixedPoints_subgroupOf (ρ : Q →* MulAut H) :
    IsInvariantSubgroup (isInvariantSubgroup_fixedPointsNormalizer ρ).restrictAut
      ((FixedPoints.subgroup ρ.range H).subgroupOf (fixedPointsNormalizer ρ)) := by
  refine isInvariantSubgroup_of_forall_apply_mem fun q v hv => ?_
  rw [Subgroup.mem_subgroupOf] at hv ⊢
  rw [(isInvariantSubgroup_fixedPointsNormalizer ρ).coe_restrictAut_apply]
  exact (isInvariantSubgroup_fixedPoints_range ρ).apply_mem q hv

theorem fixedPoints_restrictAut_range (ρ : Q →* MulAut H) :
    FixedPoints.subgroup (isInvariantSubgroup_fixedPointsNormalizer ρ).restrictAut.range
        ↥(fixedPointsNormalizer ρ)
      = (FixedPoints.subgroup ρ.range H).subgroupOf (fixedPointsNormalizer ρ) := by
  ext x
  rw [mem_fixedPoints_range_iff, Subgroup.mem_subgroupOf, mem_fixedPoints_range_iff]
  refine ⟨fun h q => ?_, fun h q => Subtype.ext ?_⟩
  · have h2 := congrArg (Subtype.val) (h q)
    rwa [(isInvariantSubgroup_fixedPointsNormalizer ρ).coe_restrictAut_apply] at h2
  · rw [(isInvariantSubgroup_fixedPointsNormalizer ρ).coe_restrictAut_apply, h q]

section Steps

variable {r a : ℕ}

theorem inv_mul_apply_mem_fixedPoints_of_isNilpotent (ha : Nat.card H = r ^ a)
    (hQ : (Nat.card Q).Coprime r)
    (hnil : Group.IsNilpotent (↥(fixedPointsNormalizerSemidirect ρ) ⧸ fixedPointsInSemidirect ρ))
    {n : H} (hn : n ∈ fixedPointsNormalizer ρ) (q : Q) :
    n⁻¹ * ρ q n ∈ FixedPoints.subgroup ρ.range H := by
  set x : ↥(fixedPointsNormalizerSemidirect ρ) := ⟨inl n, by simpa using hn⟩ with hx
  set y : ↥(fixedPointsNormalizerSemidirect ρ) := ⟨inr q, by simp⟩ with hy
  have hxo : orderOf ((QuotientGroup.mk' (fixedPointsInSemidirect ρ)) x) ∣ r ^ a := by
    refine (orderOf_map_dvd _ _).trans ?_
    rw [hx, Subgroup.orderOf_mk, orderOf_injective (inl : H →* H ⋊[ρ] Q) inl_injective n, ← ha]
    exact orderOf_dvd_natCard n
  have hyo : orderOf ((QuotientGroup.mk' (fixedPointsInSemidirect ρ)) y) ∣ Nat.card Q := by
    refine (orderOf_map_dvd _ _).trans ?_
    rw [hy, Subgroup.orderOf_mk, orderOf_injective (inr : Q →* H ⋊[ρ] Q) inr_injective q]
    exact orderOf_dvd_natCard q
  have hcomm := commute_of_coprime_orderOf _
    ((QuotientGroup.mk' (fixedPointsInSemidirect ρ)) x)
    ((QuotientGroup.mk' (fixedPointsInSemidirect ρ)) y)
    (((hQ.pow_right a).symm.coprime_dvd_left hxo).coprime_dvd_right hyo)
  have hone : (QuotientGroup.mk' (fixedPointsInSemidirect ρ)) (x⁻¹ * y * x * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ _ (QuotientGroup.mk' _ x),
      ← hcomm.eq]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_fixedPointsInSemidirect] at hone
  have hcoe : ((x⁻¹ * y * x * y⁻¹ : ↥(fixedPointsNormalizerSemidirect ρ)) : H ⋊[ρ] Q)
      = inl (n⁻¹ * ρ q n) := by
    push_cast
    rw [hx, hy]
    refine SemidirectProduct.ext ?_ ?_ <;>
      simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
        SemidirectProduct.inv_right, mul_assoc]
  rwa [hcoe, Subgroup.mem_map_iff_mem inl_injective] at hone

theorem fixedPointsNormalizer_le_fixedPoints_of_forall [Finite H] [Finite Q]
    [Group.IsSolvable Q] [Group.IsSolvable H] (hcop : (Nat.card Q).Coprime (Nat.card H))
    (h : ∀ n ∈ fixedPointsNormalizer ρ, ∀ q : Q,
      n⁻¹ * ρ q n ∈ FixedPoints.subgroup ρ.range H) :
    fixedPointsNormalizer ρ ≤ FixedPoints.subgroup ρ.range H := by
  set N := fixedPointsNormalizer ρ with hN
  set U' := (FixedPoints.subgroup ρ.range H).subgroupOf N with hU'
  have hinv := isInvariantSubgroup_fixedPoints_subgroupOf ρ
  have key := fixedPoints_quotientAut_range_of_isSolvable_subgroup hinv
    (hcop.coprime_dvd_right N.card_subgroup_dvd_card)
  have hLHS : FixedPoints.subgroup hinv.quotientAut.range (↥N ⧸ U') = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_fixedPoints_range_iff]
    intro q
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [hinv.quotientAut_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      push_cast
      rw [(isInvariantSubgroup_fixedPointsNormalizer ρ).coe_restrictAut_apply]
      simpa using (FixedPoints.subgroup ρ.range H).inv_mem (h (v : H) v.2 q)
  have hRHS : (FixedPoints.subgroup
      (isInvariantSubgroup_fixedPointsNormalizer ρ).restrictAut.range ↥N).map
        (QuotientGroup.mk' U') = ⊥ := by
    rw [fixedPoints_restrictAut_range, ← hU', QuotientGroup.map_mk'_self]
  rw [hLHS, hRHS] at key
  have htop : U' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← QuotientGroup.eq_one_iff]
    have hx : (x : ↥N ⧸ U') ∈ (⊥ : Subgroup (↥N ⧸ U')) := key ▸ mem_top _
    exact hx
  rwa [hU', Subgroup.subgroupOf_eq_top] at htop

end Steps

theorem not_isNilpotent_quotient_fixedPointsInSemidirect {r : ℕ} [Finite H] [Finite Q]
    [Group.IsSolvable Q] (hr : r.Prime) (hH : IsPGroup r H) (hQ : (Nat.card Q).Coprime r)
    (hρ : ρ ≠ 1) :
    ¬ Group.IsNilpotent (↥(fixedPointsNormalizerSemidirect ρ) ⧸ fixedPointsInSemidirect ρ) := by
  have hfact := Fact.mk hr
  intro hnil
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := r)).1 hH
  have hHnil : Group.IsNilpotent H := hH.isNilpotent
  have hUtop : FixedPoints.subgroup ρ.range H < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hρ ((fixedPoints_range_eq_top_iff ρ).1 h)
  have hUN : FixedPoints.subgroup ρ.range H < fixedPointsNormalizer ρ :=
    Group.normalizerCondition_of_isNilpotent _ hUtop
  exact absurd (fixedPointsNormalizer_le_fixedPoints_of_forall (ha ▸ hQ.pow_right a)
    fun n hn q => inv_mul_apply_mem_fixedPoints_of_isNilpotent ha hQ hnil hn q) hUN.not_ge

end CFSG.FeitThompson
