module

public import Mathlib.GroupTheory.Abelianization.Finite
public import CFSG.FeitThompson.Local.FixedDisplacementSplittingCoprime
public import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Displacement

variable {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]

def smulDisplacementSubgroup (A V : Type*) [Group A] [Group V] [MulDistribMulAction A V] :
    Subgroup V :=
  Subgroup.closure {x | ∃ (a : A) (v : V), v⁻¹ * a • v = x}

theorem smulDisplacementSubgroup_eq_closure :
    smulDisplacementSubgroup A V = Subgroup.closure {x | ∃ (a : A) (v : V), v⁻¹ * a • v = x} :=
  (rfl)

theorem inv_mul_smul_mem_smulDisplacementSubgroup (a : A) (v : V) :
    v⁻¹ * a • v ∈ smulDisplacementSubgroup A V :=
  Subgroup.subset_closure ⟨a, v, rfl⟩

theorem smulDisplacementSubgroup_le {H : Subgroup V}
    (h : ∀ (a : A) (v : V), v⁻¹ * a • v ∈ H) : smulDisplacementSubgroup A V ≤ H := by
  rw [smulDisplacementSubgroup_eq_closure, Subgroup.closure_le]
  rintro x ⟨a, v, rfl⟩
  exact h a v

private theorem mul_smul_inv_mem_smulDisplacementSubgroup (a : A) (t : V) :
    t * a • t⁻¹ ∈ smulDisplacementSubgroup A V := by
  simpa using inv_mul_smul_mem_smulDisplacementSubgroup a t⁻¹

private theorem conj_inv_mul_smul (a : A) (v t : V) :
    t * (v⁻¹ * a • v) * t⁻¹ = ((v * t⁻¹)⁻¹ * a • (v * t⁻¹)) * (t * a • t⁻¹)⁻¹ := by
  simp [smul_mul', smul_inv', mul_assoc]

instance smulDisplacementSubgroup_normal : (smulDisplacementSubgroup A V).Normal := by
  constructor
  intro n hn w
  have h : smulDisplacementSubgroup A V
      ≤ (smulDisplacementSubgroup A V).comap (MulAut.conj w).toMonoidHom := by
    refine smulDisplacementSubgroup_le fun a v => ?_
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_inv_mul_smul]
    exact mul_mem (inv_mul_smul_mem_smulDisplacementSubgroup a (v * w⁻¹))
      (inv_mem (mul_smul_inv_mem_smulDisplacementSubgroup a w))
  exact h hn

theorem smul_mem_smulDisplacementSubgroup (a : A) {v : V}
    (hv : v ∈ smulDisplacementSubgroup A V) : a • v ∈ smulDisplacementSubgroup A V := by
  have h : smulDisplacementSubgroup A V
      ≤ (smulDisplacementSubgroup A V).comap (MulDistribMulAction.toMonoidHom V a) := by
    refine smulDisplacementSubgroup_le fun b v => ?_
    have hb : a • (b • v) = (a * b * a⁻¹) • (a • v) := by
      rw [← mul_smul, ← mul_smul, inv_mul_cancel_right]
    simp only [Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply, smul_mul', smul_inv', hb]
    exact inv_mul_smul_mem_smulDisplacementSubgroup _ _
  exact h hv

theorem smulDisplacementSubgroup_eq_bot_iff :
    smulDisplacementSubgroup A V = ⊥ ↔ ∀ (a : A) (v : V), a • v = v := by
  constructor
  · intro h a v
    have hmem := h ▸ inv_mul_smul_mem_smulDisplacementSubgroup a v
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  · intro h
    rw [eq_bot_iff]
    exact smulDisplacementSubgroup_le fun a v => by simp [h a v]

end Displacement

section Abelianization

variable {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]

private def abelianizationAut : A →* MulAut (Abelianization V) where
  toFun a := MulEquiv.abelianizationCongr (MulDistribMulAction.toMulEquiv V a)
  map_one' := by
    have h : MulDistribMulAction.toMulEquiv V (1 : A) = MulEquiv.refl V := by ext v; simp
    rw [h, abelianizationCongr_refl]; rfl
  map_mul' a b := by
    have h : MulDistribMulAction.toMulEquiv V (a * b)
        = (MulDistribMulAction.toMulEquiv V b).trans (MulDistribMulAction.toMulEquiv V a) := by
      ext v; simp [mul_smul]
    rw [h, ← abelianizationCongr_trans]; rfl

private instance mulDistribMulActionAbelianization :
    MulDistribMulAction A (Abelianization V) :=
  MulDistribMulAction.compHom _ (abelianizationAut (A := A) (V := V))

private instance distribMulActionAdditive {M N : Type*} [Monoid M] [CommGroup N]
    [MulDistribMulAction M N] : DistribMulAction M (Additive N) where
  smul m x := Additive.ofMul (m • x.toMul)
  one_smul x := by
    change Additive.ofMul ((1 : M) • x.toMul) = x
    rw [one_smul, ofMul_toMul]
  mul_smul m n x := by
    change Additive.ofMul ((m * n) • x.toMul)
      = Additive.ofMul (m • (Additive.ofMul (n • x.toMul)).toMul)
    rw [mul_smul, toMul_ofMul]
  smul_zero m := by
    change Additive.ofMul (m • (1 : N)) = 0
    rw [smul_one]; rfl
  smul_add m x y := by
    change Additive.ofMul (m • (x.toMul * y.toMul)) = _
    rw [smul_mul']; rfl

private theorem smul_abelianization_of (a : A) (v : V) :
    a • Abelianization.of v = Abelianization.of (a • v) := rfl

private def abelAddHom (V : Type*) [Group V] : Additive V →+ Additive (Abelianization V) :=
  MonoidHom.toAdditive (Abelianization.of : V →* Abelianization V)

private theorem abelAddHom_apply (v : V) :
    abelAddHom V (Additive.ofMul v) = Additive.ofMul (Abelianization.of v) := rfl

private theorem abelAddHom_surjective : Function.Surjective (abelAddHom V) := by
  intro w
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (s := commutator V) w.toMul
  exact ⟨Additive.ofMul v, by
    rw [abelAddHom_apply, show Abelianization.of v = w.toMul from hv, ofMul_toMul]⟩

private theorem displacementAddSubgroup_eq_top (h : smulDisplacementSubgroup A V = ⊤) :
    displacementAddSubgroup A (Additive (Abelianization V)) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  obtain ⟨x, rfl⟩ := abelAddHom_surjective (V := V) w
  have key : smulDisplacementSubgroup A V ≤ AddSubgroup.toSubgroup'
      ((displacementAddSubgroup A (Additive (Abelianization V))).comap (abelAddHom V)) := by
    refine smulDisplacementSubgroup_le fun a v => ?_
    change abelAddHom V (Additive.ofMul (v⁻¹ * a • v))
      ∈ displacementAddSubgroup A (Additive (Abelianization V))
    rw [abelAddHom_apply, map_mul, map_inv, ← smul_abelianization_of, mul_comm, ← div_eq_mul_inv]
    exact sub_mem_displacementAddSubgroup a (Additive.ofMul (Abelianization.of v))
  have h2 : Additive.ofMul x.toMul
      ∈ (displacementAddSubgroup A (Additive (Abelianization V))).comap (abelAddHom V) :=
    key (h ▸ Subgroup.mem_top x.toMul)
  rw [ofMul_toMul] at h2
  exact h2

private theorem card_additive_abelianization_dvd [Finite V] :
    Nat.card (Additive (Abelianization V)) ∣ Nat.card V := by
  rw [Nat.card_congr (Additive.ofMul (α := Abelianization V)).symm]
  exact Subgroup.card_quotient_dvd_card _

theorem fixedPoints_subgroup_le_commutator [Finite A] [Finite V]
    (hcop : (Nat.card A).Coprime (Nat.card V))
    (hgen : smulDisplacementSubgroup A V = ⊤) :
    FixedPoints.subgroup A V ≤ commutator V := by
  have hfin : Finite (Additive (Abelianization V)) :=
    Finite.of_equiv _ (Additive.ofMul (α := Abelianization V))
  have hcop' : (Nat.card A).Coprime (Nat.card (Additive (Abelianization V))) :=
    Nat.Coprime.coprime_dvd_right card_additive_abelianization_dvd hcop
  intro v hv
  have hfix : ∀ a : A, a • abelAddHom V (Additive.ofMul v) = abelAddHom V (Additive.ofMul v) := by
    intro a
    have hav : a • v = v := (FixedPoints.mem_subgroup A V v).1 hv a
    change Additive.ofMul (Abelianization.of (a • v)) = Additive.ofMul (Abelianization.of v)
    rw [hav]
  have hzero : abelAddHom V (Additive.ofMul v) = 0 :=
    eq_zero_of_mem_displacementAddSubgroup_of_forall_smul_eq hcop'
      (displacementAddSubgroup_eq_top hgen ▸ AddSubgroup.mem_top _) hfix
  rw [← Abelianization.ker_of]
  exact Additive.ofMul.injective hzero

end Abelianization

section MonoidHomVersion

variable {A V : Type*} [Group A] [Group V] [Finite A] [Finite V]

theorem mem_closure_setOf_inv_mul_inv_mul_mul_of_forall_apply_eq (ρ : A →* MulAut V)
    (hcop : (Nat.card A).Coprime (Nat.card V))
    (hgen : Subgroup.closure {x : V | ∃ (a : A) (v : V), v⁻¹ * ρ a v = x} = ⊤)
    {v : V} (hv : ∀ a : A, ρ a v = v) :
    v ∈ Subgroup.closure {g : V | ∃ u w : V, u⁻¹ * w⁻¹ * u * w = g} := by
  let inst : MulDistribMulAction A V := MulDistribMulAction.compHom V ρ
  rw [closure_setOf_inv_mul_inv_mul_mul_eq_commutator]
  refine fixedPoints_subgroup_le_commutator hcop ?_ ((FixedPoints.mem_subgroup A V v).2 hv)
  rw [smulDisplacementSubgroup_eq_closure]
  exact hgen

end MonoidHomVersion

end CFSG.FeitThompson
