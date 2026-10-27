module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.FixedPointFreeActsFreelyOnLinearChars
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FrobeniusInduction

open SemidirectProduct
open NormalInduction (conjClassFun conjClassFun_apply coe_conjNormal_inv)

instance instFintypeSemidirectProduct {N H : Type*} [Group N] [Group H] {ψ : H →* MulAut N}
    [Fintype N] [Fintype H] : Fintype (N ⋊[ψ] H) :=
  Fintype.ofEquiv (N × H) equivProd.symm

instance instNormalRangeInl {N H : Type*} [Group N] [Group H] {ψ : H →* MulAut N} :
    ((inl : N →* N ⋊[ψ] H).range).Normal := range_inl_normal

variable {P U : Type*} [CommGroup P] [Group U] {φ : U →* MulAut P}

theorem mem_range_inl_iff {x : P ⋊[φ] U} :
    x ∈ (inl : P →* P ⋊[φ] U).range ↔ x.right = 1 := by
  rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  rfl

theorem index_range_inl : (inl : P →* P ⋊[φ] U).range.index = Nat.card U := by
  rw [range_inl_eq_ker_rightHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 rightHom_surjective, Subgroup.card_top]

theorem inv_mul_inl_mul (t : P ⋊[φ] U) (q : P) :
    t⁻¹ * inl q * t = inl ((φ t.right)⁻¹ q) := by
  have hq : ((inl t.left)⁻¹ * inl q * inl t.left : P ⋊[φ] U) = inl q := by
    rw [← map_inv, ← map_mul, ← map_mul, mul_comm t.left⁻¹ q, mul_assoc, inv_mul_cancel, mul_one]
  conv_lhs => rw [← inl_left_mul_inr_right t]
  rw [inl_aut_inv, mul_inv_rev]
  calc (inr t.right)⁻¹ * (inl t.left)⁻¹ * inl q * (inl t.left * inr t.right)
      = (inr t.right)⁻¹ * ((inl t.left)⁻¹ * inl q * inl t.left) * inr t.right := by group
    _ = (inr t.right)⁻¹ * inl q * inr t.right := by rw [hq]
    _ = inr t.right⁻¹ * inl q * inr t.right := by rw [map_inv]

def rangeInlEquiv {N H : Type*} [Group N] [Group H] (ψ : H →* MulAut N) :
    (inl : N →* N ⋊[ψ] H).range ≃* N where
  toFun x := (x : N ⋊[ψ] H).left
  invFun n := ⟨inl n, ⟨n, rfl⟩⟩
  left_inv x := by obtain ⟨-, n, rfl⟩ := x; simp
  right_inv n := by simp
  map_mul' x y := by
    obtain ⟨-, m, rfl⟩ := x
    obtain ⟨-, n, rfl⟩ := y
    simp [← map_mul]

@[simp] theorem rangeInlEquiv_apply (n : (inl : P →* P ⋊[φ] U).range) :
    rangeInlEquiv φ n = (n : P ⋊[φ] U).left := (rfl)

@[simp] theorem coe_rangeInlEquiv_symm (p : P) :
    ((rangeInlEquiv φ).symm p : P ⋊[φ] U) = inl p := (rfl)

theorem inl_left_coe (n : (inl : P →* P ⋊[φ] U).range) :
    inl ((n : P ⋊[φ] U).left) = (n : P ⋊[φ] U) := by
  obtain ⟨-, m, rfl⟩ := n
  simp

def kernelChar (φ : U →* MulAut P) (lam : P → ℂ) : (inl : P →* P ⋊[φ] U).range → ℂ :=
  lam ∘ rangeInlEquiv φ

@[simp] theorem kernelChar_apply (lam : P → ℂ) (n : (inl : P →* P ⋊[φ] U).range) :
    kernelChar φ lam n = lam ((n : P ⋊[φ] U).left) := (rfl)

theorem kernelChar_injective : Function.Injective (kernelChar φ) := by
  intro lam mu h
  funext p
  simpa using congrFun h ((rangeInlEquiv φ).symm p)

theorem mem_Irr_comp_mulEquiv {G W : Type*} [Group G] [Group W] {χ : G → ℂ} (hχ : χ ∈ Irr G)
    (e : W ≃* G) : χ ∘ e ∈ Irr W := by
  rw [← normalInduction_irrChars_eq_Irr] at hχ ⊢
  exact NormalInduction.mem_irrChars_comp_mulEquiv hχ e

theorem kernelChar_mem_Irr {lam : P → ℂ} (hlam : lam ∈ Irr P) :
    kernelChar φ lam ∈ Irr ((inl : P →* P ⋊[φ] U).range) :=
  mem_Irr_comp_mulEquiv hlam (rangeInlEquiv φ)

@[simp] theorem kernelChar_one_apply (lam : P → ℂ) :
    kernelChar φ lam (1 : (inl : P →* P ⋊[φ] U).range) = lam 1 := by
  simp

theorem conjClassFun_kernelChar (t : P ⋊[φ] U) (lam : P → ℂ) :
    conjClassFun (inl : P →* P ⋊[φ] U).range t (kernelChar φ lam)
      = kernelChar φ (fun p => lam ((φ t.right)⁻¹ p)) := by
  funext n
  rw [conjClassFun_apply, kernelChar_apply, kernelChar_apply]
  congr 1
  have h : ((MulAut.conjNormal t⁻¹ n : (inl : P →* P ⋊[φ] U).range) : P ⋊[φ] U)
      = inl ((φ t.right)⁻¹ ((n : P ⋊[φ] U).left)) := by
    rw [coe_conjNormal_inv]
    conv_lhs => rw [← inl_left_coe n]
    rw [inv_mul_inl_mul]
  rw [h, left_inl]

theorem comp_mem_nonprincipalIrr {lam : P → ℂ} (hlam : lam ∈ nonprincipalIrr P) (u : U) :
    (fun p => lam (φ u p)) ∈ nonprincipalIrr P := by
  obtain ⟨hl, hl1⟩ := mem_nonprincipalIrr.1 hlam
  refine mem_nonprincipalIrr.2 ⟨mem_Irr_comp_mulAut hl (φ u), fun h => hl1 ?_⟩
  funext p
  simpa using congrFun h ((φ u)⁻¹ p)

theorem eq_one_of_forall_apply_eq [Finite P]
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) {lam : P → ℂ}
    (hlam : lam ∈ Irr P) (hlam1 : lam ≠ 1) {u : U} (h : ∀ p : P, lam (φ u p) = lam p) : u = 1 := by
  by_contra hu
  exact hlam1 (eq_one_of_forall_apply_aut_eq (hφ u hu) hlam h)

variable [Fintype P] [Fintype U]

theorem inertiaGroup_le_range_inl
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) {lam : P → ℂ}
    (hlam : lam ∈ Irr P) (hlam1 : lam ≠ 1) :
    inertiaGroup (inl : P →* P ⋊[φ] U).range (kernelChar φ lam)
      ≤ (inl : P →* P ⋊[φ] U).range := by
  intro t ht
  rw [mem_inertiaGroup, conjClassFun_kernelChar] at ht
  have hlam' : ∀ p : P, lam (φ t.right⁻¹ p) = lam p := by
    intro p
    rw [map_inv]
    exact congrFun (kernelChar_injective ht) p
  have h1 : t.right⁻¹ = 1 := eq_one_of_forall_apply_eq hφ hlam hlam1 hlam'
  rw [mem_range_inl_iff, ← inv_inv t.right, h1, inv_one]

theorem inertiaGroup_eq_range_inl
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) {lam : P → ℂ}
    (hlam : lam ∈ Irr P) (hlam1 : lam ≠ 1) :
    inertiaGroup (inl : P →* P ⋊[φ] U).range (kernelChar φ lam)
      = (inl : P →* P ⋊[φ] U).range :=
  le_antisymm (inertiaGroup_le_range_inl hφ hlam hlam1)
    (le_inertiaGroup _ (Irr_subset_classFun (kernelChar_mem_Irr hlam)))

theorem cfInner_self_indClassFun_kernelChar
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) {lam : P → ℂ}
    (hlam : lam ∈ Irr P) (hlam1 : lam ≠ 1) :
    cfInner (indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam))
      (indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam)) = 1 := by
  rw [cfInner_self_indClassFun _ (kernelChar_mem_Irr hlam),
    Subgroup.relIndex_eq_one.2 (inertiaGroup_le_range_inl hφ hlam hlam1), Nat.cast_one]

theorem indClassFun_kernelChar_mem_Irr
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) {lam : P → ℂ}
    (hlam : lam ∈ Irr P) (hlam1 : lam ≠ 1) :
    indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam) ∈ Irr (P ⋊[φ] U) := by
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam
    (inl : P →* P ⋊[φ] U).range
    (indClassFun_mem_indFam _ (kernelChar_mem_Irr (φ := φ) hlam))
  have h1 : Representation.character W.ρ
      = indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam) := hW
  refine mem_Irr.2 ⟨W, ?_, hW⟩
  rw [isIrreducible_iff_cfInner_self_eq_one W.ρ, h1]
  exact cfInner_self_indClassFun_kernelChar hφ hlam hlam1

theorem indClassFun_kernelChar_one {lam : P → ℂ} (hlam : lam ∈ Irr P) :
    indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam) 1 = (Nat.card U : ℂ) := by
  rw [NormalInducedFamily.indClassFun_one_eq_index_mul, index_range_inl, kernelChar_one_apply,
    Irr.apply_one_eq_one hlam, mul_one]

theorem indClassFun_kernelChar_eq_iff {lam mu : P → ℂ} (hlam : lam ∈ Irr P) (hmu : mu ∈ Irr P) :
    indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam)
        = indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ mu)
      ↔ ∃ u : U, (fun p => mu (φ u p)) = lam := by
  rw [NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun _
    (kernelChar_mem_Irr hlam) (kernelChar_mem_Irr hmu)]
  constructor
  · rintro ⟨t, ht⟩
    rw [conjClassFun_kernelChar] at ht
    refine ⟨t.right⁻¹, ?_⟩
    have h := kernelChar_injective ht
    funext p
    rw [map_inv]
    exact congrFun h p
  · rintro ⟨u, hu⟩
    refine ⟨inr u⁻¹, ?_⟩
    rw [conjClassFun_kernelChar, right_inr]
    refine congrArg (kernelChar φ) ?_
    funext p
    rw [← hu]
    simp

def frobeniusInducedIrr (φ : U →* MulAut P) [Fintype P] [Fintype U] : Set (P ⋊[φ] U → ℂ) :=
  (fun lam => indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam)) '' nonprincipalIrr P

theorem mem_frobeniusInducedIrr {f : P ⋊[φ] U → ℂ} :
    f ∈ frobeniusInducedIrr φ ↔ ∃ lam ∈ nonprincipalIrr P,
      indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam) = f := Iff.rfl

theorem indClassFun_kernelChar_mem_frobeniusInducedIrr {lam : P → ℂ}
    (hlam : lam ∈ nonprincipalIrr P) :
    indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam) ∈ frobeniusInducedIrr φ :=
  ⟨lam, hlam, rfl⟩

theorem finite_frobeniusInducedIrr : (frobeniusInducedIrr φ).Finite :=
  finite_nonprincipalIrr.image _

instance instFiniteFrobeniusInducedIrr : Finite (frobeniusInducedIrr φ) :=
  finite_frobeniusInducedIrr.to_subtype

theorem frobeniusInducedIrr_subset_Irr
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) :
    frobeniusInducedIrr φ ⊆ Irr (P ⋊[φ] U) := by
  rintro f ⟨lam, hlam, rfl⟩
  obtain ⟨hl, hl1⟩ := mem_nonprincipalIrr.1 hlam
  exact indClassFun_kernelChar_mem_Irr hφ hl hl1

theorem natCard_orbit
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) {lam : P → ℂ}
    (hlam : lam ∈ nonprincipalIrr P) :
    Nat.card {mu : nonprincipalIrr P //
        indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ (mu : P → ℂ))
          = indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam)} = Nat.card U := by
  obtain ⟨hl, hl1⟩ := mem_nonprincipalIrr.1 hlam
  have hind : ∀ u : U,
      indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ (fun p => lam (φ u p)))
        = indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam) :=
    fun u => (indClassFun_kernelChar_eq_iff
      (mem_nonprincipalIrr.1 (comp_mem_nonprincipalIrr hlam u)).1 hl).2 ⟨u, rfl⟩
  refine (Nat.card_congr (Equiv.ofBijective
    (fun u : U => (⟨⟨_, comp_mem_nonprincipalIrr hlam u⟩, hind u⟩ :
      {mu : nonprincipalIrr P //
        indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ (mu : P → ℂ))
          = indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam)}))
    ⟨?_, ?_⟩)).symm
  ·
    intro u v huv
    have h : ∀ p : P, lam (φ u p) = lam (φ v p) :=
      fun p => congrFun (congrArg Subtype.val (congrArg Subtype.val huv)) p
    have hfix : ∀ p : P, lam (φ (u * v⁻¹) p) = lam p := by
      intro p
      simpa [map_mul, map_inv] using h ((φ v)⁻¹ p)
    have := eq_one_of_forall_apply_eq hφ hl hl1 hfix
    rwa [mul_inv_eq_one] at this
  ·
    rintro ⟨⟨mu, hmu⟩, hfib⟩
    obtain ⟨u, hu⟩ := (indClassFun_kernelChar_eq_iff (mem_nonprincipalIrr.1 hmu).1 hl).1 hfib
    exact ⟨u, Subtype.ext (Subtype.ext hu)⟩

theorem natCard_nonprincipalIrr : Nat.card (nonprincipalIrr P) = Nat.card P - 1 := by
  have h : nonprincipalIrr P = Irr P \ {1} := by
    ext χ
    exact mem_nonprincipalIrr
  rw [Nat.card_coe_set_eq, h, Set.ncard_sdiff_singleton_of_mem one_mem_Irr,
    ← Nat.card_coe_set_eq, card_Irr_eq_card]

theorem natCard_frobeniusInducedIrr_mul_natCard
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) :
    Nat.card (frobeniusInducedIrr φ) * Nat.card U = Nat.card P - 1 := by
  classical
  have _ : Fintype (frobeniusInducedIrr φ) := Fintype.ofFinite _
  set F : nonprincipalIrr P → frobeniusInducedIrr φ := fun lam =>
    ⟨_, indClassFun_kernelChar_mem_frobeniusInducedIrr lam.2⟩ with hF
  have hfib : ∀ s : frobeniusInducedIrr φ, Nat.card {a // F a = s} = Nat.card U := by
    rintro ⟨-, lam, hlam, rfl⟩
    refine Eq.trans (Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_))
      (natCard_orbit hφ hlam)
    rw [hF]
    exact Subtype.ext_iff
  have hsigma := Nat.card_congr (Equiv.sigmaFiberEquiv F)
  rw [Nat.card_sigma, Finset.sum_congr rfl fun s _ => hfib s] at hsigma
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at hsigma
  rw [hsigma, natCard_nonprincipalIrr]

theorem natCard_frobeniusInducedIrr
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) :
    Nat.card (frobeniusInducedIrr φ) = (Nat.card P - 1) / Nat.card U :=
  (Nat.div_eq_of_eq_mul_left Nat.card_pos
    (natCard_frobeniusInducedIrr_mul_natCard hφ).symm).symm

end FrobeniusInduction

end CFSG.FeitThompson
