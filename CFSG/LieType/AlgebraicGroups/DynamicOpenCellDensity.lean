module

public import CFSG.ThirdParty.TauCeti.DynamicSmooth
public import CFSG.ThirdParty.TauCeti.FullLieAlgebra
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.RingTheory.FiniteType.PointSeparation

public noncomputable section

open WithConv

namespace CFSG.LieType.AlgebraicGroups.DynamicOpenCell

universe u

variable {k : Type u} [Field k]

theorem vanishingIdeal_le_parabolicDefiningHopfIdeal [IsAlgClosed k]
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [Algebra.Smooth k M]
    (l : M →ₐc[k] LaurentPolynomial k) (S : Subgroup (WithConv (M →ₐ[k] k)))
    (hS : TauCeti.Cocharacter.parabolic k l ≤ S) :
    TauCeti.HopfIdeal.vanishingIdeal S ≤
      CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal l := by
  let P := CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal l
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient M P
  have hsm : Algebra.Smooth k Q :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp
      (CFSG.ThirdParty.TauCeti.BialgHom.smoothCommHopfAlgProperty_quotient_parabolicDefiningHopfIdeal
        l)
  have : IsReduced Q := TauCeti.isReduced_of_smooth k Q
  intro x hx
  rw [TauCeti.HopfIdeal.mem_vanishingIdeal] at hx
  rw [← TauCeti.HopfIdeal.mem_toIdeal, ← Ideal.Quotient.eq_zero_iff_mem]
  change (Ideal.Quotient.mkₐ k P.toIdeal) x = 0
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro q
  have hg : toConv (q.comp (Ideal.Quotient.mkₐ k P.toIdeal)) ∈ S := by
    apply hS
    rw [← CFSG.ThirdParty.TauCeti.Cocharacter.quotientPointsSubgroup_parabolicDefiningHopfIdeal l,
      TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro y hy
    change q (Ideal.Quotient.mkₐ k P.toIdeal y) = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
      (TauCeti.HopfIdeal.mem_toIdeal.mpr hy), map_zero]
  have h := hx ⟨_, hg⟩
  rw [map_zero]
  exact h

theorem coeff_conjugationAlgHom_oppositeCocharacter
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (l : M →ₐc[k] LaurentPolynomial k)
    (h : M) (n : ℤ) :
    (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom
        (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) h).coeff n =
      (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff (-n) := by
  have h₁ := CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugate
    (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) (toConv (AlgHom.id k M)) h n
  have h₂ := CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugate l (toConv (AlgHom.id k M)) h (-n)
  rw [ofConv_toConv, AlgHom.id_apply] at h₁ h₂
  rw [← h₁, ← h₂, CFSG.ThirdParty.TauCeti.Cocharacter.conjugate_oppositeCocharacter,
    TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  exact LaurentPolynomial.invert_apply _ n

theorem counit_coeff_conjugationAlgHom
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (l : M →ₐc[k] LaurentPolynomial k)
    (h : M) (n : ℤ) :
    Coalgebra.counit (R := k)
        ((CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff n) =
      if n = 0 then Coalgebra.counit (R := k) h else 0 := by
  have h₁ := CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugate l
    (1 : WithConv (M →ₐ[k] k)) h n
  rw [map_one] at h₁
  simpa [eq_comm] using h₁.symm

theorem linearMap_algebraMap_eq_zero
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (D : M →ₗ[k] k)
    (hD : ∀ x y : M, D (x * y) =
      Coalgebra.counit (R := k) x * D y + Coalgebra.counit (R := k) y * D x)
    (r : k) : D (algebraMap k M r) = 0 := by
  have h1 : D 1 = 0 := by
    have h := hD 1 1
    rw [one_mul, Bialgebra.counit_one, one_mul] at h
    linear_combination -h
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

theorem linearMap_coeff_mul
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (D : M →ₗ[k] k)
    (hD : ∀ x y : M, D (x * y) =
      Coalgebra.counit (R := k) x * D y + Coalgebra.counit (R := k) y * D x)
    (p q : LaurentPolynomial M) (ρ σ : k)
    (hp : ∀ m, Coalgebra.counit (R := k) (p.coeff m) = if m = 0 then ρ else 0)
    (hq : ∀ m, Coalgebra.counit (R := k) (q.coeff m) = if m = 0 then σ else 0) (n : ℤ) :
    D ((p * q).coeff n) = ρ * D (q.coeff n) + σ * D (p.coeff n) := by
  classical
  set α : M := algebraMap k M ρ
  set β : M := algebraMap k M σ
  set p' := p - AddMonoidAlgebra.single 0 α with hp'
  set q' := q - AddMonoidAlgebra.single 0 β with hq'
  have hcp : ∀ m, Coalgebra.counit (R := k) (p'.coeff m) = 0 := by
    intro m
    rw [hp', AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, map_sub, hp,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hm : m = 0
    · subst hm; simp [α]
    · simp [hm, Ne.symm hm]
  have hcq : ∀ m, Coalgebra.counit (R := k) (q'.coeff m) = 0 := by
    intro m
    rw [hq', AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, map_sub, hq,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hm : m = 0
    · subst hm; simp [β]
    · simp [hm, Ne.symm hm]
  have hDp' : D (p'.coeff n) = D (p.coeff n) := by
    rw [hp', AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, map_sub,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · rw [linearMap_algebraMap_eq_zero M D hD, sub_zero]
    · rw [map_zero, sub_zero]
  have hDq' : D (q'.coeff n) = D (q.coeff n) := by
    rw [hq', AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, map_sub,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · rw [linearMap_algebraMap_eq_zero M D hD, sub_zero]
    · rw [map_zero, sub_zero]
  have hpq : p * q = AddMonoidAlgebra.single 0 (α * β) + AddMonoidAlgebra.single 0 α * q' +
      AddMonoidAlgebra.single 0 β * p' + p' * q' := by
    have hs : AddMonoidAlgebra.single (0 : ℤ) (α * β) =
        AddMonoidAlgebra.single 0 α * AddMonoidAlgebra.single 0 β := by
      rw [AddMonoidAlgebra.single_mul_single, add_zero]
    rw [hs, hp', hq']
    ring
  have hzero : D ((p' * q').coeff n) = 0 := by
    rw [AddMonoidAlgebra.coeff_mul, map_finsuppSum]
    refine Finset.sum_eq_zero fun m₁ _ ↦ ?_
    beta_reduce
    rw [map_finsuppSum]
    refine Finset.sum_eq_zero fun m₂ _ ↦ ?_
    beta_reduce
    split_ifs
    · rw [hD, hcp, hcq, zero_mul, zero_mul, add_zero]
    · exact map_zero D
  rw [hpq, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, map_add, map_add, map_add, hzero,
    add_zero, AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_single_zero_mul,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hD, hD, hDp', hDq']
  have hα : Coalgebra.counit (R := k) α = ρ := by simp [α]
  have hβ : Coalgebra.counit (R := k) β = σ := by simp [β]
  have hDα : D α = 0 := linearMap_algebraMap_eq_zero M D hD ρ
  have hDβ : D β = 0 := linearMap_algebraMap_eq_zero M D hD σ
  have hDαβ : D (if (0 : ℤ) = n then α * β else 0) = 0 := by
    split_ifs
    · rw [hD, hDα, hDβ, mul_zero, mul_zero, add_zero]
    · exact map_zero D
  rw [hDαβ, hα, hβ, hDα, hDβ, mul_zero, mul_zero, add_zero, add_zero, zero_add]

def tangentFunctional (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (d : Derivation k M (TauCeti.Bialgebra.CounitAlgebra k M k)) : M →ₗ[k] k :=
  (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k M k).toLinearMap ∘ₗ d.toLinearMap

theorem tangentFunctional_mul (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (d : Derivation k M (TauCeti.Bialgebra.CounitAlgebra k M k)) (x y : M) :
    tangentFunctional M d (x * y) =
      Coalgebra.counit (R := k) x * tangentFunctional M d y +
        Coalgebra.counit (R := k) y * tangentFunctional M d x := by
  have h := TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_apply_mul d x y
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

def nonnegPart (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (l : M →ₐc[k] LaurentPolynomial k) (D : M →ₗ[k] k) : M →ₗ[k] k :=
  Finsupp.lsum k (fun n : ℤ ↦ if 0 ≤ n then D else 0) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap ∘ₗ
      (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l).toLinearMap

theorem nonnegPart_apply_of_support_subset (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (l : M →ₐc[k] LaurentPolynomial k) (D : M →ₗ[k] k) (h : M) {s : Finset ℤ}
    (hs : (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff.support ⊆ s) :
    nonnegPart M l D h = ∑ n ∈ s,
      if 0 ≤ n then D ((CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff n)
      else 0 := by
  simp only [nonnegPart, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    AlgHom.toLinearMap_apply, AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.lsum_apply]
  rw [Finsupp.sum_of_support_subset _ hs _ fun n _ ↦ map_zero _]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  split_ifs <;> simp

theorem nonnegPart_coeff_conjugationAlgHom (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (l : M →ₐc[k] LaurentPolynomial k) (D : M →ₗ[k] k) (h : M) (j : ℤ) :
    nonnegPart M l D ((CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff j) =
      if 0 ≤ j then D ((CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff j)
      else 0 := by
  rw [nonnegPart_apply_of_support_subset M l D _ (s := {j}), Finset.sum_singleton,
    CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugationAlgHom_coeff, if_pos rfl]
  intro m hm
  rw [Finset.mem_singleton]
  by_contra hne
  exact (Finsupp.mem_support_iff.mp hm)
    (by rw [CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugationAlgHom_coeff, if_neg hne])

theorem nonnegPart_mul (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (l : M →ₐc[k] LaurentPolynomial k) (D : M →ₗ[k] k)
    (hD : ∀ x y : M, D (x * y) =
      Coalgebra.counit (R := k) x * D y + Coalgebra.counit (R := k) y * D x) (x y : M) :
    nonnegPart M l D (x * y) =
      Coalgebra.counit (R := k) x * nonnegPart M l D y +
        Coalgebra.counit (R := k) y * nonnegPart M l D x := by
  classical
  rw [nonnegPart_apply_of_support_subset M l D (x * y)
      (s := (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l (x * y)).coeff.support ∪
        ((CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l x).coeff.support ∪
          (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l y).coeff.support))
      Finset.subset_union_left,
    nonnegPart_apply_of_support_subset M l D y
      (Finset.subset_union_right.trans Finset.subset_union_right),
    nonnegPart_apply_of_support_subset M l D x
      (Finset.subset_union_left.trans Finset.subset_union_right),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [map_mul, linearMap_coeff_mul M D hD _ _ _ _ (counit_coeff_conjugationAlgHom M l x)
    (counit_coeff_conjugationAlgHom M l y) n]
  split_ifs <;> ring

def nonnegDerivation (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (l : M →ₐc[k] LaurentPolynomial k)
    (d : Derivation k M (TauCeti.Bialgebra.CounitAlgebra k M k)) :
    Derivation k M (TauCeti.Bialgebra.CounitAlgebra k M k) :=
  Derivation.mk' ((TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k M k).symm.toLinearMap ∘ₗ
      nonnegPart M l (tangentFunctional M d)) fun x y ↦ by
    apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k M k).injective
    rw [map_add, TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul]
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      AlgEquiv.apply_symm_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact nonnegPart_mul M l _ (tangentFunctional_mul M d) x y

theorem algEquivSelf_nonnegDerivation_apply (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (l : M →ₐc[k] LaurentPolynomial k)
    (d : Derivation k M (TauCeti.Bialgebra.CounitAlgebra k M k)) (x : M) :
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k M k (nonnegDerivation M l d x) =
      nonnegPart M l (tangentFunctional M d) x := by
  rw [nonnegDerivation, Derivation.coe_mk', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply]

theorem exists_add_mem_lieSubalgebra_parabolic
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (l : M →ₐc[k] LaurentPolynomial k)
    (d : Derivation k M (TauCeti.Bialgebra.CounitAlgebra k M k)) :
    ∃ d₁ ∈ (CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal l).lieSubalgebra (B := k),
    ∃ d₂ ∈ (CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal
        (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l)).lieSubalgebra (B := k),
      d = d₁ + d₂ := by
  refine ⟨nonnegDerivation M l d, ?_, d - nonnegDerivation M l d, ?_,
    (add_sub_cancel _ _).symm⟩
  · rw [TauCeti.HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _
      (CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal_toIdeal l)]
    rintro _ ⟨h, n, hn, rfl⟩
    apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k M k).injective
    rw [algEquivSelf_nonnegDerivation_apply, nonnegPart_coeff_conjugationAlgHom,
      if_neg (not_le.mpr hn), map_zero]
  · rw [TauCeti.HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _
      (CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal_toIdeal
        (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l))]
    rintro _ ⟨h, n, hn, rfl⟩
    rw [coeff_conjugationAlgHom_oppositeCocharacter, Derivation.sub_apply]
    apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k M k).injective
    rw [map_sub, algEquivSelf_nonnegDerivation_apply, nonnegPart_coeff_conjugationAlgHom,
      if_pos (by omega), map_zero, sub_eq_zero]
    rfl

theorem vanishingIdeal_eq_bot_of_parabolic_le [IsAlgClosed k]
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [Algebra.Smooth k M]
    [ConnectedSpace (PrimeSpectrum M)]
    (l : M →ₐc[k] LaurentPolynomial k) (S : Subgroup (WithConv (M →ₐ[k] k)))
    (h₁ : TauCeti.Cocharacter.parabolic k l ≤ S)
    (h₂ : TauCeti.Cocharacter.parabolic k
      (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) ≤ S) :
    TauCeti.HopfIdeal.vanishingIdeal S = ⊥ := by
  let J := TauCeti.HopfIdeal.vanishingIdeal S
  have hred : IsReduced (M ⧸ J.toIdeal) :=
    TauCeti.HopfIdeal.isReduced_quotient_vanishingIdeal S
  have hsm : Algebra.Smooth k (M ⧸ J.toIdeal) :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp
      (TauCeti.smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J).obj)
  have hJ₁ := vanishingIdeal_le_parabolicDefiningHopfIdeal M l S h₁
  have hJ₂ := vanishingIdeal_le_parabolicDefiningHopfIdeal M
    (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) S h₂
  apply CFSG.ThirdParty.TauCeti.HopfIdeal.eq_bot_of_lieSubalgebra_eq_top J
  rw [eq_top_iff]
  intro d _
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := exists_add_mem_lieSubalgebra_parabolic M l d
  apply add_mem
  · rw [TauCeti.HopfIdeal.mem_lieSubalgebra_iff] at hd₁ ⊢
    exact fun x hx => hd₁ x (TauCeti.HopfIdeal.mem_toIdeal.mpr
      (hJ₁ (TauCeti.HopfIdeal.mem_toIdeal.mp hx)))
  · rw [TauCeti.HopfIdeal.mem_lieSubalgebra_iff] at hd₂ ⊢
    exact fun x hx => hd₂ x (TauCeti.HopfIdeal.mem_toIdeal.mpr
      (hJ₂ (TauCeti.HopfIdeal.mem_toIdeal.mp hx)))

end CFSG.LieType.AlgebraicGroups.DynamicOpenCell
