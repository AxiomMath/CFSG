module

public import CFSG.LargeExtraspecial.S4CELin
public import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LargeExtraspecial.S4SpU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Transvection
open scoped Matrix

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}
  {n : ℕ}

@[expose] def IsSpBasis (β : LinearMap.BilinForm (ZMod 2) V)
    (c : Basis (Fin n ⊕ Fin n) (ZMod 2) V) : Prop :=
  ∀ p q, β (c p) (c q) = if q = Sum.swap p then 1 else 0

theorem IsSpBasis.of_pairs (hβ : β.IsAlt) {c : Basis (Fin n ⊕ Fin n) (ZMod 2) V}
    (h1 : ∀ i j, β (c (Sum.inl i)) (c (Sum.inl j)) = 0)
    (h2 : ∀ i j, β (c (Sum.inr i)) (c (Sum.inr j)) = 0)
    (h3 : ∀ i j, β (c (Sum.inl i)) (c (Sum.inr j)) = if i = j then 1 else 0) :
    IsSpBasis β c := by
  rintro (i | i) (j | j)
  · rw [h1]
    simp
  · rw [h3]
    simp [eq_comm]
  · rw [OrthoF2.isAlt_symm hβ, h3]
    simp
  · rw [h2]
    simp

variable {c : Basis (Fin n ⊕ Fin n) (ZMod 2) V}

theorem IsSpBasis.repr_swap (hc : IsSpBasis β c) (v : V) (p : Fin n ⊕ Fin n) :
    c.repr v (Sum.swap p) = β v (c p) := by
  conv_rhs => rw [← c.sum_repr v]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single (Sum.swap p)]
  · rw [map_smul, LinearMap.smul_apply, hc, Sum.swap_swap, ite_eq_left rfl, smul_eq_mul,
      mul_one]
  · intro r _ hr
    rw [map_smul, LinearMap.smul_apply, hc, smul_eq_mul]
    have : p ≠ Sum.swap r := fun e => hr (by rw [e, Sum.swap_swap])
    rw [ite_eq_right this, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem IsSpBasis.apply_eq_zero (hc : IsSpBasis β c) {r p : Fin n ⊕ Fin n}
    (h : p ≠ Sum.swap r) : β (c r) (c p) = 0 := by
  rw [hc, ite_eq_right h]

@[expose] noncomputable def spIota (c : Basis (Fin n ⊕ Fin n) (ZMod 2) V) :
    StatedSp n (ZMod 2) →* (V ≃ₗ[ZMod 2] V) :=
  (glAut c).toMonoidHom.comp (StatedSp n (ZMod 2)).subtype

theorem spIota_apply (g : StatedSp n (ZMod 2)) (v : V) :
    spIota c g v = c.equivFun.symm
      (((g : GL (Fin n ⊕ Fin n) (ZMod 2)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) *ᵥ
        c.equivFun v) :=
  rfl

theorem spIota_injective : Function.Injective (spIota c) :=
  (glAut c).injective.comp (StatedSp n (ZMod 2)).subtype_injective

theorem toMatrix_glAut (M : GL (Fin n ⊕ Fin n) (ZMod 2)) :
    LinearMap.toMatrix c c ((glAut c M : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = M := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, glAut_apply, ← Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]
  have : c.equivFun (c j) = Pi.single j 1 := by
    funext k
    rw [Basis.equivFun_self, Pi.single_apply]
    by_cases hjk : j = k
    · subst hjk
      simp
    · simp [hjk, Ne.symm hjk]
  rw [this, Matrix.mulVec_single_one]
  rfl

theorem IsSpBasis.toMatrix_eq (hc : IsSpBasis β c) :
    LinearMap.BilinForm.toMatrix c β = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext (i | i) (j | j)
  · rw [LinearMap.BilinForm.toMatrix_apply, hc, Matrix.fromBlocks_apply₁₁]
    simp
  · rw [LinearMap.BilinForm.toMatrix_apply, hc, Matrix.fromBlocks_apply₁₂, Matrix.one_apply]
    simp [eq_comm]
  · rw [LinearMap.BilinForm.toMatrix_apply, hc, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Sum.swap_inr, ite_true]
      decide
    · simp [hij, Ne.symm hij]
  · rw [LinearMap.BilinForm.toMatrix_apply, hc, Matrix.fromBlocks_apply₂₂]
    simp

theorem IsSpBasis.le_range_spIota (hc : IsSpBasis β c) :
    TauCeti.BilinForm.isometryGroup β ≤ (spIota c).range := by
  intro f hf
  set M := (glAut c).symm f
  have hM : M ∈ StatedSp n (ZMod 2) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    have hcomp : β.comp ((f : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
        ((f : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = β := by
      ext x y
      exact TauCeti.BilinForm.mem_isometryGroup_iff.mp hf x y
    have h := LinearMap.BilinForm.toMatrix_comp c c β ((f : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
      ((f : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
    rw [hcomp, show f = glAut c M from (MulEquiv.apply_symm_apply _ f).symm, toMatrix_glAut,
      hc.toMatrix_eq] at h
    exact h.symm
  exact ⟨⟨M, hM⟩, (glAut c).apply_symm_apply f⟩

open CFSG.LieType.Universal.Symplectic.SpExtras in
theorem spIota_spElt_apply {p q : Fin n ⊕ Fin n} (hq : q ≠ Sum.swap p) (t : ZMod 2) (v : V) :
    spIota c (spElt p q t) v = v + t • (if q = p then c.repr v (Sum.swap p) • c p
      else c.repr v (Sum.swap q) • c p + c.repr v (Sum.swap p) • c q) := by
  rw [spIota_apply, ← mat_apply, mat_spElt hq t, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, map_add, map_smul, LinearEquiv.symm_apply_apply]
  congr 2
  split_ifs
  · rw [Matrix.single_mulVec_eq, one_mul, map_smul, Basis.equivFun_symm_single,
      Basis.equivFun_apply]
  · rw [Matrix.add_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq, one_mul, one_mul,
      map_add, map_smul, map_smul, Basis.equivFun_symm_single, Basis.equivFun_symm_single,
      Basis.equivFun_apply]

theorem IsSpBasis.spIota_spElt_self (hc : IsSpBasis β c) (p : Fin n ⊕ Fin n) (t : ZMod 2)
    (v : V) : spIota c (spElt p p t) v = v + (t * β v (c p)) • c p := by
  rw [spIota_spElt_apply (Pres.swap_ne_self p).symm, ite_eq_left rfl, hc.repr_swap, smul_smul]

theorem IsSpBasis.spIota_spElt (hc : IsSpBasis β c) {p q : Fin n ⊕ Fin n} (hqp : q ≠ p)
    (hq : q ≠ Sum.swap p) (t : ZMod 2) (v : V) :
    spIota c (spElt p q t) v = v + (t * β v (c q)) • c p + (t * β v (c p)) • c q := by
  rw [spIota_spElt_apply hq, ite_eq_right hqp, hc.repr_swap, hc.repr_swap, smul_add, smul_smul,
    smul_smul, add_assoc]

theorem IsSpBasis.spIota_spElt_one_self (hβ : β.IsAlt) (hc : IsSpBasis β c)
    (p : Fin n ⊕ Fin n) : spIota c (spElt p p 1) = spTransvection β hβ (c p) :=
  LinearEquiv.ext fun v => by rw [hc.spIota_spElt_self, one_mul, spTransvection_apply]

theorem IsSpBasis.spIota_spElt_one (hβ : β.IsAlt) (hc : IsSpBasis β c) {p q : Fin n ⊕ Fin n}
    (hqp : q ≠ p) (hq : q ≠ Sum.swap p) :
    spIota c (spElt p q 1) = spRho hβ (hc.apply_eq_zero hq) 0 :=
  LinearEquiv.ext fun v => by
    rw [hc.spIota_spElt hqp hq, spRho_apply, one_mul, one_mul, zero_mul, add_zero,
      add_right_comm]

theorem IsSpBasis.spIota_spElt_mem (hβ : β.IsAlt) (hc : IsSpBasis β c) {p q : Fin n ⊕ Fin n}
    (hq : q ≠ Sum.swap p) (t : ZMod 2) : spIota c (spElt p q t) ∈ spPointRadical β (c p) := by
  rcases OrthoF2.zmod2_eq_zero_or_eq_one t with rfl | rfl
  · rw [spElt_zero, map_one]
    exact one_mem _
  · by_cases hqp : q = p
    · subst hqp
      rw [hc.spIota_spElt_one_self hβ]
      exact spTransvection_mem_spPointRadical hβ _
    · rw [hc.spIota_spElt_one hβ hqp hq]
      exact spRho_mem_spPointRadical hβ _ 0

theorem IsSpBasis.spIota_spElt_apply_basis (hc : IsSpBasis β c) {p q r : Fin n ⊕ Fin n}
    (hq : q ≠ Sum.swap p) (hpr : p ≠ Sum.swap r) (hqr : q ≠ Sum.swap r) (t : ZMod 2) :
    spIota c (spElt p q t) (c r) = c r := by
  by_cases hqp : q = p
  · subst hqp
    rw [hc.spIota_spElt_self, hc.apply_eq_zero hpr, mul_zero, zero_smul, add_zero]
  · rw [hc.spIota_spElt hqp hq, hc.apply_eq_zero hpr, hc.apply_eq_zero hqr, mul_zero,
      zero_smul, add_zero, zero_smul, add_zero]

end CFSG.LargeExtraspecial.S4
