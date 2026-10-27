module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.CuspidalInduction

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open CFSG.Wreathed.CentralSL2 CFSG.TwoRankLowerBound.Helpers

namespace IndexTwo

variable {C : Type} [Group C]

theorem sq_mem (A : Subgroup C) (x : C) (hxA : x ∉ A) (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A) :
    x * x ∈ A := by
  rcases hcover (x * x) with h | h
  · exact h
  · rw [mul_inv_cancel_right] at h
    exact absurd h hxA

theorem inv_conj_eq (A : Subgroup C) (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (x : C) (hxA : x ∉ A)
    (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A) {a : C} (ha : x * a * x⁻¹ ∈ A) :
    x⁻¹ * a * x = x * a * x⁻¹ := by
  have hcomm := hAcomm (x * x)⁻¹ (A.inv_mem (sq_mem A x hxA hcover)) _ ha
  calc x⁻¹ * a * x = (x * x)⁻¹ * (x * a * x⁻¹) * (x * x) := by group
    _ = (x * a * x⁻¹) * (x * x)⁻¹ * (x * x) := by rw [hcomm]
    _ = x * a * x⁻¹ := by group

theorem normal (A : Subgroup C) (x : C) (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A)
    (hconj : ∀ a ∈ A, x * a * x⁻¹ ∈ A) : A.Normal where
  conj_mem n hn g := by
    rcases hcover g with hg | hg
    · exact A.mul_mem (A.mul_mem hg hn) (A.inv_mem hg)
    · have h : g * n * g⁻¹ = (g * x⁻¹) * (x * n * x⁻¹) * (g * x⁻¹)⁻¹ := by group
      rw [h]
      exact A.mul_mem (A.mul_mem hg (hconj n hn)) (A.inv_mem hg)

@[expose] noncomputable def coverEquiv (A : Subgroup C) (x : C) (hxA : x ∉ A)
    (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A) : ↥A ⊕ ↥A ≃ C :=
  Equiv.ofBijective (Sum.elim (fun a => (a : C)) (fun a => (a : C) * x))
    ⟨by
      rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exfalso
        have h' : x = (b : C)⁻¹ * (a : C) := by
          have h1 : (a : C) = (b : C) * x := h
          rw [h1]
          group
        exact hxA (h' ▸ A.mul_mem (A.inv_mem b.2) a.2)
      · exfalso
        have h' : x = (a : C)⁻¹ * (b : C) := by
          have h1 : (a : C) * x = (b : C) := h
          rw [← h1]
          group
        exact hxA (h' ▸ A.mul_mem (A.inv_mem a.2) b.2)
      · exact congrArg Sum.inr (Subtype.ext (mul_right_cancel h)),
    fun c => by
      rcases hcover c with h | h
      · exact ⟨Sum.inl ⟨c, h⟩, rfl⟩
      · exact ⟨Sum.inr ⟨c * x⁻¹, h⟩, inv_mul_cancel_right c x⟩⟩

theorem coverEquiv_inl (A : Subgroup C) (x : C) (hxA : x ∉ A)
    (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A) (a : ↥A) : coverEquiv A x hxA hcover (Sum.inl a) = a :=
  rfl

theorem coverEquiv_inr (A : Subgroup C) (x : C) (hxA : x ∉ A)
    (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A) (a : ↥A) :
    coverEquiv A x hxA hcover (Sum.inr a) = (a : C) * x :=
  rfl

theorem inducedFunction_of_mem [Fintype C] (A : Subgroup C) (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (x : C) (hxA : x ∉ A) (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A) (σ : ↥A → ↥A)
    (hσ : ∀ a : ↥A, (σ a : C) = x * (a : C) * x⁻¹) (μ : ↥A → ℂ) (a : ↥A) :
    inducedFunction A μ (a : C) = μ a + μ (σ a) := by
  classical
  have hcard : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hconj : ∀ b : ↥A, (b : C)⁻¹ * (a : C) * (b : C) = (a : C) := fun b => by
    rw [mul_assoc, hAcomm _ a.2 _ b.2, inv_mul_cancel_left]
  rw [inducedFunction_eq_extendByZero, ← (coverEquiv A x hxA hcover).sum_comp, Fintype.sum_sum_type]
  have h1 : ∀ b : ↥A, extendByZero A μ ((coverEquiv A x hxA hcover (Sum.inl b))⁻¹ * (a : C) *
      coverEquiv A x hxA hcover (Sum.inl b)) = μ a := fun b => by
    rw [coverEquiv_inl, hconj b]
    exact extendByZero_coe A μ a
  have h2 : ∀ b : ↥A, extendByZero A μ ((coverEquiv A x hxA hcover (Sum.inr b))⁻¹ * (a : C) *
      coverEquiv A x hxA hcover (Sum.inr b)) = μ (σ a) := fun b => by
    have hb : ((b : C) * x)⁻¹ * (a : C) * ((b : C) * x) = (σ a : C) :=
      calc ((b : C) * x)⁻¹ * (a : C) * ((b : C) * x)
          = x⁻¹ * ((b : C)⁻¹ * (a : C) * (b : C)) * x := by group
        _ = x⁻¹ * (a : C) * x := by rw [hconj b]
        _ = x * (a : C) * x⁻¹ :=
          inv_conj_eq A hAcomm x hxA hcover (by rw [← hσ a]; exact (σ a).2)
        _ = (σ a : C) := (hσ a).symm
    rw [coverEquiv_inr, hb]
    exact extendByZero_coe A μ (σ a)
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_congr rfl fun b _ => h2 b, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  field_simp

theorem inducedFunction_of_not_mem [Fintype C] (A : Subgroup C) (x : C)
    (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A) (σ : ↥A → ↥A)
    (hσ : ∀ a : ↥A, (σ a : C) = x * (a : C) * x⁻¹) (μ : ↥A → ℂ) {g : C} (hg : g ∉ A) :
    inducedFunction A μ g = 0 := by
  classical
  have hnormal : A.Normal :=
    normal A x hcover fun a ha => by rw [← hσ ⟨a, ha⟩]; exact (σ ⟨a, ha⟩).2
  rw [inducedFunction_eq_extendByZero, Finset.sum_eq_zero, mul_zero]
  intro c _
  apply extendByZero_of_not_mem
  intro h
  apply hg
  have h' : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
  rw [← h']
  exact hnormal.conj_mem _ h c

end IndexTwo

theorem exists_irr_induced_index_two
    {C : Type} [Group C] [Finite C] (A : Subgroup C)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (x : C) (hxA : x ∉ A) (hcover : ∀ c : C, c ∈ A ∨ c * x⁻¹ ∈ A)
    (lam : ↥A →* ℂˣ) (σ : ↥A →* ↥A) (hσ : ∀ a : ↥A, (σ a : C) = x * (a : C) * x⁻¹)
    (hne : ∃ a : ↥A, lam (σ a) ≠ lam a) :
    ∃ ω ∈ BlocksIrr C, ω 1 = 2 ∧ (∀ a : ↥A, ω a = (lam a : ℂ) + (lam (σ a) : ℂ)) ∧
      (∀ c : C, c ∉ A → ω c = 0) := by
  classical
  have : Fintype C := Fintype.ofFinite C
  let μ : ↥A →* ℂ := (Units.coeHom ℂ).comp lam
  have hval : ∀ a : ↥A, inducedFunction A (fun a => μ a) (a : C) =
      (lam a : ℂ) + (lam (σ a) : ℂ) := fun a =>
    IndexTwo.inducedFunction_of_mem A hAcomm x hxA hcover σ hσ (fun a => μ a) a
  have hzero : ∀ c : C, c ∉ A → inducedFunction A (fun a => μ a) c = 0 := fun c hc =>
    IndexTwo.inducedFunction_of_not_mem A x hcover σ hσ _ hc
  have hone : inducedFunction A (fun a => μ a) 1 = 2 := by
    have h := hval 1
    rw [Subgroup.coe_one] at h
    rw [h, map_one, map_one]
    norm_num
  have hlam : lam ≠ lam.comp σ := by
    intro h
    obtain ⟨a, ha⟩ := hne
    apply ha
    have := DFunLike.congr_fun h a
    simpa using this.symm
  have hclass : BlocksIsClassFunction (inducedFunction A (fun a => μ a)) := fun g h =>
    inducedFunction_conjugate A _ g h
  have hnorm : BlocksInnerProduct (inducedFunction A (fun a => μ a))
      (inducedFunction A (fun a => μ a)) = 1 := by
    rw [blocksInnerProduct_inducedFunction_left A _ _ hclass]
    have hfun : (fun h : ↥A => inducedFunction A (fun a => μ a) (h : C)) =
        fun h => (lam h : ℂ) + (lam (σ h) : ℂ) := funext hval
    rw [hfun]
    have hadd : BlocksInnerProduct (fun a : ↥A => (μ a : ℂ))
        (fun h => (lam h : ℂ) + (lam (σ h) : ℂ)) =
        BlocksInnerProduct (fun a : ↥A => (lam a : ℂ)) (fun h => (lam h : ℂ)) +
        BlocksInnerProduct (fun a : ↥A => (lam a : ℂ)) (fun h => ((lam.comp σ) h : ℂ)) := by
      unfold BlocksInnerProduct
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      simp [μ, mul_add]
    rw [hadd, blocksInnerProduct_units_hom, blocksInnerProduct_units_hom, ite_eq_left rfl,
      ite_eq_right hlam]
    norm_num
  have hvc : inducedFunction A (fun a => μ a) ∈ BlocksVChar C :=
    CFSG.Wreathed.CentralSL2.inducedFunction_mem_blocksVChar A μ
  exact ⟨_, mem_blocksIrr_of_virtual_norm_one hvc hnorm (by rw [hone]; norm_num), hone, hval,
    hzero⟩

end CFSG.GH74.GLS.Stage4.Q3n
