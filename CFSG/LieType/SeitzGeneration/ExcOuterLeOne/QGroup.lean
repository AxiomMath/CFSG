module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.A2Hom

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

section QDefs

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def QGens (τ : Tag) (K : Type) [Field K] : Set ↥(adjointGroup τ K) :=
  {g | ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ 0 < lvl τ γ ∧ ∃ c : K, g = xPar (rootOperatorFamily τ) γ c}

@[expose] noncomputable def Qgrp (τ : Tag) (K : Type) [Field K] : Subgroup ↥(adjointGroup τ K) :=
  Subgroup.closure (QGens τ K)

@[expose] noncomputable def ULGens (τ : Tag) (K : Type) [Field K] : Set ↥(adjointGroup τ K) :=
  {g | ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ lvl τ γ = 0 ∧ 0 < height γ ∧
    ∃ c : K, g = xPar (rootOperatorFamily τ) γ c}

@[expose] noncomputable def ULgrp (τ : Tag) (K : Type) [Field K] : Subgroup ↥(adjointGroup τ K) :=
  Subgroup.closure (ULGens τ K)

@[expose] noncomputable def StabSL2 (τ : Tag) (K : Type) [Field K] : Subgroup ↥(adjointGroup τ K) where
  carrier := {m | ∃ χ : Kˣ,
    (∀ c : K, m * xPar (rootOperatorFamily τ) (hiRoot τ) c * m⁻¹ =
      xPar (rootOperatorFamily τ) (hiRoot τ) ((χ : K) * c)) ∧
    (∀ c : K, m * xPar (rootOperatorFamily τ) (-hiRoot τ) c * m⁻¹ =
      xPar (rootOperatorFamily τ) (-hiRoot τ) (((χ⁻¹ : Kˣ) : K) * c))}
  one_mem' := ⟨1, fun c => by simp, fun c => by simp⟩
  mul_mem' := by
    rintro m₁ m₂ ⟨χ₁, h₁, h₁'⟩ ⟨χ₂, h₂, h₂'⟩
    refine ⟨χ₁ * χ₂, fun c => ?_, fun c => ?_⟩
    · have e : m₁ * m₂ * xPar (rootOperatorFamily τ) (hiRoot τ) c * (m₁ * m₂)⁻¹ =
          m₁ * (m₂ * xPar (rootOperatorFamily τ) (hiRoot τ) c * m₂⁻¹) * m₁⁻¹ := by group
      rw [e, h₂ c, h₁ ((χ₂ : K) * c), Units.val_mul, mul_assoc]
    · have e : m₁ * m₂ * xPar (rootOperatorFamily τ) (-hiRoot τ) c * (m₁ * m₂)⁻¹ =
          m₁ * (m₂ * xPar (rootOperatorFamily τ) (-hiRoot τ) c * m₂⁻¹) * m₁⁻¹ := by group
      rw [e, h₂' c, h₁' (((χ₂⁻¹ : Kˣ) : K) * c)]
      congr 1
      rw [mul_inv_rev, Units.val_mul]
      ring
  inv_mem' := by
    rintro m ⟨χ, h, h'⟩
    refine ⟨χ⁻¹, fun c => ?_, fun c => ?_⟩
    · have := h (((χ⁻¹ : Kˣ) : K) * c)
      rw [← mul_assoc, Units.mul_inv, one_mul] at this
      rw [eq_comm, ← mul_inv_eq_iff_eq_mul, ← inv_mul_eq_iff_eq_mul] at this
      simpa [mul_assoc] using this
    · have := h' ((χ : K) * c)
      simp only [← mul_assoc, Units.inv_mul, one_mul] at this
      rw [eq_comm, ← mul_inv_eq_iff_eq_mul, ← inv_mul_eq_iff_eq_mul] at this
      simpa [mul_assoc] using this

end QDefs

section QLemmas

variable {τ : Tag} {K : Type} [Field K]

theorem lvl_add (u v : Fin τ.rank → ℤ) : lvl τ (u + v) = lvl τ u + lvl τ v := rfl
theorem lvl_neg (u : Fin τ.rank → ℤ) : lvl τ (-u) = -lvl τ u := rfl
theorem lvl_nsmul (n : ℕ) (u : Fin τ.rank → ℤ) : lvl τ (n • u) = n * lvl τ u := by
  simp [lvl]

theorem xPar_mem_Qgrp {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (h : 0 < lvl τ γ) (c : K) :
    xPar (rootOperatorFamily τ) γ c ∈ Qgrp τ K :=
  Subgroup.subset_closure ⟨γ, hγ, h, c, rfl⟩

theorem commute_Q_hiRoot (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {q : ↥(adjointGroup τ K)}
    (hq : q ∈ Qgrp τ K) (c : K) :
    Commute q (xPar (rootOperatorFamily τ) (hiRoot τ) c) := by
  obtain ⟨D, hD, hG2⟩ := exists_adjData_valid_all hτ
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl, a, rfl⟩ := hx
    refine commute_xPar hD hG2 hγ (hiRoot_isMax hτ).1 ?_ (not_isRoot_add_hiRoot_of_lvl_nonneg hτ hl) a c
    intro h
    have h1 := congrArg (lvl τ) h
    rw [lvl_add, lvl_hiRoot hτ] at h1
    have h2 : lvl τ (0 : Fin τ.rank → ℤ) = 0 := rfl
    omega
  | one => exact Commute.one_left _
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

theorem conj_gen_level_one (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hl : 0 < lvl τ γ) (hδ : IsRoot τ δ) (hδl : lvl τ δ = 1) (a : K) :
    ∃ c : K, ∀ t : K, xPar (rootOperatorFamily τ) γ a * xPar (rootOperatorFamily τ) δ t *
        (xPar (rootOperatorFamily τ) γ a)⁻¹ =
      xPar (rootOperatorFamily τ) δ t * xPar (rootOperatorFamily τ) (hiRoot τ) (c * t) := by
  classical
  obtain ⟨D, hD, hG2⟩ := exists_adjData_valid_all hτ
  have hθ := (hiRoot_isMax hτ).1
  have hcommθδ : ∀ t u : K, Commute (xPar (rootOperatorFamily τ) δ t)
      (xPar (rootOperatorFamily τ) (hiRoot τ) u) := fun t u => by
    refine commute_xPar hD hG2 hδ hθ ?_ ?_ t u
    · intro h
      have h1 := congrArg (lvl τ) h
      rw [lvl_add, lvl_hiRoot hτ, hδl] at h1
      have h2 : lvl τ (0 : Fin τ.rank → ℤ) = 0 := rfl
      omega
    · exact not_isRoot_add_hiRoot_of_lvl_nonneg hτ (γ := δ) (by omega)
  by_cases hγδ : γ = δ
  · subst hγδ
    refine ⟨0, fun t => ?_⟩
    have : xPar (rootOperatorFamily τ) γ a * xPar (rootOperatorFamily τ) γ t =
        xPar (rootOperatorFamily τ) γ t * xPar (rootOperatorFamily τ) γ a := by
      rw [← xPar_add, ← xPar_add, add_comm]
    rw [zero_mul, xPar_zero, mul_one, this, mul_inv_cancel_right]
  · have hne' : γ ≠ -δ := fun h => by
      have h1 := congrArg (lvl τ) h
      rw [lvl_neg] at h1
      omega
    have hcomm := commutator_xPar (F := rootOperatorFamily τ) hD hG2 hγ hδ hγδ hne' a
    have h12 : ¬IsRoot τ (γ + (2 : ℕ) • δ) := fun h => by
      have := (lvl_bound hτ h).2
      rw [lvl_add, lvl_nsmul, hδl] at this
      omega
    have h21 : ¬IsRoot τ ((2 : ℕ) • γ + δ) := fun h => by
      have := (lvl_bound hτ h).2
      rw [lvl_add, lvl_nsmul, hδl] at this
      omega
    by_cases hs : IsRoot τ (γ + δ)
    · have hlv : lvl τ (γ + δ) = 2 := by
        have := (lvl_bound hτ hs).2
        rw [lvl_add, hδl] at this ⊢
        omega
      have hθeq : γ + δ = hiRoot τ := eq_hiRoot_of_lvl_eq_two hτ hs hlv
      refine ⟨(RootOperatorFamily'.coeff11 (rootOperatorFamily τ) hD ⟨γ, hγ⟩ ⟨δ, hδ⟩ : K) * a, fun t => ?_⟩
      have h := hcomm t
      rw [xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one, hθeq] at h
      have e : xPar (rootOperatorFamily τ) γ a * xPar (rootOperatorFamily τ) δ t *
          (xPar (rootOperatorFamily τ) γ a)⁻¹ = ⁅xPar (rootOperatorFamily τ) γ a,
            xPar (rootOperatorFamily τ) δ t⁆ * xPar (rootOperatorFamily τ) δ t := by
        rw [commutatorElement_def]; group
      rw [e, h, ((hcommθδ t _).eq).symm]
    · refine ⟨0, fun t => ?_⟩
      have h := hcomm t
      rw [xPar_of_not_isRoot hs, xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one] at h
      have e : xPar (rootOperatorFamily τ) γ a * xPar (rootOperatorFamily τ) δ t *
          (xPar (rootOperatorFamily τ) γ a)⁻¹ = ⁅xPar (rootOperatorFamily τ) γ a,
            xPar (rootOperatorFamily τ) δ t⁆ * xPar (rootOperatorFamily τ) δ t := by
        rw [commutatorElement_def]; group
      rw [e, h, zero_mul, xPar_zero, mul_one, one_mul]

theorem Q_conj_delta (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {q : ↥(adjointGroup τ K)}
    (hq : q ∈ Qgrp τ K) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hδl : lvl τ δ = 1) :
    ∃ c : K, ∀ t : K, q * xPar (rootOperatorFamily τ) δ t * q⁻¹ =
      xPar (rootOperatorFamily τ) δ t * xPar (rootOperatorFamily τ) (hiRoot τ) (c * t) := by
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl, a, rfl⟩ := hx
    exact conj_gen_level_one hτ hγ hl hδ hδl a
  | one => exact ⟨0, fun t => by simp [xPar_zero]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨c, hc⟩ := ihx
    obtain ⟨c', hc'⟩ := ihy
    refine ⟨c + c', fun t => ?_⟩
    have e : x * y * xPar (rootOperatorFamily τ) δ t * (x * y)⁻¹ =
        x * (y * xPar (rootOperatorFamily τ) δ t * y⁻¹) * x⁻¹ := by group
    rw [e, hc' t]
    have e2 : x * (xPar (rootOperatorFamily τ) δ t * xPar (rootOperatorFamily τ) (hiRoot τ) (c' * t)) * x⁻¹ =
        (x * xPar (rootOperatorFamily τ) δ t * x⁻¹) *
          (x * xPar (rootOperatorFamily τ) (hiRoot τ) (c' * t) * x⁻¹) := by group
    rw [e2, hc t, ((commute_Q_hiRoot hτ hx (c' * t)).eq), mul_inv_cancel_right, mul_assoc, ← xPar_add]
    congr 2
    ring
  | inv x hx ihx =>
    obtain ⟨c, hc⟩ := ihx
    refine ⟨-c, fun t => ?_⟩
    have h1 := hc t
    have hcomm : x⁻¹ * xPar (rootOperatorFamily τ) (hiRoot τ) (c * t) * x =
        xPar (rootOperatorFamily τ) (hiRoot τ) (c * t) := by
      have := ((commute_Q_hiRoot hτ hx (c * t)).inv_left).eq
      rw [this, mul_assoc, inv_mul_cancel, mul_one]
    have h2 : xPar (rootOperatorFamily τ) δ t =
        (x⁻¹ * xPar (rootOperatorFamily τ) δ t * x) * xPar (rootOperatorFamily τ) (hiRoot τ) (c * t) := by
      calc xPar (rootOperatorFamily τ) δ t
          = x⁻¹ * (x * xPar (rootOperatorFamily τ) δ t * x⁻¹) * x := by group
        _ = x⁻¹ * (xPar (rootOperatorFamily τ) δ t * xPar (rootOperatorFamily τ) (hiRoot τ) (c * t)) * x := by
          rw [h1]
        _ = (x⁻¹ * xPar (rootOperatorFamily τ) δ t * x) *
            (x⁻¹ * xPar (rootOperatorFamily τ) (hiRoot τ) (c * t) * x) := by group
        _ = _ := by rw [hcomm]
    have h3 := eq_mul_inv_of_mul_eq h2.symm
    rw [xPar_neg] at h3
    rw [inv_inv, h3, neg_mul]

theorem xPar_mem_ULgrp {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (h0 : lvl τ γ = 0) (hh : 0 < height γ)
    (c : K) : xPar (rootOperatorFamily τ) γ c ∈ ULgrp τ K :=
  Subgroup.subset_closure ⟨γ, hγ, h0, hh, c, rfl⟩

theorem commute_UL_pm_hiRoot (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {l : ↥(adjointGroup τ K)}
    (hl : l ∈ ULgrp τ K) (c : K) :
    Commute l (xPar (rootOperatorFamily τ) (hiRoot τ) c) ∧
      Commute l (xPar (rootOperatorFamily τ) (-hiRoot τ) c) := by
  obtain ⟨D, hD, hG2⟩ := exists_adjData_valid_all hτ
  have hθ := (hiRoot_isMax hτ).1
  have hθn : IsRoot τ (-hiRoot τ) := IsRoot.neg hθ
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl0, hh, a, rfl⟩ := hx
    have hγ0 : γ ≠ 0 := fun h => by simp [h, height] at hh
    refine ⟨commute_xPar hD hG2 hγ hθ ?_ ?_ a c, commute_xPar hD hG2 hγ hθn ?_ ?_ a c⟩
    · intro h
      have h1 := congrArg (lvl τ) h
      rw [lvl_add, lvl_hiRoot hτ, hl0] at h1
      have h2 : lvl τ (0 : Fin τ.rank → ℤ) = 0 := rfl
      omega
    · intro hr
      have hlv : lvl τ (γ + hiRoot τ) = 2 := by rw [lvl_add, lvl_hiRoot hτ, hl0]; norm_num
      have := eq_hiRoot_of_lvl_eq_two hτ hr hlv
      exact hγ0 (by simpa using this)
    · intro h
      have h1 := congrArg (lvl τ) h
      rw [lvl_add, lvl_neg, lvl_hiRoot hτ, hl0] at h1
      have h2 : lvl τ (0 : Fin τ.rank → ℤ) = 0 := rfl
      omega
    · intro hr
      have hr' : IsRoot τ (-(γ + -hiRoot τ)) := IsRoot.neg hr
      have hlv : lvl τ (-(γ + -hiRoot τ)) = 2 := by
        rw [lvl_neg, lvl_add, lvl_neg, lvl_hiRoot hτ, hl0]; norm_num
      have := eq_hiRoot_of_lvl_eq_two hτ hr' hlv
      apply hγ0
      have h3 : γ = 0 := by
        have : -(γ + -hiRoot τ) = hiRoot τ := this
        rw [neg_add, neg_neg] at this
        have h4 : -γ = 0 := by
          have := congrArg (fun v => v - hiRoot τ) this
          simpa using this
        simpa using h4
      exact h3
  | one => exact ⟨Commute.one_left _, Commute.one_left _⟩
  | mul x y _ _ hx hy => exact ⟨hx.1.mul_left hy.1, hx.2.mul_left hy.2⟩
  | inv x _ hx => exact ⟨hx.1.inv_left, hx.2.inv_left⟩

theorem ULgrp_le_StabSL2 (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ULgrp τ K ≤ StabSL2 τ K := fun l hl => by
  refine ⟨1, fun c => ?_, fun c => ?_⟩
  · rw [((commute_UL_pm_hiRoot hτ hl c).1).eq, mul_inv_cancel_right]; simp
  · rw [((commute_UL_pm_hiRoot hτ hl c).2).eq, mul_inv_cancel_right]; simp

theorem xPar_mem_Qgrp' {v : Fin τ.rank → ℤ} (h : 0 < lvl τ v) (c : K) :
    xPar (rootOperatorFamily τ) v c ∈ Qgrp τ K := by
  by_cases hr : IsRoot τ v
  · exact xPar_mem_Qgrp hr h c
  · rw [xPar_of_not_isRoot hr]; exact Subgroup.one_mem _

theorem conj_QGen_of_UL_gen (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ β : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hγ0 : lvl τ γ = 0) (hβ : IsRoot τ β) (hβl : 0 < lvl τ β) (a c : K) :
    xPar (rootOperatorFamily τ) γ a * xPar (rootOperatorFamily τ) β c *
      (xPar (rootOperatorFamily τ) γ a)⁻¹ ∈ Qgrp τ K := by
  obtain ⟨D, hD, hG2⟩ := exists_adjData_valid_all hτ
  have hne : γ ≠ β := fun h => by
    have := congrArg (lvl τ) h
    omega
  have hne' : γ ≠ -β := fun h => by
    have h1 := congrArg (lvl τ) h
    rw [lvl_neg] at h1
    omega
  have hcomm := commutator_xPar (F := rootOperatorFamily τ) hD hG2 hγ hβ hne hne' a c
  have e : xPar (rootOperatorFamily τ) γ a * xPar (rootOperatorFamily τ) β c *
      (xPar (rootOperatorFamily τ) γ a)⁻¹ = ⁅xPar (rootOperatorFamily τ) γ a,
        xPar (rootOperatorFamily τ) β c⁆ * xPar (rootOperatorFamily τ) β c := by
    rw [commutatorElement_def]; group
  rw [e, hcomm]
  have hA := xPar_mem_Qgrp' (K := K) (v := γ + β) (by rw [lvl_add, hγ0]; omega)
    ((RootOperatorFamily'.coeff11 (rootOperatorFamily τ) hD ⟨γ, hγ⟩ ⟨β, hβ⟩ : K) * a * c)
  have hB := xPar_mem_Qgrp' (K := K) (v := γ + (2 : ℕ) • β) (by rw [lvl_add, lvl_nsmul, hγ0]; push_cast; omega)
    ((RootOperatorFamily'.coeff12 (rootOperatorFamily τ) hD ⟨γ, hγ⟩ ⟨β, hβ⟩ : K) * a * c ^ 2)
  have hC := xPar_mem_Qgrp' (K := K) (v := (2 : ℕ) • γ + β) (by rw [lvl_add, lvl_nsmul, hγ0]; push_cast; omega)
    ((RootOperatorFamily'.coeff21 (rootOperatorFamily τ) hD ⟨γ, hγ⟩ ⟨β, hβ⟩ : K) * a ^ 2 * c)
  have hD' : xPar (rootOperatorFamily τ) β c ∈ Qgrp τ K := xPar_mem_Qgrp hβ hβl c
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hB) hC) hD'

theorem conj_Q_of_UL_gen (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hγ0 : lvl τ γ = 0) (a : K) {q : ↥(adjointGroup τ K)} (hq : q ∈ Qgrp τ K) :
    xPar (rootOperatorFamily τ) γ a * q * (xPar (rootOperatorFamily τ) γ a)⁻¹ ∈ Qgrp τ K := by
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, hl, c, rfl⟩ := hx
    exact conj_QGen_of_UL_gen hτ hγ hγ0 hβ hl a c
  | one => simp
  | mul x y _ _ hx hy =>
    have e : xPar (rootOperatorFamily τ) γ a * (x * y) * (xPar (rootOperatorFamily τ) γ a)⁻¹ =
        (xPar (rootOperatorFamily τ) γ a * x * (xPar (rootOperatorFamily τ) γ a)⁻¹) *
          (xPar (rootOperatorFamily τ) γ a * y * (xPar (rootOperatorFamily τ) γ a)⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : xPar (rootOperatorFamily τ) γ a * x⁻¹ * (xPar (rootOperatorFamily τ) γ a)⁻¹ =
        (xPar (rootOperatorFamily τ) γ a * x * (xPar (rootOperatorFamily τ) γ a)⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ hx

theorem ULgrp_le_normalizer_Qgrp (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ULgrp τ K ≤ Subgroup.normalizer (Qgrp τ K : Set ↥(adjointGroup τ K)) := by
  rw [ULgrp, Subgroup.closure_le]
  rintro g ⟨γ, hγ, hγ0, hh, a, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · exact conj_Q_of_UL_gen hτ hγ hγ0 a
  · intro hq
    have h := conj_Q_of_UL_gen hτ hγ hγ0 (-a) hq
    have e : xPar (rootOperatorFamily τ) γ (-a) *
        (xPar (rootOperatorFamily τ) γ a * q * (xPar (rootOperatorFamily τ) γ a)⁻¹) *
          (xPar (rootOperatorFamily τ) γ (-a))⁻¹ = q := by
      rw [← xPar_neg, inv_inv]; group
    rwa [e] at h

theorem lvl_nonneg_of_height_pos (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (h : 0 < height γ) : 0 ≤ lvl τ γ := by
  have key : ∀ γ ∈ rootFinset τ, 0 < height γ → 0 ≤ lvl τ γ := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel
  exact key γ (mem_rootFinset.2 hγ) h

theorem torusElement_mem_StabSL2 (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank)
    (s : Kˣ) : torusElement τ K i s ∈ StabSL2 τ K := by
  have hθ := (hiRoot_isMax hτ).1
  have hθn : IsRoot τ (-hiRoot τ) := IsRoot.neg hθ
  refine ⟨s ^ (∑ j, τ.cartan i j * hiRoot τ j), fun c => ?_, fun c => ?_⟩
  · rw [xPar_of_isRoot hθ, (rootOperatorFamily τ).torusElement_mul_eltElement_mul_inv, ← xPar_of_isRoot hθ]
  · rw [xPar_of_isRoot hθn, (rootOperatorFamily τ).torusElement_mul_eltElement_mul_inv, ← xPar_of_isRoot hθn]
    congr 2
    simp [Finset.sum_neg_distrib, mul_neg, zpow_neg]

theorem torus_le_StabSL2 (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (⨆ i : Fin τ.rank, torus (τ := τ) K i) ≤ StabSL2 τ K := by
  refine iSup_le fun i => ?_
  rintro _ ⟨s, rfl⟩
  exact torusElement_mem_StabSL2 hτ i s

end QLemmas

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
