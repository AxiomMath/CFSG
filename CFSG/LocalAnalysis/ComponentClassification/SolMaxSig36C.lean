module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33A

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {α : Type*} [DecidableEq α]

theorem swap_mul_swap_comm_of_ne {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  ext x
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

@[expose] def threeCycleOf (x y z : α) : Perm α := swap x z * swap x y

theorem threeCycleOf_apply_left {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) :
    threeCycleOf x y z x = y := by
  rw [threeCycleOf, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hxy) hyz]

theorem threeCycleOf_apply_right {x y z : α} (hxz : x ≠ z) (hyz : y ≠ z) :
    threeCycleOf x y z z = x := by
  rw [threeCycleOf, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxz) (Ne.symm hyz),
    swap_apply_right]

theorem threeCycleOf_apply_of_ne {x y z w : α} (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    threeCycleOf x y z w = w := by
  rw [threeCycleOf, Perm.mul_apply, swap_apply_of_ne_of_ne hwx hwy,
    swap_apply_of_ne_of_ne hwx hwz]

theorem conj_threeCycleOf (f : Perm α) (x y z : α) :
    f * threeCycleOf x y z * f⁻¹ = threeCycleOf (f x) (f y) (f z) := by
  unfold threeCycleOf
  rw [swap_apply_apply, swap_apply_apply]
  group

theorem swap_mul_swap_eq_threeCycleOf_mul {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d = threeCycleOf a b c * threeCycleOf b c d := by
  have h : (swap a c * swap a b) * (swap b d * swap b c) = swap a b * swap c d := by
    ext x
    simp only [Perm.mul_apply, swap_apply_def]
    split_ifs <;> simp_all
  exact h.symm

variable [Fintype α]

theorem isThreeCycle_threeCycleOf {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (threeCycleOf x y z).IsThreeCycle :=
  Perm.isThreeCycle_swap_mul_swap_same hxz hxy (Ne.symm hyz)

@[expose] def oddCentGen (σ : Perm α) : Subgroup (Perm α) :=
  closure {π | π ∈ alternatingGroup α ∧ π * σ = σ * π ∧ Odd (orderOf π)}

theorem subset_oddCentGen {σ π : Perm α} (hπA : π ∈ alternatingGroup α) (hπσ : π * σ = σ * π)
    (hπ : Odd (orderOf π)) : π ∈ oddCentGen σ :=
  subset_closure ⟨hπA, hπσ, hπ⟩

theorem commute_of_mem_oddCentGen {σ π : Perm α} (hπ : π ∈ oddCentGen σ) :
    π * σ = σ * π := by
  have h : oddCentGen σ ≤ centralizer ({σ} : Set (Perm α)) := by
    refine (closure_le _).mpr ?_
    rintro π ⟨-, hπσ, -⟩
    exact mem_centralizer_singleton_iff.mpr hπσ
  exact mem_centralizer_singleton_iff.mp (h hπ)

theorem threeCycleOf_mem_oddCentGen {σ : Perm α} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hσ : σ * threeCycleOf x y z * σ⁻¹ = threeCycleOf x y z) :
    threeCycleOf x y z ∈ oddCentGen σ := by
  have h3 := isThreeCycle_threeCycleOf hxy hxz hyz
  refine subset_oddCentGen (Perm.mem_alternatingGroup.mpr h3.sign) ?_ ?_
  · calc threeCycleOf x y z * σ = σ * threeCycleOf x y z * σ⁻¹ * σ := by rw [hσ]
      _ = σ * threeCycleOf x y z := by group
  · rw [h3.orderOf]
    decide

theorem fix_pair_mem_oddCentGen {σ : Perm α} {a b c d : α} (ha : σ a = a) (hb : σ b = b)
    (hc : σ c = c) (hd : σ d = d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : swap a b * swap c d ∈ oddCentGen σ := by
  rw [swap_mul_swap_eq_threeCycleOf_mul hab hac had hbc hbd hcd]
  refine mul_mem (threeCycleOf_mem_oddCentGen hab hac hbc ?_)
    (threeCycleOf_mem_oddCentGen hbc hbd hcd ?_)
  · rw [conj_threeCycleOf, ha, hb, hc]
  · rw [conj_threeCycleOf, hb, hc, hd]

theorem pair_mem_oddCentGen {σ : Perm α} (hσ : σ * σ = 1) {a₁ a₂ a₃ : α} (h₁ : σ a₁ ≠ a₁)
    (h₂ : σ a₂ ≠ a₂) (h₃ : σ a₃ ≠ a₃) (h₂₁ : a₂ ≠ a₁) (h₂₁' : a₂ ≠ σ a₁) (h₃₁ : a₃ ≠ a₁)
    (h₃₁' : a₃ ≠ σ a₁) (h₃₂ : a₃ ≠ a₂) (h₃₂' : a₃ ≠ σ a₂) :
    swap a₂ (σ a₂) * swap a₃ (σ a₃) ∈ oddCentGen σ := by
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  set b₁ := σ a₁ with hb₁
  set b₂ := σ a₂ with hb₂
  set b₃ := σ a₃ with hb₃
  have hσb₁ : σ b₁ = a₁ := hσσ a₁
  have hσb₂ : σ b₂ = a₂ := hσσ a₂
  have hσb₃ : σ b₃ = a₃ := hσσ a₃
  have e1 : a₁ ≠ b₁ := Ne.symm h₁
  have e2 : a₂ ≠ b₂ := Ne.symm h₂
  have e3 : a₃ ≠ b₃ := Ne.symm h₃
  have f21 : b₂ ≠ a₁ := fun h => h₂₁' (by rw [hb₁, ← h, hb₂, hσσ])
  have f21' : b₂ ≠ b₁ := fun h => h₂₁ (σ.injective h)
  have f31 : b₃ ≠ a₁ := fun h => h₃₁' (by rw [hb₁, ← h, hb₃, hσσ])
  have f31' : b₃ ≠ b₁ := fun h => h₃₁ (σ.injective h)
  have f32 : b₃ ≠ a₂ := fun h => h₃₂' (by rw [hb₂, ← h, hb₃, hσσ])
  have f32' : b₃ ≠ b₂ := fun h => h₃₂ (σ.injective h)
  set c₁ := threeCycleOf a₁ a₂ a₃ with hc₁
  set c₂ := threeCycleOf b₁ b₂ b₃ with hc₂
  have hc₁3 : c₁.IsThreeCycle :=
    isThreeCycle_threeCycleOf (Ne.symm h₂₁) (Ne.symm h₃₁) (Ne.symm h₃₂)
  have hc₂3 : c₂.IsThreeCycle :=
    isThreeCycle_threeCycleOf (Ne.symm f21') (Ne.symm f31') (Ne.symm f32')
  have hdisj : c₁.Disjoint c₂ := by
    intro w
    by_cases hw1 : w = a₁
    · right
      rw [hw1]
      exact threeCycleOf_apply_of_ne e1 (Ne.symm f21) (Ne.symm f31)
    by_cases hw2 : w = a₂
    · right
      rw [hw2]
      exact threeCycleOf_apply_of_ne h₂₁' e2 (Ne.symm f32)
    by_cases hw3 : w = a₃
    · right
      rw [hw3]
      exact threeCycleOf_apply_of_ne h₃₁' h₃₂' e3
    · left
      exact threeCycleOf_apply_of_ne hw1 hw2 hw3
  set π := c₁ * c₂ with hπdef
  have hcomm : c₁ * c₂ = c₂ * c₁ := hdisj.commute.eq
  have hσc₁ : σ * c₁ * σ⁻¹ = c₂ := by rw [hc₁, conj_threeCycleOf]
  have hσc₂ : σ * c₂ * σ⁻¹ = c₁ := by rw [hc₂, conj_threeCycleOf, hσb₁, hσb₂, hσb₃]
  have hπσ : π * σ = σ * π := by
    have h1 : σ * π * σ⁻¹ = π := by
      calc σ * π * σ⁻¹ = (σ * c₁ * σ⁻¹) * (σ * c₂ * σ⁻¹) := by rw [hπdef]; group
        _ = π := by rw [hσc₁, hσc₂, hπdef, hcomm]
    calc π * σ = σ * π * σ⁻¹ * σ := by rw [h1]
      _ = σ * π := by group
  have hπodd : Odd (orderOf π) := by
    have h3 : π ^ 3 = 1 := by
      have h1 : c₁ ^ 3 = 1 := by rw [← hc₁3.orderOf]; exact pow_orderOf_eq_one c₁
      have h2 : c₂ ^ 3 = 1 := by rw [← hc₂3.orderOf]; exact pow_orderOf_eq_one c₂
      rw [hπdef, (show Commute c₁ c₂ from hcomm).mul_pow 3, h1, h2, one_mul]
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
  have hπA : π ∈ alternatingGroup α := by
    rw [Perm.mem_alternatingGroup, hπdef, map_mul, hc₁3.sign, hc₂3.sign, mul_one]
  set x := swap a₁ b₁ * swap a₃ b₃ with hxdef
  have hxσ : x * σ = σ * x := by
    have h1 := swap_mul_comm_of_involution hσ a₁
    have h3 := swap_mul_comm_of_involution hσ a₃
    rw [hxdef, mul_assoc, h3, ← mul_assoc, h1, mul_assoc]
  have hxA : x ∈ alternatingGroup α := by
    rw [Perm.mem_alternatingGroup, hxdef, map_mul, Perm.sign_swap e1, Perm.sign_swap e3]
    simp
  have hπ'σ : x * π * x⁻¹ * σ = σ * (x * π * x⁻¹) := by
    have hx'σ : x⁻¹ * σ = σ * x⁻¹ := by
      calc x⁻¹ * σ = x⁻¹ * (σ * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * σ) * x⁻¹ := by rw [hxσ]
        _ = σ * x⁻¹ := by group
    calc x * π * x⁻¹ * σ = x * π * (x⁻¹ * σ) := by group
      _ = x * π * (σ * x⁻¹) := by rw [hx'σ]
      _ = x * (π * σ) * x⁻¹ := by group
      _ = x * (σ * π) * x⁻¹ := by rw [hπσ]
      _ = (x * σ) * π * x⁻¹ := by group
      _ = (σ * x) * π * x⁻¹ := by rw [hxσ]
      _ = σ * (x * π * x⁻¹) := by group
  have hπ'odd : Odd (orderOf (x * π * x⁻¹)) := by
    rw [show x * π * x⁻¹ = MulAut.conj x π from rfl, MulEquiv.orderOf_eq]
    exact hπodd
  have hmem : x * π * x⁻¹ * π⁻¹ ∈ oddCentGen σ :=
    mul_mem (subset_oddCentGen (mul_mem (mul_mem hxA hπA) (inv_mem hxA)) hπ'σ hπ'odd)
      (inv_mem (subset_oddCentGen hπA hπσ hπodd))
  have hπa₁ : π a₁ = a₂ := by
    rw [hπdef, Perm.mul_apply, hc₂, threeCycleOf_apply_of_ne e1 (Ne.symm f21) (Ne.symm f31), hc₁,
      threeCycleOf_apply_left (Ne.symm h₂₁) (Ne.symm h₃₂)]
  have hπb₁ : π b₁ = b₂ := by
    rw [hπdef, Perm.mul_apply, hc₂, threeCycleOf_apply_left (Ne.symm f21') (Ne.symm f32'), hc₁,
      threeCycleOf_apply_of_ne f21 (Ne.symm e2) (Ne.symm h₃₂')]
  have hπa₃ : π a₃ = a₁ := by
    rw [hπdef, Perm.mul_apply, hc₂, threeCycleOf_apply_of_ne h₃₁' h₃₂' e3, hc₁,
      threeCycleOf_apply_right (Ne.symm h₃₁) (Ne.symm h₃₂)]
  have hπb₃ : π b₃ = b₁ := by
    rw [hπdef, Perm.mul_apply, hc₂, threeCycleOf_apply_right (Ne.symm f31') (Ne.symm f32'), hc₁,
      threeCycleOf_apply_of_ne (Ne.symm e1) (Ne.symm h₂₁') (Ne.symm h₃₁')]
  have hπx : π * x * π⁻¹ = swap a₂ b₂ * swap a₁ b₁ := by
    calc π * x * π⁻¹ = (π * swap a₁ b₁ * π⁻¹) * (π * swap a₃ b₃ * π⁻¹) := by
          rw [hxdef]; group
      _ = swap a₂ b₂ * swap a₁ b₁ := by
          rw [← swap_apply_apply, ← swap_apply_apply, hπa₁, hπb₁, hπa₃, hπb₃]
  have h13 : swap a₁ b₁ * swap a₃ b₃ = swap a₃ b₃ * swap a₁ b₁ :=
    swap_mul_swap_comm_of_ne (Ne.symm h₃₁) (Ne.symm f31) (Ne.symm h₃₁') (Ne.symm f31')
  have h23 : swap a₃ b₃ * swap a₂ b₂ = swap a₂ b₂ * swap a₃ b₃ :=
    swap_mul_swap_comm_of_ne h₃₂ h₃₂' f32 f32'
  have hcomm' : x * π * x⁻¹ * π⁻¹ = swap a₂ b₂ * swap a₃ b₃ := by
    calc x * π * x⁻¹ * π⁻¹ = x * (π * x * π⁻¹)⁻¹ := by group
      _ = swap a₁ b₁ * swap a₃ b₃ * (swap a₁ b₁ * swap a₂ b₂) := by
          rw [hπx, mul_inv_rev, swap_inv, swap_inv]
      _ = swap a₃ b₃ * (swap a₁ b₁ * (swap a₁ b₁ * swap a₂ b₂)) := by rw [h13, mul_assoc]
      _ = swap a₂ b₂ * swap a₃ b₃ := by rw [swap_mul_self_mul, h23]
  rw [← hcomm']
  exact hmem

end CFSG.ComponentClassification.SolMax
