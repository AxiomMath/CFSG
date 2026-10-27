module

public import CFSG.LocalAnalysis.EvenBN.U5.Model
public import CFSG.RankThree.CentralLiftU.UnitaryTorus
public import CFSG.RankThree.CentralLiftU.UnitaryBorelLift
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
public import CFSG.RankThree.CentralLiftU.UnitaryTriRoots

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section Generic

theorem exists_unit_generator (h : UnitaryFieldData 2 f K) :
    ∃ ω : Kˣ, orderOf ω = (2 ^ f) ^ 2 - 1 := by
  have := h.finite
  obtain ⟨ω, hω⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  exact ⟨ω, by rw [hω, Nat.card_units, h.card_eq_sq]⟩

theorem bar_zpow (h : UnitaryFieldData 2 f K) (ω : Kˣ) (m : ℤ) :
    h.bar ((ω ^ m : Kˣ) : K) = ((ω ^ ((2 ^ f : ℕ) * m) : Kˣ) : K) := by
  rw [UnitaryFieldData.bar_apply, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm]

theorem zpow_val_eq_iff {ω : Kˣ} {Q : ℕ} (hω : orderOf ω = Q) {m n : ℤ} :
    ((ω ^ m : Kˣ) : K) = ((ω ^ n : Kˣ) : K) ↔ (Q : ℤ) ∣ m - n := by
  rw [Units.val_inj, ← hω, orderOf_dvd_iff_zpow_eq_one, _root_.zpow_sub, mul_inv_eq_one]

theorem not_dvd_of_lt {Q e : ℤ} (h0 : e ≠ 0) (h1 : -Q < e) (h2 : e < Q) : ¬ Q ∣ e :=
  fun hd => h0 (Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨h1, h2⟩))

theorem exists_torus_zpow (h : UnitaryFieldData 2 f K) (ω : Kˣ) (i j : ℤ) :
    ∃ t ∈ Isub h, mat t ιe₁ ιe₁ = ((ω ^ i : Kˣ) : K) ∧ mat t ιe₂ ιe₂ = ((ω ^ j : Kˣ) : K) ∧
      mat t ιz ιz = ((ω ^ (((2 ^ f : ℕ) : ℤ) * i + (2 ^ f : ℕ) * j - i - j) : Kˣ) : K) ∧
      mat t ιf₁ ιf₁ = ((ω ^ (-(((2 ^ f : ℕ) : ℤ) * i)) : Kˣ) : K) ∧
      mat t ιf₂ ιf₂ = ((ω ^ (-(((2 ^ f : ℕ) : ℤ) * j)) : Kˣ) : K) := by
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus h (ω ^ i).ne_zero (ω ^ j).ne_zero
  refine ⟨t, ht, e1, e2, ?_, ?_, ?_⟩
  · rw [e3, bar_zpow, bar_zpow, ← Units.val_mul, ← Units.val_mul, ← Units.val_div_eq_div_val,
      ← _root_.zpow_add, ← _root_.zpow_add, div_eq_mul_inv, ← _root_.zpow_neg,
      ← _root_.zpow_add]
    congr 2
    ring
  · rw [e4, bar_zpow, ← Units.val_inv_eq_inv_val, ← _root_.zpow_neg]
  · rw [e5, bar_zpow, ← Units.val_inv_eq_inv_val, ← _root_.zpow_neg]

end Generic

theorem cast_card_units (f : ℕ) : (((2 ^ f) ^ 2 - 1 : ℕ) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 - 1 := by
  have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  push_cast [Nat.cast_sub this]
  ring

theorem zpow_val_ne {ω : Kˣ} (hω : orderOf ω = (2 ^ f) ^ 2 - 1) {m n : ℤ} (k : ℤ)
    (h0 : m - n - k * (((2 ^ f : ℕ) : ℤ) ^ 2 - 1) ≠ 0)
    (h1 : -(((2 ^ f : ℕ) : ℤ) ^ 2 - 1) < m - n - k * (((2 ^ f : ℕ) : ℤ) ^ 2 - 1))
    (h2 : m - n - k * (((2 ^ f : ℕ) : ℤ) ^ 2 - 1) < ((2 ^ f : ℕ) : ℤ) ^ 2 - 1) :
    ((ω ^ m : Kˣ) : K) ≠ ((ω ^ n : Kˣ) : K) := by
  rw [Ne, zpow_val_eq_iff hω, cast_card_units]
  intro hd
  exact not_dvd_of_lt h0 h1 h2 (dvd_sub hd (dvd_mul_left _ k))

theorem zpow_val_eq {ω : Kˣ} (hω : orderOf ω = (2 ^ f) ^ 2 - 1) {m n : ℤ} (k : ℤ)
    (hk : m - n = k * (((2 ^ f : ℕ) : ℤ) ^ 2 - 1)) : ((ω ^ m : Kˣ) : K) = ((ω ^ n : Kˣ) : K) := by
  rw [zpow_val_eq_iff hω, cast_card_units, hk]
  exact dvd_mul_left _ k

theorem four_le_q {f : ℕ} (hf : 2 ≤ f) : (4 : ℤ) ≤ ((2 ^ f : ℕ) : ℤ) := by
  have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  push_cast
  exact_mod_cast this

section Centralizers

variable (hf : 2 ≤ f)
include hf

theorem U_inf_centralizer_I₁ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₁sub h : Set (hypSU h 2 1)) =
      patSub h sI₁ isPattern_sI₁ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 1 1
  have htI : t ∈ I₁sub h := mem_I₁sub.2 ⟨ht, by rw [e1, e2]⟩
  refine U_inf_centralizer_eq (torusEq_le _) isPattern_sI₁ (fun p hp => ⟨t, htI, ?_⟩) ?_
  · simp only [sI₁, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e1, e2, e3, e4, e5] <;>
      refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  · intro t' ht' a b hab hS
    obtain ⟨ht'I, ht'eq⟩ := mem_I₁sub.1 ht'
    have hf12 : mat t' ιf₂ ιf₂ = mat t' ιf₁ ιf₁ := by
      have b1 := torus_bar_mul ht'I ιe₁
      have b2 := torus_bar_mul ht'I ιe₂
      simp only [hypPartner_inl] at b1 b2
      rw [ht'eq] at b1
      exact mul_left_cancel₀ ((map_ne_zero h.bar).2 (torus_ne_zero ht'I ιe₂)) (b2.trans b1.symm)
    revert a b
    rw [forall_upper (P := fun a b => (a, b) ∉ sI₁ → mat t' a a = mat t' b b)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hS <;>
      first | exact absurd (by decide) hS | exact ht'eq | exact hf12

theorem U_inf_centralizer_I₂ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set (hypSU h 2 1)) =
      patSub h sI₂ isPattern_sI₂ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω (((2 ^ f : ℕ) : ℤ) + 1) 0
  have e3' : mat t ιz ιz = ((ω ^ (0 : ℤ) : Kˣ) : K) := e3.trans (zpow_val_eq hω 1 (by ring))
  have e4' : mat t ιf₁ ιf₁ = ((ω ^ (-(((2 ^ f : ℕ) : ℤ) + 1)) : Kˣ) : K) :=
    e4.trans (zpow_val_eq hω (-1) (by ring))
  have e5' : mat t ιf₂ ιf₂ = ((ω ^ (0 : ℤ) : Kˣ) : K) := e5.trans (by simp)
  have htI : t ∈ I₂sub h := mem_I₂sub.2 ⟨ht, by rw [e2, e3'], by rw [e3', e5']⟩
  refine U_inf_centralizer_eq (torusEq_le _) isPattern_sI₂ (fun p hp => ⟨t, htI, ?_⟩) ?_
  · simp only [sI₂, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e1, e2, e3', e4', e5'] <;>
      refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  · intro t' ht' a b hab hS
    obtain ⟨ht'I, h1, h2⟩ := mem_I₂sub.1 ht'
    revert a b
    rw [forall_upper (P := fun a b => (a, b) ∉ sI₂ → mat t' a a = mat t' b b)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hS <;>
      first | exact absurd (by decide) hS | exact h1 | exact h2 | exact h1.trans h2

theorem U_inf_centralizer_I₃ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₃sub h : Set (hypSU h 2 1)) = ZPsub h := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 0 1
  have htI : t ∈ I₃sub h := mem_I₃sub.2 ⟨ht, by rw [e1, e4]; simp⟩
  refine U_inf_centralizer_eq (torusEq_le _) isPattern_sZP (fun p hp => ⟨t, htI, ?_⟩) ?_
  · simp only [sZP, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e1, e2, e3, e4, e5] <;>
      refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  · intro t' ht' a b hab hS
    obtain ⟨ht'I, ht'eq⟩ := mem_I₃sub.1 ht'
    revert a b
    rw [forall_upper (P := fun a b => (a, b) ∉ sZP → mat t' a a = mat t' b b)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hS <;>
      first | exact absurd (by decide) hS | exact ht'eq

theorem U_inf_centralizer_I₄ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₄sub h : Set (hypSU h 2 1)) =
      patSub h sI₄ isPattern_sI₄ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 1 (-((2 ^ f : ℕ) : ℤ))
  have e3' : mat t ιz ιz = ((ω ^ (2 * ((2 ^ f : ℕ) : ℤ) - 2) : Kˣ) : K) :=
    e3.trans (zpow_val_eq hω (-1) (by ring))
  have e5' : mat t ιf₂ ιf₂ = ((ω ^ (1 : ℤ) : Kˣ) : K) := e5.trans (zpow_val_eq hω 1 (by ring))
  have htI : t ∈ I₄sub h := mem_I₄sub.2 ⟨ht, by rw [e1, e5']⟩
  refine U_inf_centralizer_eq (torusEq_le _) isPattern_sI₄ (fun p hp => ⟨t, htI, ?_⟩) ?_
  · simp only [sI₄, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e1, e2, e3', e4, e5'] <;>
      refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  · intro t' ht' a b hab hS
    obtain ⟨ht'I, ht'eq⟩ := mem_I₄sub.1 ht'
    have he₂f₁ : mat t' ιe₂ ιe₂ = mat t' ιf₁ ιf₁ := by
      have b1 := torus_bar_mul ht'I ιe₁
      have b2 := torus_bar_mul ht'I ιf₂
      simp only [hypPartner_inl, hypPartner_inr_inr] at b1 b2
      rw [← ht'eq] at b2
      exact mul_left_cancel₀ ((map_ne_zero h.bar).2 (torus_ne_zero ht'I ιe₁)) (b2.trans b1.symm)
    revert a b
    rw [forall_upper (P := fun a b => (a, b) ∉ sI₄ → mat t' a a = mat t' b b)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hS <;>
      first | exact absurd (by decide) hS | exact ht'eq | exact he₂f₁

theorem U_inf_centralizer_I₅ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₅sub h : Set (hypSU h 2 1)) =
      patSub h sI₅ isPattern_sI₅ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 0 (((2 ^ f : ℕ) : ℤ) + 1)
  have e3' : mat t ιz ιz = ((ω ^ (0 : ℤ) : Kˣ) : K) := e3.trans (zpow_val_eq hω 1 (by ring))
  have e4' : mat t ιf₁ ιf₁ = ((ω ^ (0 : ℤ) : Kˣ) : K) := e4.trans (by simp)
  have e5' : mat t ιf₂ ιf₂ = ((ω ^ (-(((2 ^ f : ℕ) : ℤ) + 1)) : Kˣ) : K) :=
    e5.trans (zpow_val_eq hω (-1) (by ring))
  have htI : t ∈ I₅sub h := mem_I₅sub.2 ⟨ht, by rw [e1, e3'], by rw [e3', e4']⟩
  refine U_inf_centralizer_eq (torusEq_le _) isPattern_sI₅ (fun p hp => ⟨t, htI, ?_⟩) ?_
  · simp only [sI₅, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e1, e2, e3', e4', e5'] <;>
      refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  · intro t' ht' a b hab hS
    obtain ⟨ht'I, h1, h2⟩ := mem_I₅sub.1 ht'
    revert a b
    rw [forall_upper (P := fun a b => (a, b) ∉ sI₅ → mat t' a a = mat t' b b)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hS <;>
      first | exact absurd (by decide) hS | exact h1 | exact h2 | exact h1.trans h2

theorem U_inf_centralizer_I₆ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₆sub h : Set (hypSU h 2 1)) =
      patSub h sI₆ isPattern_sI₆ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 1 0
  have htI : t ∈ I₆sub h := mem_I₆sub.2 ⟨ht, by rw [e2, e5]; simp⟩
  refine U_inf_centralizer_eq (torusEq_le _) isPattern_sI₆ (fun p hp => ⟨t, htI, ?_⟩) ?_
  · simp only [sI₆, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e1, e2, e3, e4, e5] <;>
      refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  · intro t' ht' a b hab hS
    obtain ⟨ht'I, ht'eq⟩ := mem_I₆sub.1 ht'
    revert a b
    rw [forall_upper (P := fun a b => (a, b) ∉ sI₆ → mat t' a a = mat t' b b)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hS <;>
      first | exact absurd (by decide) hS | exact ht'eq

theorem U_inf_centralizer_I₃₆ :
    hypUnitriangular h 2 1 ⊓ centralizer ((I₃sub h ⊓ I₆sub h : Subgroup (hypSU h 2 1)) :
      Set (hypSU h 2 1)) = patSub h sI₃₆ isPattern_sI₃₆ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω (((2 ^ f : ℕ) : ℤ) - 1) 0
  have e3' : mat t ιz ιz = ((ω ^ (2 - 2 * ((2 ^ f : ℕ) : ℤ)) : Kˣ) : K) :=
    e3.trans (zpow_val_eq hω 1 (by ring))
  have e4' : mat t ιf₁ ιf₁ = ((ω ^ (((2 ^ f : ℕ) : ℤ) - 1) : Kˣ) : K) :=
    e4.trans (zpow_val_eq hω (-1) (by ring))
  have htI : t ∈ I₃sub h ⊓ I₆sub h :=
    ⟨mem_I₃sub.2 ⟨ht, by rw [e1, e4']⟩, mem_I₆sub.2 ⟨ht, by rw [e2, e5]; simp⟩⟩
  refine U_inf_centralizer_eq (inf_le_left.trans (torusEq_le _)) isPattern_sI₃₆
    (fun p hp => ⟨t, htI, ?_⟩) ?_
  · simp only [sI₃₆, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e1, e2, e3', e4', e5] <;>
      refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  · rintro t' ⟨ht₃, ht₆⟩ a b hab hS
    obtain ⟨ht'I, h3⟩ := mem_I₃sub.1 ht₃
    obtain ⟨-, h6⟩ := mem_I₆sub.1 ht₆
    revert a b
    rw [forall_upper (P := fun a b => (a, b) ∉ sI₃₆ → mat t' a a = mat t' b b)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hS <;>
      first | exact absurd (by decide) hS | exact h3 | exact h6

end Centralizers

theorem torus_conj_mem_patSub {S : Finset (HypIndex 2 1 × HypIndex 2 1)} (hS : IsPattern S)
    {t g : hypSU h 2 1} (ht : t ∈ Isub h) (hg : g ∈ patSub h S hS) :
    t * g * t⁻¹ ∈ patSub h S hS := by
  obtain ⟨hgU, hgS⟩ := hg
  refine ⟨mem_hypUnitriangular.2 ⟨fun a b hab => ?_, fun a => ?_⟩, fun p hp => ?_⟩
  · change mat (t * g * t⁻¹) a b = 0
    rw [torus_conj_apply ht, U_lower hgU hab, mul_zero, zero_mul]
  · change mat (t * g * t⁻¹) a a = 1
    rw [torus_conj_apply ht, U_diag hgU, mul_one, mul_inv_cancel₀ (torus_ne_zero ht a)]
  · rw [torus_conj_apply ht, hgS p hp, mul_zero, zero_mul]

theorem torus_conj_mem_U {t g : hypSU h 2 1} (ht : t ∈ Isub h)
    (hg : g ∈ hypUnitriangular h 2 1) : t * g * t⁻¹ ∈ hypUnitriangular h 2 1 := by
  rw [U_eq_patSub] at hg ⊢
  exact torus_conj_mem_patSub _ ht hg

theorem eq_one_of_U_entries {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
    (h1 : mat g ιe₁ ιe₂ = 0) (h2 : mat g ιe₁ ιz = 0) (h3 : mat g ιe₁ ιf₂ = 0)
    (h4 : mat g ιe₁ ιf₁ = 0) (h5 : mat g ιe₂ ιz = 0) (h6 : mat g ιe₂ ιf₂ = 0)
    (h7 : mat g ιe₂ ιf₁ = 0) (h8 : mat g ιz ιf₂ = 0) (h9 : mat g ιz ιf₁ = 0)
    (h10 : mat g ιf₂ ιf₁ = 0) : g = 1 :=
  eq_of_U_entries hg (one_mem _) (forall_upper.2 (by simp [mat_one, *]))

section MulInv

variable {w y : hypSU h 2 1} (hw : w ∈ hypUnitriangular h 2 1)
  (hy : y ∈ hypUnitriangular h 2 1)
include hw hy

theorem mulInv_entries :
    mat (w * y⁻¹) ιe₁ ιe₂ = mat w ιe₁ ιe₂ + h.bar (mat y ιf₂ ιf₁) ∧
    mat (w * y⁻¹) ιe₁ ιz = mat w ιe₁ ιz + h.bar (mat y ιz ιf₁) +
      mat w ιe₁ ιe₂ * h.bar (mat y ιz ιf₂) ∧
    mat (w * y⁻¹) ιe₂ ιz = mat w ιe₂ ιz + h.bar (mat y ιz ιf₂) ∧
    mat (w * y⁻¹) ιe₁ ιf₂ = mat w ιe₁ ιf₂ + h.bar (mat y ιe₂ ιf₁) +
      mat w ιe₁ ιe₂ * h.bar (mat y ιe₂ ιf₂) + mat w ιe₁ ιz * h.bar (mat y ιe₂ ιz) ∧
    mat (w * y⁻¹) ιe₂ ιf₂ = mat w ιe₂ ιf₂ + h.bar (mat y ιe₂ ιf₂) +
      mat w ιe₂ ιz * h.bar (mat y ιe₂ ιz) ∧
    mat (w * y⁻¹) ιz ιf₂ = mat w ιz ιf₂ + h.bar (mat y ιe₂ ιz) ∧
    mat (w * y⁻¹) ιe₁ ιf₁ = mat w ιe₁ ιf₁ + h.bar (mat y ιe₁ ιf₁) +
      mat w ιe₁ ιe₂ * h.bar (mat y ιe₁ ιf₂) + mat w ιe₁ ιz * h.bar (mat y ιe₁ ιz) +
        mat w ιe₁ ιf₂ * h.bar (mat y ιe₁ ιe₂) ∧
    mat (w * y⁻¹) ιe₂ ιf₁ = mat w ιe₂ ιf₁ + h.bar (mat y ιe₁ ιf₂) +
      mat w ιe₂ ιz * h.bar (mat y ιe₁ ιz) + mat w ιe₂ ιf₂ * h.bar (mat y ιe₁ ιe₂) ∧
    mat (w * y⁻¹) ιz ιf₁ = mat w ιz ιf₁ + h.bar (mat y ιe₁ ιz) +
      mat w ιz ιf₂ * h.bar (mat y ιe₁ ιe₂) ∧
    mat (w * y⁻¹) ιf₂ ιf₁ = mat w ιf₂ ιf₁ + h.bar (mat y ιe₁ ιe₂) := by
  have hi := inv_mem hy
  rw [mul_e₁e₂ hw hi, mul_e₁z hw hi, mul_e₂z hw hi, mul_e₁f₂ hw hi, mul_e₂f₂ hw hi,
    mul_zf₂ hw hi, mul_e₁f₁ hw hi, mul_e₂f₁ hw hi, mul_zf₁ hw hi, mul_f₂f₁ hw hi]
  simp only [mat_inv_apply, hypPartner_inl, hypPartner_inr_inl, hypPartner_inr_inr, and_self]

end MulInv

section PatternMembership

variable {g : hypSU h 2 1}

theorem mem_patSub_sI₁ : g ∈ patSub h sI₁ isPattern_sI₁ ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧ mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 ∧
    mat g ιe₁ ιf₂ = 0 ∧ mat g ιe₂ ιf₁ = 0 ∧ mat g ιe₂ ιf₂ = 0 ∧ mat g ιe₁ ιf₁ = 0 := by
  simp [mem_patSub, sI₁]

theorem mem_patSub_sI₂ : g ∈ patSub h sI₂ isPattern_sI₂ ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧
    mat g ιe₁ ιf₂ = 0 ∧ mat g ιe₂ ιf₁ = 0 ∧ mat g ιe₁ ιf₁ = 0 := by
  simp [mem_patSub, sI₂]

theorem mem_patSub_sI₄ : g ∈ patSub h sI₄ isPattern_sI₄ ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧
    mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 ∧ mat g ιe₂ ιf₂ = 0 ∧ mat g ιe₁ ιf₁ = 0 := by
  simp [mem_patSub, sI₄]

theorem mem_patSub_sI₅ : g ∈ patSub h sI₅ isPattern_sI₅ ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 ∧
    mat g ιe₁ ιf₂ = 0 ∧ mat g ιe₂ ιf₁ = 0 ∧ mat g ιe₂ ιf₂ = 0 := by
  simp [mem_patSub, sI₅]

theorem mem_patSub_sI₆ : g ∈ patSub h sI₆ isPattern_sI₆ ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧
    mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 ∧ mat g ιe₁ ιf₂ = 0 ∧ mat g ιe₂ ιf₁ = 0 ∧
    mat g ιe₁ ιf₁ = 0 := by
  simp [mem_patSub, sI₆]

theorem mem_patSub_sI₃₆ : g ∈ patSub h sI₃₆ isPattern_sI₃₆ ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧
    mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 ∧ mat g ιe₁ ιf₂ = 0 ∧ mat g ιe₂ ιf₁ = 0 := by
  simp [mem_patSub, sI₃₆]

theorem mem_Ssub' : g ∈ Ssub h ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 := by
  rw [Ssub_eq_patSub]
  simp [mem_patSub, sA₃]

theorem mem_Vsub' : g ∈ Vsub h ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧
    mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 := by
  rw [Vsub_eq_patSub]
  simp [mem_patSub, sA₁]

end PatternMembership

section Factorizations

theorem patSub_I₁_le_A₂sub : patSub h sI₁ isPattern_sI₁ ≤ A₂sub h :=
  patSub_mono _ _ (by decide)

theorem patSub_I₅_le_A₂sub_inf_Ssub : patSub h sI₅ isPattern_sI₅ ≤ A₂sub h ⊓ Ssub h :=
  le_inf (patSub_mono _ _ (by decide)) (by rw [Ssub_eq_patSub]; exact patSub_mono _ _ (by decide))

theorem patSub_I₂_le_Ssub : patSub h sI₂ isPattern_sI₂ ≤ Ssub h := by
  rw [Ssub_eq_patSub]; exact patSub_mono _ _ (by decide)

theorem Z₂Psub_eq_sup_I₄ : Z₂Psub h = ZPsub h ⊔ patSub h sI₄ isPattern_sI₄ ∧
    ZPsub h ⊓ patSub h sI₄ isPattern_sI₄ = ⊥ := by
  have := h.charP
  refine ⟨le_antisymm (fun w hw => ?_) (sup_le ZPsub_le_Z₂Psub
    (by rw [Z₂Psub_eq_patSub]; exact patSub_mono _ _ (by decide))), ?_⟩
  · obtain ⟨hwU, w1, w2, w3, w4, w5, w6, w7⟩ := mem_Z₂Psub.1 hw
    obtain ⟨y, hy, hyb⟩ := exists_rootI₄ h (mat w ιe₁ ιf₂)
    obtain ⟨hyU, y1, y2, y3, y4, y5, y6, y7, y8⟩ := mem_patSub_sI₄.1 hy
    obtain ⟨-, -, -, r4, -, -⟩ := U_rel hyU
    obtain ⟨-, -, -, s4, -, -⟩ := U_rel hwU
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩ := mulInv_entries hwU hyU
    have hx : w * y⁻¹ ∈ ZPsub h :=
      mem_ZPsub.2 ⟨mul_mem hwU (inv_mem hyU), by
        simp [x1, x2, x3, x4, x5, x6, x8, x9, x10, w1, w2, w3, w4, w5, w6, w7, y1, y2, y3, y4,
          y5, y6, y7, r4, s4, hyb, h.bar_bar, CharTwo.add_self_eq_zero]⟩
    rw [show w = w * y⁻¹ * y by group]
    exact mul_mem_sup hx hy
  · refine (Subgroup.eq_bot_iff_forall _).2 fun g ⟨hg1, hg2⟩ => ?_
    obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_ZPsub.1 hg1
    obtain ⟨-, -, -, -, -, -, -, -, b8⟩ := mem_patSub_sI₄.1 hg2
    exact eq_one_of_U_entries hgU a1 a3 a7 b8 a5 a9 a8 a6 a4 a2

end Factorizations

section Factorizations2

theorem Vsub_eq_sup_I₆ : Vsub h = Z₂Psub h ⊔ patSub h sI₆ isPattern_sI₆ ∧
    Z₂Psub h ⊓ patSub h sI₆ isPattern_sI₆ = ⊥ := by
  have := h.charP
  refine ⟨le_antisymm (fun w hw => ?_) (sup_le Z₂Psub_le_Vsub
    (by rw [Vsub_eq_patSub]; exact patSub_mono _ _ (by decide))), ?_⟩
  · obtain ⟨hwU, w1, w2, w3, w4, w5, w6⟩ := mem_Vsub'.1 hw
    obtain ⟨-, -, -, -, s5, -⟩ := U_rel hwU
    have hc : h.bar (mat w ιe₂ ιf₂) = mat w ιe₂ ιf₂ :=
      bar_eq_of_add_eq_zero h (by rw [s5, w5, zero_mul])
    obtain ⟨y, hy, hyc⟩ := exists_rootI₆ h hc
    obtain ⟨hyU, y1, y2, y3, y4, y5, y6, y7, y8, y9⟩ := mem_patSub_sI₆.1 hy
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩ := mulInv_entries hwU hyU
    have hx : w * y⁻¹ ∈ Z₂Psub h :=
      mem_Z₂Psub.2 ⟨mul_mem hwU (inv_mem hyU), by
        simp [*, CharTwo.add_self_eq_zero]⟩
    rw [show w = w * y⁻¹ * y by group]
    exact mul_mem_sup hx hy
  · refine (Subgroup.eq_bot_iff_forall _).2 fun g ⟨hg1, hg2⟩ => ?_
    obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7⟩ := mem_Z₂Psub.1 hg1
    obtain ⟨-, -, -, -, -, -, -, b7, b8, b9⟩ := mem_patSub_sI₆.1 hg2
    exact eq_one_of_U_entries hgU a1 a3 b7 b9 a5 a7 b8 a6 a4 a2

theorem Vsub_eq_sup_I₄_I₃₆ : Vsub h = patSub h sI₄ isPattern_sI₄ ⊔ patSub h sI₃₆ isPattern_sI₃₆ ∧
    patSub h sI₄ isPattern_sI₄ ⊓ patSub h sI₃₆ isPattern_sI₃₆ = ⊥ := by
  have := h.charP
  refine ⟨le_antisymm (fun w hw => ?_) (sup_le
    (by rw [Vsub_eq_patSub]; exact patSub_mono _ _ (by decide))
    (by rw [Vsub_eq_patSub]; exact patSub_mono _ _ (by decide))), ?_⟩
  · obtain ⟨hwU, w1, w2, w3, w4, w5, w6⟩ := mem_Vsub'.1 hw
    obtain ⟨-, -, -, s4, -, -⟩ := U_rel hwU
    obtain ⟨y, hy, hyb⟩ := exists_rootI₄ h (mat w ιe₁ ιf₂)
    obtain ⟨hyU, y1, y2, y3, y4, y5, y6, y7, y8⟩ := mem_patSub_sI₄.1 hy
    obtain ⟨-, -, -, r4, -, -⟩ := U_rel hyU
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩ := mulInv_entries hwU hyU
    have hx : w * y⁻¹ ∈ patSub h sI₃₆ isPattern_sI₃₆ :=
      mem_patSub_sI₃₆.2 ⟨mul_mem hwU (inv_mem hyU), by
        simp [*, h.bar_bar, CharTwo.add_self_eq_zero]⟩
    rw [show w = w * y⁻¹ * y by group]
    exact mul_mem (mem_sup_right hx) (mem_sup_left hy)
  · refine (Subgroup.eq_bot_iff_forall _).2 fun g ⟨hg1, hg2⟩ => ?_
    obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7, a8⟩ := mem_patSub_sI₄.1 hg1
    obtain ⟨-, -, -, -, -, -, -, b7, b8⟩ := mem_patSub_sI₃₆.1 hg2
    exact eq_one_of_U_entries hgU a1 a3 b7 a8 a5 a7 b8 a6 a4 a2

theorem A₂sub_eq_sup_I₁ : A₂sub h = (A₂sub h ⊓ Ssub h) ⊔ patSub h sI₁ isPattern_sI₁ ∧
    (A₂sub h ⊓ Ssub h) ⊓ patSub h sI₁ isPattern_sI₁ = ⊥ := by
  have := h.charP
  refine ⟨le_antisymm (fun w hw => ?_) (sup_le inf_le_left patSub_I₁_le_A₂sub), ?_⟩
  · have hwU := A₂sub_le_U hw
    obtain ⟨y, hy, hya⟩ := exists_rootI₁ h (mat w ιe₁ ιe₂)
    obtain ⟨hyU, y1, y2, y3, y4, y5, y6, y7, y8⟩ := mem_patSub_sI₁.1 hy
    obtain ⟨r1, -, -, -, -, -⟩ := U_rel hyU
    obtain ⟨x1, -⟩ := mulInv_entries hwU hyU
    have hx : w * y⁻¹ ∈ A₂sub h ⊓ Ssub h :=
      Subgroup.mem_inf.2 ⟨(A₂sub h).mul_mem hw ((A₂sub h).inv_mem (patSub_I₁_le_A₂sub hy)),
        mem_Ssub'.2 ⟨mul_mem hwU (inv_mem hyU),
        by rw [x1, r1, hya, h.bar_bar, CharTwo.add_self_eq_zero],
        by rw [(U_rel (mul_mem hwU (inv_mem hyU))).1, x1, r1, hya, h.bar_bar,
          CharTwo.add_self_eq_zero, map_zero]⟩⟩
    rw [show w = w * y⁻¹ * y by group]
    exact mul_mem_sup hx hy
  · refine (Subgroup.eq_bot_iff_forall _).2 fun g ⟨⟨hg1, hg2⟩, hg3⟩ => ?_
    obtain ⟨hgU, a1, a2, a3⟩ := mem_A₂sub.1 hg1
    obtain ⟨-, b1, b2⟩ := mem_Ssub'.1 hg2
    obtain ⟨-, c1, c2, c3, c4, c5, c6, c7, c8⟩ := mem_patSub_sI₁.1 hg3
    exact eq_one_of_U_entries hgU b1 c1 c5 c8 a1 a3 c6 a2 c2 b2

theorem Ssub_eq_sup_I₂ : Ssub h = (A₂sub h ⊓ Ssub h) ⊔ patSub h sI₂ isPattern_sI₂ ∧
    (A₂sub h ⊓ Ssub h) ⊓ patSub h sI₂ isPattern_sI₂ = ⊥ := by
  have := h.charP
  refine ⟨le_antisymm (fun w hw => ?_) (sup_le inf_le_right patSub_I₂_le_Ssub), ?_⟩
  · obtain ⟨hwU, w1, w2⟩ := mem_Ssub'.1 hw
    obtain ⟨-, s2, -, -, s5, -⟩ := U_rel hwU
    obtain ⟨y, hy, hyu, hyc⟩ := exists_rootI₂ h s5
    obtain ⟨hyU, y1, y2, y3, y4, y5, y6, y7⟩ := mem_patSub_sI₂.1 hy
    obtain ⟨-, r2, -, -, r5, -⟩ := U_rel hyU
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩ := mulInv_entries hwU hyU
    have hxU := mul_mem hwU (inv_mem hyU)
    have hx : w * y⁻¹ ∈ A₂sub h ⊓ Ssub h :=
      Subgroup.mem_inf.2 ⟨mem_A₂sub.2 ⟨hxU,
        by rw [x3, r2, hyu, h.bar_bar, CharTwo.add_self_eq_zero],
        by rw [x6, s2, hyu, CharTwo.add_self_eq_zero], by
        rw [x5, hyc, hyu]
        linear_combination s5 + CharTwo.add_self_eq_zero (mat w ιe₂ ιz * h.bar (mat w ιe₂ ιz))⟩,
        (Ssub h).mul_mem hw ((Ssub h).inv_mem (patSub_I₂_le_Ssub hy))⟩
    rw [show w = w * y⁻¹ * y by group]
    exact mul_mem_sup hx hy
  · refine (Subgroup.eq_bot_iff_forall _).2 fun g ⟨⟨hg1, hg2⟩, hg3⟩ => ?_
    obtain ⟨hgU, a1, a2, a3⟩ := mem_A₂sub.1 hg1
    obtain ⟨-, c1, c2, c3, c4, c5, c6, c7⟩ := mem_patSub_sI₂.1 hg3
    exact eq_one_of_U_entries hgU c1 c3 c5 c7 a1 a3 c6 a2 c4 c2

end Factorizations2

theorem conj_perm_mem_patSub {w : hypSU h 2 1} {σ : Equiv.Perm (HypIndex 2 1)}
    (hσσ : ∀ a, σ (σ a) = a) (hσ : ∀ a, σ (hypPartner a) = hypPartner (σ a))
    (hw : ∀ a b, mat w a b = if σ a = b then 1 else 0)
    {S S' : Finset (HypIndex 2 1 × HypIndex 2 1)} (hS : IsPattern S) (hS' : IsPattern S')
    (hSS : ∀ a b : HypIndex 2 1, (fullPos b < fullPos a ∨ (a, b) ∈ S') →
      fullPos (σ b) < fullPos (σ a) ∨ (σ a, σ b) ∈ S)
    {g : hypSU h 2 1} (hg : g ∈ patSub h S hS) : w * g * w⁻¹ ∈ patSub h S' hS' := by
  obtain ⟨hgU, hgS⟩ := hg
  have hzero : ∀ a b, (fullPos b < fullPos a ∨ (a, b) ∈ S') → mat (w * g * w⁻¹) a b = 0 := by
    intro a b hab
    rw [conj_perm_apply hσσ hσ hw]
    rcases hSS a b hab with h1 | h1
    · exact U_lower hgU h1
    · exact hgS _ h1
  refine ⟨mem_hypUnitriangular.2 ⟨fun a b hab => hzero a b (Or.inl hab), fun a => ?_⟩,
    fun p hp => hzero p.1 p.2 (Or.inr hp)⟩
  change mat (w * g * w⁻¹) a a = 1
  rw [conj_perm_apply hσσ hσ hw, U_diag hgU]

theorem conj_s_mem_A₂sub {g : hypSU h 2 1} (hg : g ∈ Z₂Psub h) :
    sSU h * g * (sSU h)⁻¹ ∈ A₂sub h := by
  rw [Z₂Psub_eq_patSub] at hg
  exact conj_perm_mem_patSub σs_σs σs_partner mat_sSU isPattern_sZ₂P isPattern_sA₂
    (by decide) hg

theorem conj_s_mem_Z₂Psub {g : hypSU h 2 1} (hg : g ∈ patSub h sI₁ isPattern_sI₁) :
    sSU h * g * (sSU h)⁻¹ ∈ Z₂Psub h := by
  rw [Z₂Psub_eq_patSub]
  exact conj_perm_mem_patSub σs_σs σs_partner mat_sSU isPattern_sI₁ isPattern_sZ₂P
    (by decide) hg

theorem patSub_I₁_le_conj_Z₂Psub :
    patSub h sI₁ isPattern_sI₁ ≤ (Z₂Psub h).map (MulAut.conj (sSU h)).toMonoidHom := by
  intro g hg
  refine ⟨sSU h * g * (sSU h)⁻¹, conj_s_mem_Z₂Psub hg, ?_⟩
  have hs : (sSU h)⁻¹ = sSU h := inv_eq_of_mul_eq_one_right sSU_mul_self
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs]
  rw [← mul_assoc, ← mul_assoc, sSU_mul_self, one_mul, mul_assoc, sSU_mul_self, mul_one]

theorem conj_Z₂Psub_le_A₂sub : (Z₂Psub h).map (MulAut.conj (sSU h)).toMonoidHom ≤ A₂sub h := by
  rintro _ ⟨g, hg, rfl⟩
  exact conj_s_mem_A₂sub hg

section Factorizations3

theorem A₂sub_inf_Ssub_eq_sup : A₂sub h ⊓ Ssub h = Z₂Psub h ⊔ patSub h sI₅ isPattern_sI₅ := by
  have := h.charP
  refine le_antisymm (fun w hw => ?_)
    (sup_le (le_inf Z₂Psub_le_A₂sub (Z₂Psub_le_Vsub.trans Vsub_le_Ssub))
      patSub_I₅_le_A₂sub_inf_Ssub)
  obtain ⟨hwA, hwS⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨hwU, w1, w2, w3⟩ := mem_A₂sub.1 hwA
  obtain ⟨-, w4, w5⟩ := mem_Ssub'.1 hwS
  obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := mat w ιe₁ ιz * h.bar (mat w ιe₁ ιz))
    (by rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨y, hy, hyu, -⟩ := exists_rootI₅ h hc
  obtain ⟨hyU, y1, y2, y3, y4, y5, y6, y7⟩ := mem_patSub_sI₅.1 hy
  obtain ⟨-, -, r3, -, -, -⟩ := U_rel hyU
  obtain ⟨-, x2, x3, -⟩ := mulInv_entries hwU hyU
  have hxA : w * y⁻¹ ∈ A₂sub h :=
    (A₂sub h).mul_mem hwA ((A₂sub h).inv_mem (patSub_I₅_le_A₂sub_inf_Ssub hy).1)
  have hxS : w * y⁻¹ ∈ Ssub h :=
    (Ssub h).mul_mem hwS ((Ssub h).inv_mem (patSub_I₅_le_A₂sub_inf_Ssub hy).2)
  have hxV : w * y⁻¹ ∈ Vsub h := by
    refine (mem_Vsub_iff hxS).2 fun i => ?_
    fin_cases i
    · change mat (w * y⁻¹) ιe₁ ιz = 0
      simp only [x2, r3, y1, y3, hyu, w4, map_zero, zero_mul, add_zero, h.bar_bar,
        CharTwo.add_self_eq_zero]
    · exact (mem_A₂sub.1 hxA).2.1
  rw [show w = w * y⁻¹ * y by group]
  exact mul_mem_sup (Subgroup.mem_inf.2 ⟨hxV, hxA⟩) hy

theorem U_eq_sup_A₂sub_I₂ :
    hypUnitriangular h 2 1 = A₂sub h ⊔ patSub h sI₂ isPattern_sI₂ ∧
      A₂sub h ⊓ patSub h sI₂ isPattern_sI₂ = ⊥ := by
  have := h.charP
  refine ⟨le_antisymm (fun w hwU => ?_) (sup_le A₂sub_le_U (patSub_le_U _ _)), ?_⟩
  · obtain ⟨-, s2, -, -, s5, -⟩ := U_rel hwU
    obtain ⟨y, hy, hyu, hyc⟩ := exists_rootI₂ h s5
    obtain ⟨hyU, -⟩ := mem_patSub_sI₂.1 hy
    obtain ⟨-, r2, -, -, -, -⟩ := U_rel hyU
    obtain ⟨-, -, x3, -, x5, x6, -⟩ := mulInv_entries hwU hyU
    have hx : w * y⁻¹ ∈ A₂sub h :=
      mem_A₂sub.2 ⟨mul_mem hwU (inv_mem hyU),
        by rw [x3, r2, hyu, h.bar_bar, CharTwo.add_self_eq_zero],
        by rw [x6, s2, hyu, CharTwo.add_self_eq_zero], by
          rw [x5, hyc, hyu]
          linear_combination s5 + CharTwo.add_self_eq_zero (mat w ιe₂ ιz * h.bar (mat w ιe₂ ιz))⟩
    rw [show w = w * y⁻¹ * y by group]
    exact mul_mem_sup hx hy
  · refine (Subgroup.eq_bot_iff_forall _).2 fun g ⟨hg1, hg2⟩ => ?_
    obtain ⟨hgU, a1, a2, a3⟩ := mem_A₂sub.1 hg1
    obtain ⟨-, c1, c2, c3, c4, c5, c6, c7⟩ := mem_patSub_sI₂.1 hg2
    exact eq_one_of_U_entries hgU c1 c3 c5 c7 a1 a3 c6 a2 c4 c2

theorem U_eq_sup_Ssub_I₁ :
    hypUnitriangular h 2 1 = Ssub h ⊔ patSub h sI₁ isPattern_sI₁ ∧
      Ssub h ⊓ patSub h sI₁ isPattern_sI₁ = ⊥ := by
  have := h.charP
  refine ⟨le_antisymm (fun w hwU => ?_) (sup_le Ssub_le_Usub (patSub_le_U _ _)), ?_⟩
  · obtain ⟨y, hy, hya⟩ := exists_rootI₁ h (mat w ιe₁ ιe₂)
    obtain ⟨hyU, -⟩ := mem_patSub_sI₁.1 hy
    obtain ⟨r1, -⟩ := U_rel hyU
    obtain ⟨x1, -⟩ := mulInv_entries hwU hyU
    have hxU := mul_mem hwU (inv_mem hyU)
    have e1 : mat (w * y⁻¹) ιe₁ ιe₂ = 0 := by
      rw [x1, r1, hya, h.bar_bar, CharTwo.add_self_eq_zero]
    have hx : w * y⁻¹ ∈ Ssub h :=
      mem_Ssub'.2 ⟨hxU, e1, by rw [(U_rel hxU).1, e1, map_zero]⟩
    rw [show w = w * y⁻¹ * y by group]
    exact mul_mem_sup hx hy
  · refine (Subgroup.eq_bot_iff_forall _).2 fun g ⟨hg1, hg2⟩ => ?_
    obtain ⟨hgU, b1, b2⟩ := mem_Ssub'.1 hg1
    obtain ⟨-, c1, c2, c3, c4, c5, c6, c7, c8⟩ := mem_patSub_sI₁.1 hg2
    exact eq_one_of_U_entries hgU b1 c1 c5 c8 c3 c7 c6 c4 c2 b2

theorem A₂sub_eq_sup_conj : A₂sub h = Z₂Psub h ⊔
    (Z₂Psub h).map (MulAut.conj (sSU h)).toMonoidHom ⊔ patSub h sI₅ isPattern_sI₅ := by
  refine le_antisymm ?_ (sup_le (sup_le Z₂Psub_le_A₂sub conj_Z₂Psub_le_A₂sub)
    (patSub_I₅_le_A₂sub_inf_Ssub.trans inf_le_left))
  rw [A₂sub_eq_sup_I₁.1, A₂sub_inf_Ssub_eq_sup]
  exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    (patSub_I₁_le_conj_Z₂Psub.trans (le_sup_right.trans le_sup_left))

theorem Ssub_eq_sup_Vsub : Ssub h = Vsub h ⊔ patSub h sI₂ isPattern_sI₂ ⊔
    patSub h sI₅ isPattern_sI₅ := by
  refine le_antisymm ?_ (sup_le (sup_le Vsub_le_Ssub patSub_I₂_le_Ssub)
    (patSub_I₅_le_A₂sub_inf_Ssub.trans inf_le_right))
  rw [Ssub_eq_sup_I₂.1, A₂sub_inf_Ssub_eq_sup]
  exact sup_le (sup_le (Z₂Psub_le_Vsub.trans (le_sup_left.trans le_sup_left)) le_sup_right)
    (le_sup_right.trans le_sup_left)

theorem Vsub_sup_A₂sub_inf_Ssub : Vsub h ⊔ (A₂sub h ⊓ Ssub h) =
    Vsub h ⊔ patSub h sI₅ isPattern_sI₅ := by
  rw [A₂sub_inf_Ssub_eq_sup]
  exact le_antisymm (sup_le le_sup_left (sup_le (Z₂Psub_le_Vsub.trans le_sup_left) le_sup_right))
    (sup_le le_sup_left (le_sup_right.trans le_sup_right))

end Factorizations3

section Classes

theorem exists_sq_eq_of_fixed (h : UnitaryFieldData 2 f K) {c : K} (hc : h.bar c = c) :
    ∃ β : K, h.bar β = β ∧ β * β = c := by
  have h1 := h.one_le
  refine ⟨c ^ 2 ^ (f - 1), ?_, ?_⟩
  · rw [map_pow, hc]
  · rw [← sq, ← pow_mul, ← pow_succ, Nat.sub_add_cancel h1, ← h.bar_apply, hc]

theorem eq_of_mem_ZPsub {g g' : hypSU h 2 1} (hg : g ∈ ZPsub h) (hg' : g' ∈ ZPsub h)
    (e : mat g ιe₁ ιf₁ = mat g' ιe₁ ιf₁) : g = g' := by
  obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_ZPsub.1 hg
  obtain ⟨hgU', b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := mem_ZPsub.1 hg'
  exact eq_of_U_entries hgU hgU' (forall_upper.2 (by simp_all))

theorem eq_of_mem_patSub_I₄ {g g' : hypSU h 2 1} (hg : g ∈ patSub h sI₄ isPattern_sI₄)
    (hg' : g' ∈ patSub h sI₄ isPattern_sI₄) (e : mat g ιe₁ ιf₂ = mat g' ιe₁ ιf₂) : g = g' := by
  obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7, a8⟩ := mem_patSub_sI₄.1 hg
  obtain ⟨hgU', b1, b2, b3, b4, b5, b6, b7, b8⟩ := mem_patSub_sI₄.1 hg'
  have r := (U_rel hgU).2.2.2.1
  have r' := (U_rel hgU').2.2.2.1
  exact eq_of_U_entries hgU hgU' (forall_upper.2 (by simp_all))

theorem eq_of_mem_patSub_I₁ {g g' : hypSU h 2 1} (hg : g ∈ patSub h sI₁ isPattern_sI₁)
    (hg' : g' ∈ patSub h sI₁ isPattern_sI₁) (e : mat g ιe₁ ιe₂ = mat g' ιe₁ ιe₂) : g = g' := by
  obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7, a8⟩ := mem_patSub_sI₁.1 hg
  obtain ⟨hgU', b1, b2, b3, b4, b5, b6, b7, b8⟩ := mem_patSub_sI₁.1 hg'
  have r := (U_rel hgU).1
  have r' := (U_rel hgU').1
  exact eq_of_U_entries hgU hgU' (forall_upper.2 (by simp_all))

theorem ZPsub_eq_conj_z₁ (h : UnitaryFieldData 2 f K) :
    (∀ t ∈ I₂sub h, t⁻¹ * z₁SU h * t ∈ ZPsub h ∧ t⁻¹ * z₁SU h * t ≠ 1) ∧
      ∀ z ∈ ZPsub h, z ≠ 1 → ∃ t ∈ I₂sub h, z = t⁻¹ * z₁SU h * t := by
  have := h.charP
  have hz₁ := z₁SU_mem_ZPsub (h := h)
  have hconj : ∀ t ∈ Isub h, t⁻¹ * z₁SU h * t ∈ ZPsub h := fun t ht => by
    have := torus_conj_mem_patSub isPattern_sZP (inv_mem ht) hz₁
    rw [inv_inv] at this
    exact this
  refine ⟨fun t ht => ⟨hconj t (torusEq_le _ ht), fun e => z₁SU_ne_one (h := h) ?_⟩,
    fun z hz hz1 => ?_⟩
  · calc z₁SU h = t * (t⁻¹ * z₁SU h * t) * t⁻¹ := by group
      _ = 1 := by rw [e, mul_one, mul_inv_cancel]
  · obtain ⟨hzU, -, -, a3, -, -, -, a7, -, -⟩ := mem_ZPsub.1 hz
    set c := mat z ιe₁ ιf₁ with hcdef
    have hc : h.bar c = c := by
      obtain ⟨-, -, -, -, -, r6⟩ := U_rel hzU
      obtain ⟨-, a1, -⟩ := mem_ZPsub.1 hz
      rw [a1, a3, a7] at r6
      exact bar_eq_of_add_eq_zero h (by simpa using r6)
    have hc0 : c ≠ 0 := fun h0 => hz1 (eq_of_mem_ZPsub hz (one_mem _) (by
      rw [← hcdef, h0, mat_one, one_apply_ne (by decide)]))
    have hci : h.bar c⁻¹ = c⁻¹ := by rw [map_inv₀, hc]
    obtain ⟨β, hβ, hββ⟩ := exists_sq_eq_of_fixed h hci
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hββ
      exact inv_ne_zero hc0 hββ.symm
    obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus h hβ0 (one_ne_zero (α := K))
    have htI : t ∈ I₂sub h := mem_I₂sub.2 ⟨ht, by rw [e2, e3, hβ]; field_simp; simp, by
      rw [e3, e5, hβ]; field_simp; simp⟩
    refine ⟨t, htI, eq_of_mem_ZPsub hz (hconj t ht) ?_⟩
    rw [show t⁻¹ * z₁SU h * t = t⁻¹ * z₁SU h * t⁻¹⁻¹ by rw [inv_inv],
      torus_conj_apply (inv_mem ht), torus_inv_apply ht, torus_inv_apply ht, inv_inv,
      mat_z₁SU_e₁f₁, e1, e4, hβ, ← hcdef]
    field_simp
    rw [sq, hββ, mul_inv_cancel₀ hc0]

end Classes

section Classes2

theorem z₂SU_mem_patSub_I₄ : z₂SU h ∈ patSub h sI₄ isPattern_sI₄ := by
  rw [mem_patSub_sI₄, z₂SU, mat_vSU]
  refine ⟨mem_U_of_oddUni (mat_vSU _), ?_⟩
  simp [oddUni]

theorem conj_s_z₂SU : sSU h * z₂SU h * (sSU h)⁻¹ ∈ patSub h sI₁ isPattern_sI₁ ∧
    mat (sSU h * z₂SU h * (sSU h)⁻¹) ιe₁ ιe₂ = 1 := by
  refine ⟨conj_perm_mem_patSub σs_σs σs_partner mat_sSU isPattern_sI₄ isPattern_sI₁
    (by decide) z₂SU_mem_patSub_I₄, ?_⟩
  rw [conj_sSU_apply]
  exact mat_z₂SU_e₁f₂

theorem torus_conj_inv_mem_patSub {S : Finset (HypIndex 2 1 × HypIndex 2 1)} (hS : IsPattern S)
    {t g : hypSU h 2 1} (ht : t ∈ Isub h) (hg : g ∈ patSub h S hS) :
    t⁻¹ * g * t ∈ patSub h S hS := by
  have := torus_conj_mem_patSub hS (inv_mem ht) hg
  rwa [inv_inv] at this

theorem torus_conj_inv_apply {t : hypSU h 2 1} (ht : t ∈ Isub h) (g : hypSU h 2 1)
    (a b : HypIndex 2 1) : mat (t⁻¹ * g * t) a b = (mat t a a)⁻¹ * mat g a b * mat t b b := by
  have := torus_conj_apply (inv_mem ht) g a b
  rwa [inv_inv, torus_inv_apply ht, torus_inv_apply ht, inv_inv] at this

theorem closure_conj_z₂SU (hf : 2 ≤ f) :
    closure {x | ∃ t ∈ I₃sub h, x = t⁻¹ * z₂SU h * t} =
      hypUnitriangular h 2 1 ⊓ centralizer (I₄sub h : Set (hypSU h 2 1)) := by
  rw [U_inf_centralizer_I₄ hf]
  refine le_antisymm ((closure_le _).2 ?_) fun y hy => ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact torus_conj_inv_mem_patSub _ (torusEq_le _ ht) z₂SU_mem_patSub_I₄
  · by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    set b := mat y ιe₁ ιf₂ with hbdef
    have hb0 : b ≠ 0 := fun h0 => hy1 (eq_of_mem_patSub_I₄ hy (one_mem _) (by
      rw [← hbdef, h0, mat_one, one_apply_ne (by decide)]))
    have hbb : (h.bar b)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero h.bar).2 hb0)
    obtain ⟨t, ht, e1, -, -, e4, e5⟩ := exists_torus h (one_ne_zero (α := K)) hbb
    have htI : t ∈ I₃sub h := mem_I₃sub.2 ⟨ht, by rw [e1, e4, map_one, inv_one]⟩
    refine subset_closure ⟨t, htI, eq_of_mem_patSub_I₄ hy
      (torus_conj_inv_mem_patSub _ ht z₂SU_mem_patSub_I₄) ?_⟩
    rw [torus_conj_inv_apply ht, e1, e5, mat_z₂SU_e₁f₂, map_inv₀, h.bar_bar, ← hbdef]
    simp

theorem Z₂Psub_eq_sup_closure (hf : 2 ≤ f) :
    Z₂Psub h = ZPsub h ⊔ closure {x | ∃ t ∈ I₃sub h, x = t⁻¹ * z₂SU h * t} := by
  rw [closure_conj_z₂SU hf, U_inf_centralizer_I₄ hf]
  exact Z₂Psub_eq_sup_I₄.1

theorem A₂sub_eq_sup_closure :
    A₂sub h = (A₂sub h ⊓ Ssub h) ⊔ closure {x | ∃ t ∈ I₃sub h ⊔ I₆sub h,
      x = t⁻¹ * (sSU h * z₂SU h * (sSU h)⁻¹) * t} := by
  have hcl : closure {x | ∃ t ∈ I₃sub h ⊔ I₆sub h,
      x = t⁻¹ * (sSU h * z₂SU h * (sSU h)⁻¹) * t} = patSub h sI₁ isPattern_sI₁ := by
    refine le_antisymm ((closure_le _).2 ?_) fun y hy => ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact torus_conj_inv_mem_patSub _ (sup_le (torusEq_le _) (torusEq_le _) ht)
        conj_s_z₂SU.1
    · by_cases hy1 : y = 1
      · rw [hy1]
        exact one_mem _
      set a := mat y ιe₁ ιe₂ with hadef
      have ha0 : a ≠ 0 := fun h0 => hy1 (eq_of_mem_patSub_I₁ hy (one_mem _) (by
        rw [← hadef, h0, mat_one, one_apply_ne (by decide)]))
      obtain ⟨t, ht, e1, e2, -, -, e5⟩ := exists_torus h (inv_ne_zero ha0) (one_ne_zero (α := K))
      have htI : t ∈ I₆sub h := mem_I₆sub.2 ⟨ht, by rw [e2, e5, map_one, inv_one]⟩
      refine subset_closure ⟨t, mem_sup_right htI, eq_of_mem_patSub_I₁ hy
        (torus_conj_inv_mem_patSub _ ht conj_s_z₂SU.1) ?_⟩
      rw [torus_conj_inv_apply ht, e1, e2, conj_s_z₂SU.2, ← hadef]
      simp
  rw [hcl]
  exact A₂sub_eq_sup_I₁.1

end Classes2

section Invariance

variable {w : hypSU h 2 1} {σ : Equiv.Perm (HypIndex 2 1)}

theorem perm_conj_torus (hσσ : ∀ a, σ (σ a) = a) (hσ : ∀ a, σ (hypPartner a) = hypPartner (σ a))
    (hw : ∀ a b, mat w a b = if σ a = b then 1 else 0) {t : hypSU h 2 1} (ht : t ∈ Isub h) :
    w * t * w⁻¹ ∈ Isub h ∧ ∀ a, mat (w * t * w⁻¹) a a = mat t (σ a) (σ a) := by
  refine ⟨CFSG.RankThree.CentralLiftU.mem_hypTorus_of_diag h (q := fun a => mat t (σ a) (σ a))
    ?_, fun a => conj_perm_apply hσσ hσ hw t a a⟩
  ext a b
  change mat (w * t * w⁻¹) a b = _
  rw [conj_perm_apply hσσ hσ hw]
  by_cases hab : a = b
  · rw [hab, diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hab, torus_offdiag ht (fun e => hab (by rw [← hσσ a, e, hσσ]))]

theorem map_conj_torusEq (hσσ : ∀ a, σ (σ a) = a) (hσ : ∀ a, σ (hypPartner a) = hypPartner (σ a))
    (hw : ∀ a b, mat w a b = if σ a = b then 1 else 0) (hww : w * w = 1)
    {S S' : Finset (HypIndex 2 1 × HypIndex 2 1)}
    (hSS' : ∀ p ∈ S', (σ p.1, σ p.2) ∈ S) (hS'S : ∀ p ∈ S, (σ p.1, σ p.2) ∈ S') :
    (torusEq h S).map (MulAut.conj w).toMonoidHom = torusEq h S' := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have key : ∀ {T T' : Finset (HypIndex 2 1 × HypIndex 2 1)},
      (∀ p ∈ T', (σ p.1, σ p.2) ∈ T) → ∀ t ∈ torusEq h T, w * t * w⁻¹ ∈ torusEq h T' := by
    intro T T' hT t ⟨ht, htT⟩
    obtain ⟨hI, he⟩ := perm_conj_torus hσσ hσ hw ht
    exact ⟨hI, fun p hp => by rw [he, he]; exact htT _ (hT p hp)⟩
  refine le_antisymm ?_ fun t ht => ⟨w * t * w⁻¹, key hS'S t ht, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact key hSS' t ht
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwi]
    rw [← mul_assoc, ← mul_assoc, hww, one_mul, mul_assoc, hww, mul_one]

theorem I₄sub_eq_conj : I₄sub h = (I₁sub h).map (MulAut.conj (sSU h)).toMonoidHom :=
  (map_conj_torusEq σs_σs σs_partner mat_sSU sSU_mul_self (by decide) (by decide)).symm

theorem I₅sub_eq_conj : I₅sub h = (I₂sub h).map (MulAut.conj (rSU h)).toMonoidHom :=
  (map_conj_torusEq σr_σr σr_partner mat_rSU rSU_mul_self (by decide) (by decide)).symm

theorem I₆sub_eq_conj : I₆sub h = (I₃sub h).map (MulAut.conj (rSU h)).toMonoidHom :=
  (map_conj_torusEq σr_σr σr_partner mat_rSU rSU_mul_self (by decide) (by decide)).symm

theorem map_conj_sSU_I₃sub : (I₃sub h).map (MulAut.conj (sSU h)).toMonoidHom = I₃sub h :=
  map_conj_torusEq σs_σs σs_partner mat_sSU sSU_mul_self (by decide) (by decide)

theorem Isub_eq_torusEq : Isub h = torusEq h ∅ := by
  ext t
  simp [mem_torusEq]

theorem map_conj_rSU_Isub : (Isub h).map (MulAut.conj (rSU h)).toMonoidHom = Isub h := by
  rw [Isub_eq_torusEq]
  exact map_conj_torusEq σr_σr σr_partner mat_rSU rSU_mul_self (by decide) (by decide)

theorem map_conj_sSU_Isub : (Isub h).map (MulAut.conj (sSU h)).toMonoidHom = Isub h := by
  rw [Isub_eq_torusEq]
  exact map_conj_torusEq σs_σs σs_partner mat_sSU sSU_mul_self (by decide) (by decide)

end Invariance

section TorusLevi

@[expose] def diagSL (c : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem leviSU_diagSL (c : Kˣ) :
    UnitaryHigher.leviSU h 1 (diagSL c) ∈ Isub h ⊓ N₁sub h ∧
      mat (UnitaryHigher.leviSU h 1 (diagSL c)) ιe₁ ιe₁ = c ∧
      mat (UnitaryHigher.leviSU h 1 (diagSL c)) ιe₂ ιe₂ = ((c⁻¹ : Kˣ) : K) := by
  have hd : UnitaryHigher.leviDual h (SpecialLinearGroup.toGL (diagSL c)) =
      !![h.bar ((c⁻¹ : Kˣ) : K), 0; 0, h.bar (c : K)] := by
    have key := UnitaryHigher.bar_map_mul_inv h (SpecialLinearGroup.toGL (diagSL c))
    rw [SpecialLinearGroup.coe_GL_coe_matrix] at key
    set L := UnitaryHigher.leviDual h (SpecialLinearGroup.toGL (diagSL c))
    have e : ∀ i j, (((diagSL c : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * L) i j =
        (1 : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by rw [key]
    have e00 := e 0 0
    have e01 := e 0 1
    have e10 := e 1 0
    have e11 := e 1 1
    simp [diagSL, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j
    · change L 0 0 = h.bar ((c⁻¹ : Kˣ) : K)
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact eq_inv_of_mul_eq_one_right e00
    · exact e01
    · exact e10
    · change L 1 1 = h.bar (c : K)
      have := eq_inv_of_mul_eq_one_right e11
      rwa [inv_inv] at this
  have hm := mat_leviSU (h := h) (diagSL c)
  rw [hd] at hm
  refine ⟨⟨CFSG.RankThree.CentralLiftU.mem_hypTorus_of_diag h
    (q := fun a => mat (UnitaryHigher.leviSU h 1 (diagSL c)) a a) ?_, ⟨diagSL c, rfl⟩⟩, ?_, ?_⟩
  · change mat (UnitaryHigher.leviSU h 1 (diagSL c)) = _
    rw [hm]
    ext a b
    rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
      (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
      simp [diagSL]
  · rw [hm]
    simp [diagSL]
  · rw [hm]
    simp [diagSL]

variable (hf : 2 ≤ f)
include hf

theorem generator_ne_inv {ω : Kˣ} (hω : orderOf ω = (2 ^ f) ^ 2 - 1) :
    (ω : K) ≠ ((ω⁻¹ : Kˣ) : K) := by
  rw [Ne, Units.val_inj]
  intro e
  have h2 : ω ^ 2 = 1 := by rw [sq]; nth_rw 2 [e]; exact mul_inv_cancel ω
  have hle := orderOf_le_of_pow_eq_one (by norm_num) h2
  rw [hω] at hle
  have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : 4 ^ 2 ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left (by simpa using this) 2
  omega

theorem sec2_1_four_N₁ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₁sub h : Set (hypSU h 2 1)) ⊓
      centralizer ((Isub h ⊓ N₁sub h : Subgroup (hypSU h 2 1)) : Set (hypSU h 2 1)) = ⊥ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  obtain ⟨⟨htI, htN⟩, e1, e2⟩ := leviSU_diagSL (h := h) ω
  rw [U_inf_centralizer_I₁ hf]
  refine (Subgroup.eq_bot_iff_forall _).2 fun u ⟨hu, huc⟩ => ?_
  have e := (torus_commute_iff htI u).1 (mem_centralizer_iff.1 huc _ ⟨htI, htN⟩) ιe₁ ιe₂
  rw [e1, e2] at e
  have h0 : mat u ιe₁ ιe₂ = 0 := by
    have : mat u ιe₁ ιe₂ * ((ω : K) - ((ω⁻¹ : Kˣ) : K)) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (generator_ne_inv hf hω))
  exact eq_of_mem_patSub_I₁ hu (one_mem _) (by rw [h0, mat_one, one_apply_ne (by decide)])

end TorusLevi

section TorusLevi2

theorem mem_N₂sub_of_torus {t : hypSU h 2 1} (ht : t ∈ Isub h) (h1 : mat t ιe₁ ιe₁ = 1)
    (h2 : mat t ιf₁ ιf₁ = 1) : t ∈ N₂sub h := by
  rw [mem_N₂sub]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · by_cases ha : a = ιe₁
    · rw [ha, h1, one_apply_eq]
    · rw [torus_offdiag ht ha, one_apply_ne ha]
  · by_cases ha : a = ιf₁
    · rw [ha, h2, one_apply_eq]
    · rw [torus_offdiag ht ha, one_apply_ne ha]

variable (hf : 2 ≤ f)
include hf

theorem sec2_1_four_N₂ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set (hypSU h 2 1)) ⊓
      centralizer ((Isub h ⊓ N₂sub h : Subgroup (hypSU h 2 1)) : Set (hypSU h 2 1)) = ⊥ := by
  have := h.charP
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 0 1
  have htN : t ∈ Isub h ⊓ N₂sub h := ⟨ht, mem_N₂sub_of_torus ht (by rw [e1]; simp)
    (by rw [e4]; simp)⟩
  rw [U_inf_centralizer_I₂ hf]
  refine (Subgroup.eq_bot_iff_forall _).2 fun u ⟨hu, huc⟩ => ?_
  have hc := (torus_commute_iff ht u).1 (mem_centralizer_iff.1 huc _ htN)
  have sep : ∀ a b : HypIndex 2 1, mat t a a ≠ mat t b b → mat u a b = 0 := fun a b hab => by
    have e := hc a b
    have : mat u a b * (mat t a a - mat t b b) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hab)
  have hz : mat u ιe₂ ιz = 0 := sep _ _ (by
    rw [e2, e3]
    refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith)
  have hf₂ : mat u ιe₂ ιf₂ = 0 := sep _ _ (by
    rw [e2, e5]
    refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith)
  obtain ⟨huU, c1, c2, c3, c4, c5, c6, c7⟩ := mem_patSub_sI₂.1 hu
  have hzf₂ : mat u ιz ιf₂ = 0 := by rw [(U_rel huU).2.1, hz, map_zero]
  exact eq_one_of_U_entries huU c1 c3 c5 c7 hz hf₂ c6 hzf₂ c4 c2

theorem sec2_1_four_N₄ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₄sub h : Set (hypSU h 2 1)) ⊓
      centralizer ((Isub h ⊓ N₄sub h : Subgroup (hypSU h 2 1)) : Set (hypSU h 2 1)) = ⊥ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  obtain ⟨⟨htI, htN⟩, e1, e2⟩ := leviSU_diagSL (h := h) ω
  set t := UnitaryHigher.leviSU h 1 (diagSL ω)
  obtain ⟨ht'I, ht'e⟩ := perm_conj_torus σs_σs σs_partner mat_sSU htI
  have ht' : sSU h * t * (sSU h)⁻¹ ∈ Isub h ⊓ N₄sub h := ⟨ht'I, ⟨t, htN, rfl⟩⟩
  rw [U_inf_centralizer_I₄ hf]
  refine (Subgroup.eq_bot_iff_forall _).2 fun u ⟨hu, huc⟩ => ?_
  have e := (torus_commute_iff ht'I u).1 (mem_centralizer_iff.1 huc _ ht') ιe₁ ιf₂
  rw [ht'e, ht'e] at e
  change mat t ιe₁ ιe₁ * _ = _ * mat t ιe₂ ιe₂ at e
  rw [e1, e2] at e
  have h0 : mat u ιe₁ ιf₂ = 0 := by
    have : mat u ιe₁ ιf₂ * ((ω : K) - ((ω⁻¹ : Kˣ) : K)) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (generator_ne_inv hf hω))
  exact eq_of_mem_patSub_I₄ hu (one_mem _) (by rw [h0, mat_one, one_apply_ne (by decide)])

theorem sec2_1_four_N₅ :
    hypUnitriangular h 2 1 ⊓ centralizer (I₅sub h : Set (hypSU h 2 1)) ⊓
      centralizer ((Isub h ⊓ N₅sub h : Subgroup (hypSU h 2 1)) : Set (hypSU h 2 1)) = ⊥ := by
  have := h.charP
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 0 1
  have htN : t ∈ N₂sub h := mem_N₂sub_of_torus ht (by rw [e1]; simp) (by rw [e4]; simp)
  obtain ⟨ht'I, ht'e⟩ := perm_conj_torus σr_σr σr_partner mat_rSU ht
  have ht' : rSU h * t * (rSU h)⁻¹ ∈ Isub h ⊓ N₅sub h := ⟨ht'I, ⟨t, htN, rfl⟩⟩
  rw [U_inf_centralizer_I₅ hf]
  refine (Subgroup.eq_bot_iff_forall _).2 fun u ⟨hu, huc⟩ => ?_
  have hc := (torus_commute_iff ht'I u).1 (mem_centralizer_iff.1 huc _ ht')
  have sep : ∀ a b : HypIndex 2 1, mat (rSU h * t * (rSU h)⁻¹) a a ≠
      mat (rSU h * t * (rSU h)⁻¹) b b → mat u a b = 0 := fun a b hab => by
    have e := hc a b
    have : mat u a b * (mat (rSU h * t * (rSU h)⁻¹) a a - mat (rSU h * t * (rSU h)⁻¹) b b) =
      0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hab)
  have hz : mat u ιe₁ ιz = 0 := sep _ _ (by
    rw [ht'e, ht'e]
    change mat t ιe₂ ιe₂ ≠ mat t ιz ιz
    rw [e2, e3]
    refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith)
  have hf₁ : mat u ιe₁ ιf₁ = 0 := sep _ _ (by
    rw [ht'e, ht'e]
    change mat t ιe₂ ιe₂ ≠ mat t ιf₂ ιf₂
    rw [e2, e5]
    refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith)
  obtain ⟨huU, c1, c2, c3, c4, c5, c6, c7⟩ := mem_patSub_sI₅.1 hu
  have hzf₁ : mat u ιz ιf₁ = 0 := by rw [(U_rel huU).2.2.1, hz, c1]; simp
  exact eq_one_of_U_entries huU c1 hz c5 hf₁ c3 c7 c6 c4 hzf₁ c2

end TorusLevi2

theorem normalizer_U_eq_sup :
    normalizer (hypUnitriangular h 2 1 : Set (hypSU h 2 1)) = hypUnitriangular h 2 1 ⊔ Isub h := by
  rw [UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) le_rfl]
  exact le_antisymm (CFSG.RankThree.CentralLiftU.hypBorel_le_sup le_rfl (by norm_num))
    (sup_le (hypUnitriangular_le_hypBorel h) (hypTorus_le_hypBorel h))

theorem hypScalars_le_torusEq (S : Finset (HypIndex 2 1 × HypIndex 2 1)) :
    hypScalars h 2 1 ≤ torusEq h S := by
  intro z hz
  obtain ⟨c, hc0, hcm⟩ := exists_scalar_of_mem_hypScalars hz
  have hzI : z ∈ Isub h := CFSG.RankThree.CentralLiftU.mem_hypTorus_of_diag h
    (q := fun _ => c) (by
      ext a b
      change mat z a b = _
      rw [hcm, diagonal_apply])
  exact ⟨hzI, fun p _ => by rw [hcm, hcm, ite_eq_left rfl, ite_eq_left rfl]⟩

theorem hypScalars_le_Isub : hypScalars h 2 1 ≤ Isub h := by
  rw [Isub_eq_torusEq]
  exact hypScalars_le_torusEq _

namespace Data

variable {G : Type} [Group G] (d : Data G h)

theorem pull_inf_of_scalars_le {M M' : Subgroup (hypSU h 2 1)} (hM : hypScalars h 2 1 ≤ M) :
    d.pull (M ⊓ M') = d.pull M ⊓ d.pull M' := by
  refine le_antisymm (le_inf (d.pull_mono inf_le_left) (d.pull_mono inf_le_right)) ?_
  rintro _ ⟨⟨m, hm, rfl⟩, ⟨m', hm', e⟩⟩
  have hk : m⁻¹ * m' ∈ hypScalars h 2 1 := by
    rw [← ker_η d, MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
  have hm'M : m' ∈ M := by
    rw [show m' = m * (m⁻¹ * m') by group]
    exact M.mul_mem hm (hM hk)
  exact ⟨m', ⟨hm'M, hm'⟩, e⟩

theorem pull_inf_centralizer {M X : Subgroup (hypSU h 2 1)} (hM : M ≤ hypUnitriangular h 2 1)
    (hX : X ≤ Isub h) :
    d.pull (M ⊓ centralizer (X : Set (hypSU h 2 1))) =
      d.pull M ⊓ centralizer (d.pull X : Set G) := by
  refine le_antisymm (le_inf (d.pull_mono inf_le_left) ?_) ?_
  · rintro _ ⟨u, ⟨-, huc⟩, rfl⟩
    refine mem_centralizer_iff.2 ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 huc t ht]
  · rintro _ ⟨⟨u, hu, rfl⟩, hc⟩
    refine ⟨u, ⟨hu, mem_centralizer_iff.2 fun t ht => ?_⟩, rfl⟩
    have e : d.η t * d.η u = d.η u * d.η t := mem_centralizer_iff.1 hc _ ⟨t, ht, rfl⟩
    have hU := torus_conj_mem_U (hX ht) (hM hu)
    have e' : t * u * t⁻¹ = u := d.η_injOn hU (hM hu) (by
      rw [map_mul, map_mul, map_inv, e, mul_inv_cancel_right])
    calc t * u = t * u * t⁻¹ * t := by group
      _ = u * t := by rw [e']

theorem pull_U_inf_centralizer {X : Subgroup (hypSU h 2 1)} (hX : X ≤ Isub h) :
    d.pull (hypUnitriangular h 2 1 ⊓ centralizer (X : Set (hypSU h 2 1))) =
      d.P ⊓ centralizer (d.pull X : Set G) :=
  d.pull_inf_centralizer le_rfl hX

theorem pull_bot : d.pull ⊥ = ⊥ := Subgroup.map_bot _

end Data

namespace Data

variable {G : Type} [Group G] (d : Data G h)

theorem pull_U_sup_I : d.pull (hypUnitriangular h 2 1 ⊔ Isub h) = d.P ⊔ d.I :=
  Subgroup.map_sup _ _ _

theorem normalizer_P : d.L ⊓ normalizer (d.P : Set G) = d.P ⊔ d.I := by
  have := finite_hypPSU (hK := h)
  refine le_antisymm ?_ (le_inf (sup_le d.P_le_L (d.pull_le_L _)) ?_)
  · rintro x ⟨hxL, hxN⟩
    set x' := d.e ⟨x, hxL⟩ with hx'
    have hx'N : x' ∈ normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) := by
      refine mem_normalizer_of_conj_le fun k hk => ?_
      obtain ⟨u, hu, rfl⟩ := hk
      obtain ⟨u', hu', e⟩ := (mem_normalizer_iff.1 hxN (d.η u)).1 ⟨u, hu, rfl⟩
      refine ⟨u', hu', d.e.symm.injective (Subtype.ext ?_)⟩
      have : ((d.e.symm (x' * hypProj h 2 1 u * x'⁻¹) : d.L) : G) = x * d.η u * x⁻¹ := by
        rw [map_mul, map_mul, map_inv, hx', MulEquiv.symm_apply_apply]
        rfl
      rw [this, ← e]
      rfl
    rw [UnitaryHigher.normalizer_hypProjUnitriangular h (by norm_num) le_rfl] at hx'N
    obtain ⟨b, hb, hbx⟩ := hx'N
    have hbx' : x = d.η b := by
      rw [η_apply, hbx, hx', MulEquiv.symm_apply_apply]
    rw [hbx', ← d.pull_U_sup_I]
    refine ⟨b, ?_, rfl⟩
    rw [← normalizer_U_eq_sup, UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) le_rfl]
    exact hb
  · rw [← d.pull_U_sup_I, ← normalizer_U_eq_sup]
    exact Subgroup.le_normalizer_map _

end Data

theorem sec2_1_two_model (hf : 2 ≤ f) :
    ZPsub h = hypUnitriangular h 2 1 ⊓ centralizer (I₃sub h : Set (hypSU h 2 1)) ∧
    (Z₂Psub h = ZPsub h ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₄sub h : Set _)) ∧
      ZPsub h ⊓ (hypUnitriangular h 2 1 ⊓ centralizer (I₄sub h : Set _)) = ⊥) ∧
    (Vsub h = Z₂Psub h ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₆sub h : Set _)) ∧
      Z₂Psub h ⊓ (hypUnitriangular h 2 1 ⊓ centralizer (I₆sub h : Set _)) = ⊥) ∧
    (Vsub h = (hypUnitriangular h 2 1 ⊓ centralizer (I₄sub h : Set _)) ⊔
        (hypUnitriangular h 2 1 ⊓ centralizer ((I₃sub h ⊓ I₆sub h : Subgroup _) : Set _)) ∧
      (hypUnitriangular h 2 1 ⊓ centralizer (I₄sub h : Set _)) ⊓
        (hypUnitriangular h 2 1 ⊓ centralizer ((I₃sub h ⊓ I₆sub h : Subgroup _) : Set _)) = ⊥) ∧
    (A₂sub h = (A₂sub h ⊓ Ssub h) ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₁sub h : Set _)) ∧
      (A₂sub h ⊓ Ssub h) ⊓ (hypUnitriangular h 2 1 ⊓ centralizer (I₁sub h : Set _)) = ⊥) ∧
    A₂sub h = Z₂Psub h ⊔ (Z₂Psub h).map (MulAut.conj (sSU h)).toMonoidHom ⊔
      (hypUnitriangular h 2 1 ⊓ centralizer (I₅sub h : Set _)) ∧
    (Ssub h = (A₂sub h ⊓ Ssub h) ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set _)) ∧
      (A₂sub h ⊓ Ssub h) ⊓ (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set _)) = ⊥) ∧
    Ssub h = Vsub h ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set _)) ⊔
      (hypUnitriangular h 2 1 ⊓ centralizer (I₅sub h : Set _)) ∧
    A₂sub h ⊓ Ssub h = Z₂Psub h ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₅sub h : Set _)) ∧
    Vsub h ⊔ (A₂sub h ⊓ Ssub h) =
      Vsub h ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₅sub h : Set _)) ∧
    (hypUnitriangular h 2 1 = A₂sub h ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set _)) ∧
      A₂sub h ⊓ (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set _)) = ⊥) ∧
    (hypUnitriangular h 2 1 = Ssub h ⊔ (hypUnitriangular h 2 1 ⊓ centralizer (I₁sub h : Set _)) ∧
      Ssub h ⊓ (hypUnitriangular h 2 1 ⊓ centralizer (I₁sub h : Set _)) = ⊥) := by
  rw [U_inf_centralizer_I₁ hf, U_inf_centralizer_I₂ hf, U_inf_centralizer_I₃ hf,
    U_inf_centralizer_I₄ hf, U_inf_centralizer_I₅ hf, U_inf_centralizer_I₆ hf,
    U_inf_centralizer_I₃₆ hf]
  exact ⟨rfl, Z₂Psub_eq_sup_I₄, Vsub_eq_sup_I₆, Vsub_eq_sup_I₄_I₃₆, A₂sub_eq_sup_I₁,
    A₂sub_eq_sup_conj, Ssub_eq_sup_I₂, Ssub_eq_sup_Vsub, A₂sub_inf_Ssub_eq_sup,
    Vsub_sup_A₂sub_inf_Ssub, U_eq_sup_A₂sub_I₂, U_eq_sup_Ssub_I₁⟩

namespace Data

variable {G : Type} [Group G] (d : Data G h)

theorem I₃_inf_I₆ : d.I₃ ⊓ d.I₆ = d.pull (I₃sub h ⊓ I₆sub h) :=
  (d.pull_inf_of_scalars_le (hypScalars_le_torusEq _)).symm

theorem sec2_1_two (hf : 2 ≤ f) :
    d.Zp = d.P ⊓ centralizer (d.I₃ : Set G) ∧
    (d.Z₂p = d.Zp ⊔ (d.P ⊓ centralizer (d.I₄ : Set G)) ∧
      d.Zp ⊓ (d.P ⊓ centralizer (d.I₄ : Set G)) = ⊥) ∧
    (d.A₁ = d.Z₂p ⊔ (d.P ⊓ centralizer (d.I₆ : Set G)) ∧
      d.Z₂p ⊓ (d.P ⊓ centralizer (d.I₆ : Set G)) = ⊥) ∧
    (d.A₁ = (d.P ⊓ centralizer (d.I₄ : Set G)) ⊔
        (d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) ∧
      (d.P ⊓ centralizer (d.I₄ : Set G)) ⊓
        (d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = ⊥) ∧
    (d.A₂ = (d.A₂ ⊓ d.A₃) ⊔ (d.P ⊓ centralizer (d.I₁ : Set G)) ∧
      (d.A₂ ⊓ d.A₃) ⊓ (d.P ⊓ centralizer (d.I₁ : Set G)) = ⊥) ∧
    d.A₂ = d.Z₂p ⊔ d.Z₂p.map (MulAut.conj d.s).toMonoidHom ⊔
      (d.P ⊓ centralizer (d.I₅ : Set G)) ∧
    (d.A₃ = (d.A₂ ⊓ d.A₃) ⊔ (d.P ⊓ centralizer (d.I₂ : Set G)) ∧
      (d.A₂ ⊓ d.A₃) ⊓ (d.P ⊓ centralizer (d.I₂ : Set G)) = ⊥) ∧
    d.A₃ = d.A₁ ⊔ (d.P ⊓ centralizer (d.I₂ : Set G)) ⊔ (d.P ⊓ centralizer (d.I₅ : Set G)) ∧
    d.A₂ ⊓ d.A₃ = d.Z₂p ⊔ (d.P ⊓ centralizer (d.I₅ : Set G)) ∧
    d.A₁ ⊔ (d.A₂ ⊓ d.A₃) = d.A₁ ⊔ (d.P ⊓ centralizer (d.I₅ : Set G)) ∧
    (d.P = d.A₂ ⊔ (d.P ⊓ centralizer (d.I₂ : Set G)) ∧
      d.A₂ ⊓ (d.P ⊓ centralizer (d.I₂ : Set G)) = ⊥) ∧
    (d.P = d.A₃ ⊔ (d.P ⊓ centralizer (d.I₁ : Set G)) ∧
      d.A₃ ⊓ (d.P ⊓ centralizer (d.I₁ : Set G)) = ⊥) := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12⟩ := sec2_1_two_model (h := h) hf
  have hU : ∀ X : Subgroup (hypSU h 2 1),
      hypUnitriangular h 2 1 ⊓ centralizer (X : Set (hypSU h 2 1)) ≤ hypUnitriangular h 2 1 :=
    fun X => inf_le_left
  have c1 : d.P ⊓ centralizer (d.I₁ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₁sub h : Set _)) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  have c2 : d.P ⊓ centralizer (d.I₂ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set _)) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  have c3 : d.P ⊓ centralizer (d.I₃ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₃sub h : Set _)) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  have c4 : d.P ⊓ centralizer (d.I₄ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₄sub h : Set _)) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  have c5 : d.P ⊓ centralizer (d.I₅ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₅sub h : Set _)) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  have c6 : d.P ⊓ centralizer (d.I₆ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₆sub h : Set _)) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  have c36 : d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓
        centralizer ((I₃sub h ⊓ I₆sub h : Subgroup (hypSU h 2 1)) : Set _)) := by
    rw [d.I₃_inf_I₆]
    exact (d.pull_U_inf_centralizer (inf_le_left.trans (torusEq_le _))).symm
  have hA₂₃ : d.A₂ ⊓ d.A₃ = d.pull (A₂sub h ⊓ Ssub h) := (d.pull_inf A₂sub_le_U Ssub_le_Usub).symm
  have hZ₂s : d.Z₂p.map (MulAut.conj d.s).toMonoidHom =
      d.pull ((Z₂Psub h).map (MulAut.conj (sSU h)).toMonoidHom) := (d.pull_conj _ _).symm
  rw [c1, c2, c3, c4, c5, c6, c36, hA₂₃, hZ₂s]
  have e : ∀ {M M' : Subgroup (hypSU h 2 1)}, M = M' → d.pull M = d.pull M' := fun e => by rw [e]
  have hb : ∀ {M M' : Subgroup (hypSU h 2 1)}, M ≤ hypUnitriangular h 2 1 →
      M' ≤ hypUnitriangular h 2 1 → M ⊓ M' = ⊥ → d.pull M ⊓ d.pull M' = ⊥ :=
    fun hM hM' e => by rw [← d.pull_inf hM hM', e, pull_bot]
  have hs : ∀ M M' : Subgroup (hypSU h 2 1), d.pull (M ⊔ M') = d.pull M ⊔ d.pull M' :=
    fun M M' => Subgroup.map_sup _ _ _
  refine ⟨e m1, ⟨(e m2.1).trans (hs _ _), hb ZPsub_le_U (hU _) m2.2⟩,
    ⟨(e m3.1).trans (hs _ _), hb (Z₂Psub_le_A₂sub.trans A₂sub_le_U) (hU _) m3.2⟩,
    ⟨(e m4.1).trans (hs _ _), hb (hU _) (hU _) m4.2⟩,
    ⟨(e m5.1).trans (hs _ _), hb (inf_le_left.trans A₂sub_le_U) (hU _) m5.2⟩,
    (e m6).trans (by rw [hs, hs]; rfl),
    ⟨(e m7.1).trans (hs _ _), hb (inf_le_left.trans A₂sub_le_U) (hU _) m7.2⟩,
    (e m8).trans (by rw [hs, hs]; rfl), (e m9).trans (hs _ _),
    by
      change d.pull (Vsub h) ⊔ _ = d.pull (Vsub h) ⊔ _
      rw [← hs, ← hs, m10],
    ⟨(e m11.1).trans (hs _ _), hb A₂sub_le_U (hU _) m11.2⟩,
    ⟨(e m12.1).trans (hs _ _), hb Ssub_le_Usub (hU _) m12.2⟩⟩

end Data

namespace Data

variable {G : Type} [Group G] (d : Data G h)

theorem image_conj (X : Subgroup (hypSU h 2 1)) (x : hypSU h 2 1) :
    d.η '' {y | ∃ t ∈ X, y = t⁻¹ * x * t} = {y | ∃ t ∈ d.pull X, y = t⁻¹ * d.η x * t} := by
  ext y
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨d.η t, ⟨t, ht, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t⁻¹ * x * t, ⟨t, ht, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

theorem sec2_1_three (hf : 2 ≤ f) :
    (∀ t ∈ d.I₂, t⁻¹ * d.z₁ * t ∈ d.Zp ∧ t⁻¹ * d.z₁ * t ≠ 1) ∧
    (∀ z ∈ d.Zp, z ≠ 1 → ∃ t ∈ d.I₂, z = t⁻¹ * d.z₁ * t) ∧
    d.Z₂p = d.Zp ⊔ closure {x | ∃ t ∈ d.I₃, x = t⁻¹ * d.z₂ * t} ∧
    d.A₂ = (d.A₂ ⊓ d.A₃) ⊔ closure {x | ∃ t ∈ d.I₃ ⊔ d.I₆, x = t⁻¹ * (d.s * d.z₂ * d.s⁻¹) * t} := by
  obtain ⟨hz1, hz2⟩ := ZPsub_eq_conj_z₁ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨hmem, hne⟩ := hz1 t ht
    have e : (d.η t)⁻¹ * d.z₁ * d.η t = d.η (t⁻¹ * z₁SU h * t) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    refine ⟨e ▸ ⟨_, hmem, rfl⟩, fun h1 => hne ?_⟩
    rw [e] at h1
    exact d.η_injOn (ZPsub_le_U hmem) (one_mem _) (by rw [h1, map_one])
  · rintro _ ⟨z, hz, rfl⟩ hz1'
    have hz1 : z ≠ 1 := fun e => hz1' (by rw [e, map_one])
    obtain ⟨t, ht, rfl⟩ := hz2 z hz hz1
    exact ⟨d.η t, ⟨t, ht, rfl⟩, by rw [map_mul, map_mul, map_inv]; rfl⟩
  · change d.pull (Z₂Psub h) = d.pull (ZPsub h) ⊔ _
    rw [Z₂Psub_eq_sup_closure hf, pull, Subgroup.map_sup, MonoidHom.map_closure, image_conj]
    rfl
  · change d.pull (A₂sub h) = _
    rw [A₂sub_eq_sup_closure, pull, Subgroup.map_sup, MonoidHom.map_closure, image_conj,
      ← pull, d.pull_inf A₂sub_le_U Ssub_le_Usub]
    have e1 : d.pull (I₃sub h ⊔ I₆sub h) = d.I₃ ⊔ d.I₆ := Subgroup.map_sup _ _ _
    have e2 : d.η (sSU h * z₂SU h * (sSU h)⁻¹) = d.s * d.z₂ * d.s⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [e1, e2]
    rfl

theorem sec2_1_four (hf : 2 ≤ f) :
    d.P ⊓ centralizer (d.I₁ : Set G) ⊓ centralizer ((d.I ⊓ d.N₁ : Subgroup G) : Set G) = ⊥ ∧
    d.P ⊓ centralizer (d.I₂ : Set G) ⊓ centralizer ((d.I ⊓ d.N₂ : Subgroup G) : Set G) = ⊥ ∧
    d.P ⊓ centralizer (d.I₄ : Set G) ⊓ centralizer ((d.I ⊓ d.N₄ : Subgroup G) : Set G) = ⊥ ∧
    d.P ⊓ centralizer (d.I₅ : Set G) ⊓ centralizer ((d.I ⊓ d.N₅ : Subgroup G) : Set G) = ⊥ := by
  have key : ∀ {X N : Subgroup (hypSU h 2 1)}, X ≤ Isub h →
      hypUnitriangular h 2 1 ⊓ centralizer (X : Set _) ⊓
        centralizer ((Isub h ⊓ N : Subgroup _) : Set _) = ⊥ →
      d.P ⊓ centralizer (d.pull X : Set G) ⊓
        centralizer ((d.I ⊓ d.pull N : Subgroup G) : Set G) = ⊥ := by
    intro X N hX e
    rw [← d.pull_U_inf_centralizer hX, Data.I,
      ← d.pull_inf_of_scalars_le (M := Isub h) hypScalars_le_Isub,
      ← d.pull_inf_centralizer inf_le_left inf_le_left, e, pull_bot]
  exact ⟨key (torusEq_le _) (sec2_1_four_N₁ hf), key (torusEq_le _) (sec2_1_four_N₂ hf),
    key (torusEq_le _) (sec2_1_four_N₄ hf), key (torusEq_le _) (sec2_1_four_N₅ hf)⟩

theorem sec2_1_five :
    d.I.map (MulAut.conj d.r).toMonoidHom = d.I ∧ d.I.map (MulAut.conj d.s).toMonoidHom = d.I ∧
    d.I₃.map (MulAut.conj d.s).toMonoidHom = d.I₃ ∧
    d.I₄ = d.I₁.map (MulAut.conj d.s).toMonoidHom ∧
    d.I₅ = d.I₂.map (MulAut.conj d.r).toMonoidHom ∧
    d.I₆ = d.I₃.map (MulAut.conj d.r).toMonoidHom := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Data.I, Data.r, ← d.pull_conj, map_conj_rSU_Isub]
  · rw [Data.I, Data.s, ← d.pull_conj, map_conj_sSU_Isub]
  · rw [Data.I₃, Data.s, ← d.pull_conj, map_conj_sSU_I₃sub]
  · rw [Data.I₄, Data.I₁, Data.s, ← d.pull_conj, I₄sub_eq_conj]
  · rw [Data.I₅, Data.I₂, Data.r, ← d.pull_conj, I₅sub_eq_conj]
  · rw [Data.I₆, Data.I₃, Data.r, ← d.pull_conj, I₆sub_eq_conj]

end Data

end CFSG.LocalAnalysis.EvenBN.U5
