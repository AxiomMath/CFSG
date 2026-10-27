module

public import CFSG.LieType.SpecialLinear.PairedTensor.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open scoped Kronecker

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ} {σ : F ≃+* F}

theorem exists_parameter_line_of_mixed_quadratic
    (A : Subgroup (GL (Fin n) F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : A ≠ ⊥)
    (hq : ∀ a ∈ A, ∀ b ∈ A,
      ((a : Matrix (Fin n) (Fin n) F) ⊗ₖ (a : Matrix (Fin n) (Fin n) F).map σ - 1) *
      ((b : Matrix (Fin n) (Fin n) F) ⊗ₖ (b : Matrix (Fin n) (Fin n) F).map σ - 1) = 0) :
    ∃ X : Matrix (Fin n) (Fin n) F, X ≠ 0 ∧ X * X = 0 ∧
      ∀ a ∈ A, ∃ c : F, σ c = c ∧ (a : Matrix (Fin n) (Fin n) F) = 1 + c • X := by
  classical
  have hn : Nonempty (Fin n) := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    by_contra h
    have : IsEmpty (Fin n) := not_nonempty_iff.mp h
    exact ha1 (Subsingleton.elim a 1)
  have := hn
  obtain ⟨a₀, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ha₀A : (a₀ : GL (Fin n) F) ∈ A := a₀.2
  set aM : Matrix (Fin n) (Fin n) F := ((a₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with haM
  set X : Matrix (Fin n) (Fin n) F := aM - 1 with hXdef
  have ha₀2m : aM * aM = 1 := by
    have h := hA2 (a₀ : GL (Fin n) F) ha₀A
    rw [haM]
    simpa using congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F)) h
  have hXne : X ≠ 0 := by
    intro h
    apply ha₀1
    apply Subtype.ext
    apply Units.ext
    have h' : aM = 1 := sub_eq_zero.mp (by rw [← hXdef]; exact h)
    rw [← haM]
    exact h'
  have hXsq : X * X = 0 := by
    rw [hXdef]
    exact sub_one_mul_sub_one_eq_zero_of_mul_self aM ha₀2m
  have hXa : aM = 1 + X := by
    rw [hXdef, CharTwo.sub_eq_add, add_comm (1 : Matrix (Fin n) (Fin n) F) (aM + 1),
      add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have ha_nonscalar : ¬ ∃ c : F, aM = c • 1 := by
    rintro ⟨c, hc⟩
    apply ha₀1
    apply Subtype.ext
    apply Units.ext
    have h1 : aM = 1 := eq_one_of_eq_smul_one_of_mul_self aM ha₀2m ⟨c, hc⟩
    rw [← haM]
    exact h1
  have hrel_of : ∀ b : ↥A,
      (aM ⊗ₖ aM.map σ) + 1 =
        ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ⊗ₖ
            (((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) +
          ((aM * ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) ⊗ₖ
            (aM.map σ * (((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ))) := by
    intro b
    set bM : Matrix (Fin n) (Fin n) F := ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hbM
    have h := hq (a₀ : GL (Fin n) F) ha₀A (b : GL (Fin n) F) b.2
    rw [← haM, ← hbM] at h
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h
    have hmul : (aM ⊗ₖ aM.map σ) * (bM ⊗ₖ bM.map σ) =
        (aM * bM) ⊗ₖ (aM.map σ * bM.map σ) := by
      rw [Matrix.mul_kronecker_mul]
    have h' : ((aM ⊗ₖ aM.map σ) + 1) +
        ((bM ⊗ₖ bM.map σ) + ((aM * bM) ⊗ₖ (aM.map σ * bM.map σ))) = 0 := by
      rw [add_mul, mul_add, mul_add, mul_one, one_mul, hmul] at h
      rw [← h]
      simp only [mul_one]
      abel
    rw [hbM] at h' ⊢
    exact CharTwo.add_eq_zero.mp h'
  let N : Submodule F (Matrix (Fin n) (Fin n) F) :=
    Submodule.span F ({1, aM} : Set (Matrix (Fin n) (Fin n) F))
  have hmem_span : ∀ b : ↥A, ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∈ N := by
    intro b
    set bM : Matrix (Fin n) (Fin n) F := ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hbM
    by_contra hbN
    obtain ⟨ψ, hψb, hψN⟩ := Submodule.exists_le_ker_of_notMem (K := F)
      (V := Matrix (Fin n) (Fin n) F) (by simpa [hbM] using hbN)
    have hψ1 : ψ (1 : Matrix (Fin n) (Fin n) F) = 0 :=
      hψN (Submodule.subset_span (by simp))
    have hψa : ψ aM = 0 := hψN (Submodule.subset_span (by simp))
    have hψb' : ψ bM ≠ 0 := by simpa [hbM] using hψb
    have hrel := hrel_of b
    rw [← hbM] at hrel
    have hentry : ∀ k l : Fin n,
        (ψ bM) * (bM.map σ k l) +
          (ψ (aM * bM)) * ((aM.map σ * bM.map σ) k l) = 0 := by
      intro k l
      let L : Matrix (Fin n) (Fin n) F :=
        (aM.map σ k l) • aM + (if k = l then (1 : F) else 0) • (1 : Matrix (Fin n) (Fin n) F)
      let R : Matrix (Fin n) (Fin n) F :=
        (bM.map σ k l) • bM + ((aM.map σ * bM.map σ) k l) • (aM * bM)
      have hLR : L = R := by
        ext i j
        have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) F =>
          M (i, k) (j, l)) hrel
        simp only [Matrix.add_apply, Matrix.kronecker_apply, Matrix.map_apply,
          Matrix.one_apply, Matrix.smul_apply, L, R] at h ⊢
        by_cases hij : i = j
        · subst hij
          by_cases hkl : k = l
          · subst hkl
            simp only [if_true] at h ⊢
            try ring_nf at h ⊢
            linear_combination h
          · simp only [Prod.mk.injEq, hkl, true_and, if_false] at h ⊢
            try ring_nf at h ⊢
            linear_combination h
        · by_cases hkl : k = l
          · subst hkl
            simp only [Prod.mk.injEq, hij, and_true, if_false, if_true] at h ⊢
            try ring_nf at h ⊢
            linear_combination h
          · simp only [Prod.mk.injEq, hij, hkl, false_and, if_false] at h ⊢
            try ring_nf at h ⊢
            linear_combination h
      have hψLR : ψ L = ψ R := by rw [hLR]
      have hLval : ψ L = (aM.map σ k l) * ψ aM +
          (if k = l then (1 : F) else 0) * ψ (1 : Matrix (Fin n) (Fin n) F) := by
        by_cases hkl : k = l <;> simp [L, hkl, map_add, map_smul, smul_eq_mul]
      have hRval : ψ R = (bM.map σ k l) * ψ bM +
          ((aM.map σ * bM.map σ) k l) * ψ (aM * bM) := by
        simp [R, map_add, map_smul, smul_eq_mul]
      have h := hψLR
      rw [hLval, hRval, hψ1, hψa] at h
      simpa [mul_comm, add_comm] using h.symm
    let lam : F := -(ψ (aM * bM)) / ψ bM
    have hσb : bM.map σ = lam • (aM.map σ * bM.map σ) := by
      ext k l
      set y : F := (aM.map σ * bM.map σ) k l with hy
      have h := hentry k l
      have hleft : bM.map σ k l * ψ bM = -(ψ (aM * bM) * y) := by
        calc bM.map σ k l * ψ bM = ψ bM * bM.map σ k l := by ring
          _ = -(ψ (aM * bM) * y) := by
              rw [hy]
              linear_combination h
      have hlam : lam * ψ bM = -ψ (aM * bM) := by
        dsimp [lam]
        field_simp [hψb']
      have hright : (lam * y) * ψ bM = -(ψ (aM * bM) * y) := by
        calc (lam * y) * ψ bM = y * (lam * ψ bM) := by ring
          _ = y * (-ψ (aM * bM)) := by rw [hlam]
          _ = -(ψ (aM * bM) * y) := by ring
      have h' : bM.map σ k l = lam * y :=
        mul_right_cancel₀ hψb' (hleft.trans hright.symm)
      simpa [Matrix.smul_apply, smul_eq_mul] using h'
    set binvM : Matrix (Fin n) (Fin n) F :=
      (((b⁻¹ : ↥A) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hbinvM
    have hb_inv : bM.map σ * binvM.map σ = 1 := by
      have h := Matrix.GeneralLinearGroup.coe_map_mul_map_inv
        (f := (σ : F →+* F)) (b : GL (Fin n) F)
      simpa [hbM, hbinvM] using h
    have hone : (1 : Matrix (Fin n) (Fin n) F) = lam • aM.map σ := by
      calc (1 : Matrix (Fin n) (Fin n) F) = bM.map σ * binvM.map σ := hb_inv.symm
        _ = (lam • (aM.map σ * bM.map σ)) * binvM.map σ := by
              conv_lhs => rw [hσb]
        _ = lam • (aM.map σ * (bM.map σ * binvM.map σ)) := by
              rw [Matrix.smul_mul, mul_assoc]
        _ = lam • (aM.map σ * 1) := by rw [hb_inv]
        _ = lam • aM.map σ := by rw [mul_one]
    have hlamne : lam ≠ 0 := by
      intro hlam
      have h10 : (1 : Matrix (Fin n) (Fin n) F) = 0 := by
        rw [hone, hlam, zero_smul]
      exact one_ne_zero h10
    have haσ : aM.map σ = lam⁻¹ • (1 : Matrix (Fin n) (Fin n) F) := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => lam⁻¹ • M) hone
      simpa [smul_smul, inv_mul_cancel₀ hlamne] using h.symm
    have ha_scalar : ∃ c : F, aM = c • 1 := by
      refine ⟨σ.symm lam⁻¹, ?_⟩
      ext i j
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) haσ
      simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul] at h ⊢
      by_cases hij : i = j
      · simp [hij] at h ⊢
        simpa using congrArg σ.symm h
      · simp [hij] at h ⊢
        simpa using congrArg σ.symm h
    exact ha_nonscalar ha_scalar
  refine ⟨X, hXne, hXsq, ?_⟩
  intro b hb
  set bM : Matrix (Fin n) (Fin n) F := ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hbM
  have hbmem : bM ∈ N := hmem_span ⟨b, hb⟩
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp hbmem
  have hb2m : bM * bM = 1 := by
    have h := hA2 b hb
    rw [hbM]
    simpa using congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F)) h
  have hcalc : (x • (1 : Matrix (Fin n) (Fin n) F) + y • aM) *
      (x • (1 : Matrix (Fin n) (Fin n) F) + y • aM) =
      ((x + y) * (x + y)) • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [add_mul, mul_add, mul_add]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, ha₀2m]
    have hcross : (y * x) • aM + (x * y) • aM = 0 := by
      rw [← add_smul, mul_comm y x, CharTwo.add_self_eq_zero, zero_smul]
    have hsq' : (x + y) * (x + y) = x * x + y * y := by
      rw [mul_add, add_mul, add_mul, mul_comm y x]
      linear_combination CharTwo.add_self_eq_zero (x * y)
    calc (x * x) • (1 : Matrix (Fin n) (Fin n) F) + (y * x) • aM +
          ((x * y) • aM + (y * y) • (1 : Matrix (Fin n) (Fin n) F))
        = ((x * x) • (1 : Matrix (Fin n) (Fin n) F) + (y * y) • (1 : Matrix (Fin n) (Fin n) F)) +
            ((y * x) • aM + (x * y) • aM) := by abel
      _ = ((x * x + y * y) • (1 : Matrix (Fin n) (Fin n) F)) + 0 := by
            rw [hcross, ← add_smul]
      _ = ((x * x + y * y) • (1 : Matrix (Fin n) (Fin n) F)) := by rw [add_zero]
      _ = ((x + y) * (x + y)) • (1 : Matrix (Fin n) (Fin n) F) := by rw [hsq']
  have hxy1 : x + y = 1 := by
    have h1 : ((x + y) * (x + y)) • (1 : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← hcalc, hxy, hb2m]
    let i : Fin n := Classical.choice hn
    have hsq : (x + y) * (x + y) = 1 := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i i) h1
      simpa [Matrix.smul_apply, Matrix.one_apply] using h
    have h : (x + y - 1) * (x + y - 1) = 0 := by
      rw [CharTwo.sub_eq_add]
      have h' : (x + y + 1) * (x + y + 1) =
          ((x + y) * (x + y) + 1) + ((x + y) + (x + y)) := by ring
      rw [h', hsq]
      simp [CharTwo.add_self_eq_zero]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
  have hbX : bM = 1 + y • X := by
    rw [← hxy, hXa]
    rw [smul_add, ← add_assoc, ← add_smul, hxy1, one_smul]
  have habX : aM * bM = 1 + (1 + y) • X := by
    rw [hXa, hbX, mul_add, mul_one, add_mul, one_mul]
    rw [Matrix.mul_smul, hXsq, smul_zero, add_zero]
    rw [add_smul, one_smul]
    abel
  have hcy : σ y = y := by
    have haσ : aM.map σ = 1 + X.map σ := by
      rw [hXa, Matrix.map_add σ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ)]
    have hbσ : bM.map σ = 1 + (σ y) • X.map σ := by
      rw [hbX, Matrix.map_add σ (map_add σ),
        Matrix.map_one σ (map_zero σ) (map_one σ),
        Matrix.map_smul' σ y X (map_mul σ)]
    have hXentry : ∃ i j : Fin n, X i j ≠ 0 := by
      by_contra h
      apply hXne
      ext i j
      exact not_not.mp (not_exists.mp (not_exists.mp h i) j)
    have hXmap_ne : X.map σ ≠ 0 := by
      intro h
      apply hXne
      exact Matrix.map_injective σ.injective (by simpa using h)
    have hXmap_entry : ∃ k l : Fin n, (X.map σ) k l ≠ 0 := by
      by_contra h
      apply hXmap_ne
      ext k l
      exact not_not.mp (not_exists.mp (not_exists.mp h k) l)
    obtain ⟨i, hi⟩ := hXentry
    obtain ⟨j, hij⟩ := hi
    obtain ⟨k, hk⟩ := hXmap_entry
    obtain ⟨l, hkl⟩ := hk
    have hprod : X i j * (X.map σ) k l ≠ 0 := mul_ne_zero hij hkl
    have hXmap_sq : X.map σ * X.map σ = 0 := by
      rw [← Matrix.map_mul, hXsq, Matrix.map_zero σ (map_zero σ)]
    have hprodσ : (1 + X.map σ) * (1 + (σ y) • X.map σ) =
        1 + (1 + σ y) • X.map σ := by
      rw [mul_add, mul_one, add_mul, one_mul]
      rw [Matrix.mul_smul, hXmap_sq, smul_zero, add_zero]
      rw [add_smul, one_smul]
      abel
    have hmain : (y + σ y) * (X i j * (X.map σ) k l) = 0 := by
      have hrel := hrel_of ⟨b, hb⟩
      rw [← hbM] at hrel
      have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) F =>
        M (i, k) (j, l)) hrel
      rw [haσ, hbσ, habX, hXa, hbX, hprodσ] at h
      simp only [Matrix.add_apply, Matrix.kronecker_apply, Matrix.one_apply,
        Matrix.smul_apply, Matrix.map_apply, Prod.mk.injEq] at h ⊢
      by_cases h_ij : i = j
      · subst h_ij
        by_cases h_kl : k = l
        · subst h_kl
          simp only [true_and, if_true] at h ⊢
          simp only [smul_eq_mul] at h ⊢
          ring_nf at h
          try rw [CharTwo.two_eq_zero] at h
          try rw [CharTwo.two_eq_zero]
          simp only [mul_zero, add_zero, zero_add] at h ⊢
          try ring_nf at h ⊢
          first | linear_combination h | linear_combination -h
        · simp only [h_kl, true_and, if_false] at h ⊢
          simp only [zero_add, smul_eq_mul] at h ⊢
          ring_nf at h
          try rw [CharTwo.two_eq_zero] at h
          try rw [CharTwo.two_eq_zero]
          simp only [mul_zero, add_zero] at h ⊢
          try ring_nf at h ⊢
          first | linear_combination h | linear_combination -h
      · by_cases h_kl : k = l
        · subst h_kl
          simp only [h_ij, and_true, if_false, if_true] at h ⊢
          simp only [zero_add, smul_eq_mul] at h ⊢
          ring_nf at h
          try rw [CharTwo.two_eq_zero] at h
          try rw [CharTwo.two_eq_zero]
          simp only [mul_zero, add_zero] at h ⊢
          try ring_nf at h ⊢
          first | linear_combination h | linear_combination -h
        · simp only [h_ij, h_kl, false_and, if_false] at h ⊢
          simp only [zero_add, smul_eq_mul] at h ⊢
          ring_nf at h
          try rw [CharTwo.two_eq_zero] at h
          try rw [CharTwo.two_eq_zero]
          simp only [mul_zero, add_zero] at h ⊢
          try ring_nf at h ⊢
          first | linear_combination h | linear_combination -h
    have hyσ : y + σ y = 0 := by
      rcases mul_eq_zero.mp hmain with h | h
      · exact h
      · exact absurd h hprod
    have h : y = σ y := CharTwo.add_eq_zero.mp hyσ
    exact h.symm
  rw [hbM]
  exact ⟨y, hcy, hbX⟩

theorem nat_card_le_fixed_field_of_mixed_quadratic [Finite F]
    (A : Subgroup (GL (Fin n) F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : A ≠ ⊥)
    (hq : ∀ a ∈ A, ∀ b ∈ A,
      ((a : Matrix (Fin n) (Fin n) F) ⊗ₖ (a : Matrix (Fin n) (Fin n) F).map σ - 1) *
      ((b : Matrix (Fin n) (Fin n) F) ⊗ₖ (b : Matrix (Fin n) (Fin n) F).map σ - 1) = 0) :
    Nat.card A ≤ Nat.card {c : F // σ c = c} := by
  classical
  obtain ⟨X, hXne, hXsq, hline⟩ :=
    exists_parameter_line_of_mixed_quadratic A hA2 hA hq
  let f : ↥A → {c : F // σ c = c} := fun a =>
    ⟨(hline (a : GL (Fin n) F) a.2).choose, (hline (a : GL (Fin n) F) a.2).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hc : (hline (a : GL (Fin n) F) a.2).choose =
        (hline (b : GL (Fin n) F) b.2).choose := congrArg Subtype.val hab
    have ha := (hline (a : GL (Fin n) F) a.2).choose_spec.2
    have hb := (hline (b : GL (Fin n) F) b.2).choose_spec.2
    have hm : ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [ha, hc, ← hb]
    exact Subtype.ext (Units.ext hm)
  exact Nat.card_le_card_of_injective f hf

theorem nat_card_le_fixed_field_of_mixed_quadratic' [Finite F]
    (A : Subgroup (GL (Fin n) F))
    (hA2 : ∀ a ∈ A, a * a = 1)
    (hq : ∀ a ∈ A, ∀ b ∈ A,
      ((a : Matrix (Fin n) (Fin n) F) ⊗ₖ (a : Matrix (Fin n) (Fin n) F).map σ - 1) *
      ((b : Matrix (Fin n) (Fin n) F) ⊗ₖ (b : Matrix (Fin n) (Fin n) F).map σ - 1) = 0) :
    Nat.card A ≤ Nat.card {c : F // σ c = c} := by
  by_cases hA : A = ⊥
  · subst hA
    have hpos : 0 < Nat.card {c : F // σ c = c} := by
      rw [Finite.card_pos_iff]
      exact ⟨⟨0, map_zero σ⟩⟩
    have hbot : Nat.card (⊥ : Subgroup (GL (Fin n) F)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, ⟨1⟩⟩
    rw [hbot]
    exact Nat.succ_le_of_lt hpos
  · exact nat_card_le_fixed_field_of_mixed_quadratic A hA2 hA hq

end CFSG.LieType.SpecialLinear
