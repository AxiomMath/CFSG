module

public import CFSG.LieType.D4Small.Dichotomy
public import CFSG.LieType.D4Small.NormalForm
public import CFSG.LieType.D4Small.OneOrbit
public import CFSG.LieType.D4Small.Orbits
public import CFSG.LieType.D4Small.RootRelations
public import CFSG.LieType.D4Small.SmallClasses
public import CFSG.LieType.D4Small.Strings
public import CFSG.LieType.D4Small.Transport
public import CFSG.LieType.D4Small.WeightClass
public import CFSG.LieType.D4Small.Weights
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

public section

namespace CFSG.LieType.D4Small.D4Datum

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2] (D : D4Datum G K)
  {X : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X] (ρ : Representation K G X)

@[expose] def IsWtClass (N : ℕ) (j : ℕ) (C : Finset (Fin 4 → ZMod N)) : Prop :=
  (∀ a, a ∈ C ↔ IsVWt ((2 : ZMod N) ^ j) a) ∨
    ∃ (b : ZMod N) (e : ℕ), 2 * b = 2 ^ j ∧ e < 2 ∧
      ∀ a, a ∈ C ↔ IsSWt b a ∧ negCount b a % 2 = e

private theorem isUnit_two_zmod {N : ℕ} (hN : Odd N) : IsUnit (2 : ZMod N) := by
  have h2 : ((2 : ℕ) : ZMod N) = 2 := by norm_num
  rw [← h2, ZMod.isUnit_iff_coprime]
  exact Nat.coprime_two_left.mpr hN

private theorem neZero_natCard_units {K : Type*} [Field K] [Finite K] :
    NeZero (Nat.card Kˣ) :=
  ⟨Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩⟩

namespace IsWtClass

theorem isSmallClass {N : ℕ} {j : ℕ} {C : Finset (Fin 4 → ZMod N)}
    (hN3 : 3 ≤ N) (hN : Odd N) [NeZero N] (h : IsWtClass N j C) :
    IsSmallClass N ((2 : ZMod N) ^ j) C := by
  have h2 : IsUnit (2 : ZMod N) := isUnit_two_zmod hN
  rcases h with hV | ⟨b, e, hb, he, hS⟩
  · have hC : C = Finset.univ.filter fun a => IsVWt ((2 : ZMod N) ^ j) a := by
      ext a
      simpa using hV a
    rw [hC]
    exact isSmallClass_vWt hN3 hN (h2.pow j) (Or.inl rfl)
  · have hb2 : IsUnit b :=
      isUnit_of_mul_isUnit_right (x := (2 : ZMod N)) (y := b) (by rw [hb]; exact h2.pow j)
    have hC : C = Finset.univ.filter fun a => IsSWt b a ∧ negCount b a % 2 = e := by
      ext a
      simpa using hS a
    rw [hC]
    exact isSmallClass_sWt hN3 hN hb2 (Or.inl hb.symm) he

private theorem two_pow_eq_one_or_neg_one (j : ℕ) :
    (2 : ZMod 3) ^ j = 1 ∨ (2 : ZMod 3) ^ j = -1 := by
  have h : (2 : ZMod 3) = -1 := by decide
  rw [h]
  exact neg_one_pow_eq_or (ZMod 3) j

private theorem isVWt_pm_one_iff {N : ℕ} {u v : ZMod N} {a : Fin 4 → ZMod N}
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) : IsVWt u a ↔ IsVWt v a := by
  obtain rfl | rfl := hu <;> obtain rfl | rfl := hv
  · exact Iff.rfl
  · exact (isVWt_neg_iff (b := 1)).symm
  · exact isVWt_neg_iff (b := 1)
  · exact Iff.rfl

private theorem isSWt_neg_parity_iff {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0) (e : ℕ)
    (a : Fin 4 → ZMod N) :
    (IsSWt (-b) a ∧ negCount (-b) a % 2 = e) ↔
      (IsSWt b a ∧ negCount b a % 2 = e) := by
  have h4 : ∀ n : ℕ, n ≤ 4 → (4 - n) % 2 = n % 2 := by
    intro n hn
    omega
  have hle : ∀ {c : ZMod N} {x : Fin 4 → ZMod N}, negCount c x ≤ 4 := by
    intro c x
    rw [negCount]
    simpa using Finset.card_le_univ (Finset.univ.filter fun i => x i = -c)
  constructor
  · rintro ⟨hS, he⟩
    have hSb : IsSWt b a := isSWt_neg_iff.mp hS
    rw [negCount_neg hN hb hSb, h4 _ (hle (c := b))] at he
    exact ⟨hSb, he⟩
  · rintro ⟨hS, he⟩
    have hS' : IsSWt (-b) a := isSWt_neg_iff.mpr hS
    rw [negCount_neg hN hb hS, h4 _ (hle (c := b))]
    exact ⟨hS', he⟩

theorem of_three {N : ℕ} {j : ℕ} {C : Finset (Fin 4 → ZMod N)}
    (hN : N = 3) (h : IsWtClass N j C) (j' : ℕ) : IsWtClass N j' C := by
  subst hN
  rcases h with hV | ⟨b, e, hb, he, hS⟩
  · left
    intro a
    rw [hV a]
    exact isVWt_pm_one_iff (two_pow_eq_one_or_neg_one j) (two_pow_eq_one_or_neg_one j')
  · right
    have hunit : IsUnit ((2 : ZMod 3) ^ j) := (isUnit_two_zmod ⟨1, by norm_num⟩).pow j
    have hbunit : IsUnit b :=
      isUnit_of_mul_isUnit_right (x := (2 : ZMod 3)) (y := b) (by rw [hb]; exact hunit)
    have hb0 : b ≠ 0 := hbunit.ne_zero
    obtain h1 | h1 := two_pow_eq_one_or_neg_one j
    · obtain h2 | h2 := two_pow_eq_one_or_neg_one j'
      · exact ⟨b, e, by rw [hb, h1, h2], he, hS⟩
      · refine ⟨-b, e, by simp [mul_neg, hb, h1, h2], he, fun a => ?_⟩
        rw [isSWt_neg_parity_iff ⟨1, by norm_num⟩ hb0 e a, hS a]
    · obtain h2 | h2 := two_pow_eq_one_or_neg_one j'
      · refine ⟨-b, e, by simp [mul_neg, hb, h1, h2], he, fun a => ?_⟩
        rw [isSWt_neg_parity_iff ⟨1, by norm_num⟩ hb0 e a, hS a]
      · exact ⟨b, e, by rw [hb, h1, h2], he, hS⟩

end IsWtClass

private theorem natCast_pow_two {N j : ℕ} :
    ((2 ^ j : ℕ) : ZMod N) = (2 : ZMod N) ^ j := by
  rw [Nat.cast_pow]
  norm_num

private theorem rootOp_two_pow_mem_wtSpace {α : Fin 4 → ℤ} (hα : IsD4Root α) (j : ℕ)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} {x : X} (hx : x ∈ D.wtSpace ρ a) :
    rootOp D ρ α (2 ^ j) x ∈
      D.wtSpace ρ (a + (2 : ZMod (Nat.card Kˣ)) ^ j • castW (Nat.card Kˣ) α) := by
  have h := rootOp_mem_wtSpace D ρ α hα a hx (2 ^ j)
  rwa [natCast_pow_two] at h

private theorem card_eq_four_or_eight_le {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) : Nat.card K = 4 ∨ 8 ≤ Nat.card K := by
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hf2 : 2 ≤ (f : ℕ) := by
    have h4 : 2 ^ 2 ≤ 2 ^ (f : ℕ) := by rw [← hcard']; exact hK
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  rcases Nat.eq_or_lt_of_le hf2 with hf | hf
  · left
    rw [hcard', ← hf]
    norm_num
  · right
    rw [hcard']
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 3 ≤ (f : ℕ))

theorem exists_rootForm (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) (hdim : Module.finrank K X ≤ 16) :
    ∃ j : ℕ, 2 ^ j < Nat.card Kˣ ∧ IsWtClass (Nat.card Kˣ) j (wts D ρ) ∧
      IsRootForm D ρ (fun α => rootOp D ρ α (2 ^ j)) j := by
  haveI : NeZero (Nat.card Kˣ) := neZero_natCard_units
  have hN3 : 3 ≤ Nat.card Kˣ := three_le_natCard_units hK
  have hNodd : Odd (Nat.card Kˣ) := odd_natCard_units K
  have hCw : ∀ a, a ∈ wts D ρ ↔ D.wtSpace ρ a ≠ ⊥ := fun a => mem_wts D ρ (a := a)
  obtain ⟨l, hl, hWt⟩ : ∃ l, 2 ^ l < Nat.card Kˣ ∧ IsWtClass (Nat.card Kˣ) l (wts D ρ) := by
    rcases wts_classification D ρ hK hirr hnt hdim with ⟨l, hl, h⟩ | ⟨b, l, e, hl, hb, he, h⟩
    · exact ⟨l, hl, Or.inl h⟩
    · exact ⟨l, hl, Or.inr ⟨b, e, hb, he, h⟩⟩
  rcases card_eq_four_or_eight_le hK with h4 | h8
  · have hN : Nat.card Kˣ = 3 := card_units_eq_three h4
    have hC : IsSmallClass (Nat.card Kˣ) 1 (wts D ρ) := by
      have h := IsWtClass.isSmallClass hN3 hNodd (IsWtClass.of_three hN hWt 0)
      simpa using h
    have hform : ∀ α, IsD4Root α → ∀ c : K,
        ρ (D.x α c) = 1 + c • rootOp D ρ α 1 + c ^ 2 • rootOp D ρ α 2 :=
      fun α hα c => rho_x_eq_of_card_eq_four (C := wts D ρ) h4 hCw hC hα c
    have h12 : ∀ α, IsD4Root α → rootOp D ρ α 1 * rootOp D ρ α 2 = 0 :=
      fun α hα => rootOp_one_mul_two (C := wts D ρ) h4 hCw hC hα
    have h21 : ∀ α, IsD4Root α → rootOp D ρ α 2 * rootOp D ρ α 1 = 0 :=
      fun α hα => rootOp_two_mul_one (C := wts D ρ) h4 hCw hC hα
    rcases rootOp_two_eq_zero_or_rootOp_one_eq_zero (C := wts D ρ) hN hCw hC hform h12 h21 hirr
      with h2 | h1
    · refine ⟨0, by rw [hN]; norm_num, IsWtClass.of_three hN hWt 0, ?_⟩
      intro α hα c
      have h := hform α hα c
      rw [h2 α hα] at h
      simpa using h
    · refine ⟨1, by rw [hN]; norm_num, IsWtClass.of_three hN hWt 1, ?_⟩
      intro α hα c
      have h := hform α hα c
      rw [h1 α hα] at h
      simpa using h
  · exact ⟨l, hl, hWt, fun α hα c =>
      rho_x_eq_of_eight_le (C := wts D ρ) h8 hCw hl
        (IsWtClass.isSmallClass hN3 hNodd hWt) hα c⟩

theorem exists_isNormalForm (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) (hdim : Module.finrank K X ≤ 16) :
    ∃ (j : ℕ) (C : Finset (Fin 4 → ZMod (Nat.card Kˣ)))
      (b : (Fin 4 → ZMod (Nat.card Kˣ)) → X),
      2 ^ j < Nat.card Kˣ ∧ IsWtClass (Nat.card Kˣ) j C ∧ IsNormalForm D ρ C j b := by
  haveI : NeZero (Nat.card Kˣ) := neZero_natCard_units
  have hCw : ∀ a, a ∈ wts D ρ ↔ D.wtSpace ρ a ≠ ⊥ := fun a => mem_wts D ρ (a := a)
  obtain ⟨j, hl, hWt, hform⟩ := exists_rootForm D ρ hK hirr hnt hdim
  have hC : IsSmallClass (Nat.card Kˣ) ((2 : ZMod (Nat.card Kˣ)) ^ j) (wts D ρ) :=
    IsWtClass.isSmallClass (three_le_natCard_units hK) (odd_natCard_units K) hWt
  obtain ⟨T, hmem, hspan, hact⟩ := exists_normalForm (C := wts D ρ)
    (σ := (2 : ZMod (Nat.card Kˣ)) ^ j) (E := fun α => rootOp D ρ α (2 ^ j)) (j := j)
    hK hCw hC hform (fun α hα _ _ hx => rootOp_two_pow_mem_wtSpace D ρ hα j hx) hirr
  refine ⟨j, wts D ρ, T, hl, hWt, hmem, hspan, ?_⟩
  intro α hα c a ha
  rw [hform α hα c]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [hact a ha α hα]
  by_cases hc : a + (2 : ZMod (Nat.card Kˣ)) ^ j • castW (Nat.card Kˣ) α ∈ wts D ρ
  · simp [hc]
  · simp [hc]

theorem finrank_eq_eight_and_rootForm (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) (hdim : Module.finrank K X ≤ 16) :
    Module.finrank K X = 8 ∧ ∃ j : ℕ, 2 ^ j < Nat.card Kˣ ∧
      IsRootForm D ρ (fun α => rootOp D ρ α (2 ^ j)) j ∧
      ∀ α, IsD4Root α → Module.finrank K (LinearMap.range (rootOp D ρ α (2 ^ j))) = 2 := by
  haveI : NeZero (Nat.card Kˣ) := neZero_natCard_units
  have hCw : ∀ a, a ∈ wts D ρ ↔ D.wtSpace ρ a ≠ ⊥ := fun a => mem_wts D ρ (a := a)
  obtain ⟨j, hl, hWt, hform⟩ := exists_rootForm D ρ hK hirr hnt hdim
  have hC : IsSmallClass (Nat.card Kˣ) ((2 : ZMod (Nat.card Kˣ)) ^ j) (wts D ρ) :=
    IsWtClass.isSmallClass (three_le_natCard_units hK) (odd_natCard_units K) hWt
  obtain ⟨hfin, -, hrange⟩ := finrank_eq_eight_and_finrank_range (C := wts D ρ)
    (σ := (2 : ZMod (Nat.card Kˣ)) ^ j) (E := fun α => rootOp D ρ α (2 ^ j)) (j := j)
    hK hCw hC hform (fun α hα _ _ hx => rootOp_two_pow_mem_wtSpace D ρ hα j hx) hirr
  exact ⟨hfin, j, hl, hform, fun α hα => hrange α hα⟩

include D in
theorem exists_eq_smul_of_commute (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) (hdim : Module.finrank K X ≤ 16) {T : Module.End K X}
    (hT : ∀ g, T * ρ g = ρ g * T) : ∃ c : K, T = c • 1 := by
  haveI : NeZero (Nat.card Kˣ) := neZero_natCard_units
  obtain ⟨j, C, b, _, hWt, hnf⟩ := exists_isNormalForm D ρ hK hirr hnt hdim
  have hC : IsSmallClass (Nat.card Kˣ) ((2 : ZMod (Nat.card Kˣ)) ^ j) C :=
    IsWtClass.isSmallClass (three_le_natCard_units hK) (odd_natCard_units K) hWt
  exact hnf.exists_eq_smul hC hT

end CFSG.LieType.D4Small.D4Datum

end
