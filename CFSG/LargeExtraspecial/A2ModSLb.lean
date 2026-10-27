module

public import CFSG.LargeExtraspecial.A2ModSL
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Matrix Module

variable {n : ℕ}

theorem zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact .inl rfl
  · exact .inr rfl

theorem zmodTwo_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 :=
  (zmodTwo_eq_zero_or_one x).resolve_left h

theorem exists_apply_eq_one_of_ne_zero {v : Fin n → ZMod 2} (hv : v ≠ 0) : ∃ i, v i = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact ⟨i, zmodTwo_eq_one_of_ne_zero hi⟩

theorem tv_mul_self (v φ : Fin n → ZMod 2) : tv v φ * tv v φ = 1 := by
  by_cases h : φ ⬝ᵥ v = 0
  · rw [tv_mul_tv_left h h, ZModModule.add_self, tv_zero_right]
  · rw [tv_of_dotProduct_ne_zero h, mul_one]

theorem tv_inv_eq_self (v φ : Fin n → ZMod 2) : (tv v φ)⁻¹ = tv v φ :=
  inv_eq_of_mul_eq_one_right (tv_mul_self v φ)

theorem tv_mul_tv_mul_cancel (v φ : Fin n → ZMod 2) (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    tv v φ * (tv v φ * g) = g := by
  rw [← mul_assoc, tv_mul_self, one_mul]

section Field

variable {F : Type*} [Field F]

theorem tv_eq_one_iff {v φ : Fin n → F} (h : φ ⬝ᵥ v = 0) : tv v φ = 1 ↔ v = 0 ∨ φ = 0 := by
  constructor
  · intro h1
    have h2 := congrArg (fun g : SpecialLinearGroup (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h1
    simp only [coe_tv h, SpecialLinearGroup.coe_one, add_eq_left] at h2
    exact vecMulVec_eq_zero.mp h2
  · rintro (rfl | rfl)
    · exact tv_zero_left φ
    · exact tv_zero_right v

theorem tv_ne_one {v φ : Fin n → F} (hv : v ≠ 0) (hφ : φ ≠ 0) (h : φ ⬝ᵥ v = 0) : tv v φ ≠ 1 :=
  fun h1 => ((tv_eq_one_iff h).mp h1).elim hv hφ

theorem tv_right_injective {v φ ψ : Fin n → F} (hv : v ≠ 0) (h : φ ⬝ᵥ v = 0) (h' : ψ ⬝ᵥ v = 0)
    (he : tv v φ = tv v ψ) : φ = ψ := by
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) he
  simp only [coe_tv h, coe_tv h', add_right_inj] at h2
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  funext k
  have := congrFun (congrFun h2 i) k
  simp only [vecMulVec_apply] at this
  exact mul_left_cancel₀ hi this

theorem tv_left_injective {v w φ : Fin n → F} (hφ : φ ≠ 0) (h : φ ⬝ᵥ v = 0) (h' : φ ⬝ᵥ w = 0)
    (he : tv v φ = tv w φ) : v = w := by
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) he
  simp only [coe_tv h, coe_tv h', add_right_inj] at h2
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hφ
  funext k
  have := congrFun (congrFun h2 k) j
  simp only [vecMulVec_apply] at this
  exact mul_right_cancel₀ hj this

end Field

theorem tv_eq_tv_iff {v φ w ψ : Fin n → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (h : φ ⬝ᵥ v = 0)
    (h' : ψ ⬝ᵥ w = 0) : tv v φ = tv w ψ ↔ v = w ∧ φ = ψ := by
  refine ⟨fun he => ?_, fun ⟨hvw, hφψ⟩ => hvw ▸ hφψ ▸ rfl⟩
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin n) (ZMod 2) =>
    (g : Matrix (Fin n) (Fin n) (ZMod 2))) he
  simp only [coe_tv h, coe_tv h', add_right_inj] at h2
  obtain ⟨i, hi⟩ := exists_apply_eq_one_of_ne_zero hv
  obtain ⟨j, hj⟩ := exists_apply_eq_one_of_ne_zero hφ
  have hij := congrFun (congrFun h2 i) j
  simp only [vecMulVec_apply, hi, hj, one_mul] at hij
  have hprod : w i * ψ j ≠ 0 := hij ▸ one_ne_zero
  have hwi : w i = 1 := zmodTwo_eq_one_of_ne_zero (left_ne_zero_of_mul hprod)
  have hψj : ψ j = 1 := zmodTwo_eq_one_of_ne_zero (right_ne_zero_of_mul hprod)
  refine ⟨funext fun k => ?_, funext fun k => ?_⟩
  · have := congrFun (congrFun h2 k) j
    simpa [vecMulVec_apply, hj, hψj] using this
  · have := congrFun (congrFun h2 i) k
    simpa [vecMulVec_apply, hi, hwi] using this

theorem mem_ker_mulVecLin_of_iff {k : ℕ} (u : Fin k → Fin n → ZMod 2) (ψ : Fin n → ZMod 2) :
    ψ ∈ LinearMap.ker (Matrix.of u).mulVecLin ↔ ∀ i, ψ ⬝ᵥ u i = 0 := by
  rw [LinearMap.mem_ker, mulVecLin_apply, funext_iff]
  refine forall_congr' fun i => ?_
  rw [Pi.zero_apply, dotProduct_comm]
  rfl

theorem card_annihilator {k : ℕ} (u : Fin k → Fin n → ZMod 2) :
    Nat.card {ψ : Fin n → ZMod 2 // ∀ i, ψ ⬝ᵥ u i = 0} = 2 ^ (n - (Matrix.of u).rank) := by
  set f := (Matrix.of u).mulVecLin
  have e : {ψ : Fin n → ZMod 2 // ∀ i, ψ ⬝ᵥ u i = 0} ≃ LinearMap.ker f :=
    Equiv.subtypeEquivRight fun ψ => (mem_ker_mulVecLin_of_iff u ψ).symm
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at h
  have hr : (Matrix.of u).rank = finrank (ZMod 2) (LinearMap.range f) := rfl
  rw [hr]
  congr 1
  omega

theorem card_annihilator_ge {k : ℕ} (u : Fin k → Fin n → ZMod 2) :
    2 ^ (n - k) ≤ Nat.card {ψ : Fin n → ZMod 2 // ∀ i, ψ ⬝ᵥ u i = 0} := by
  rw [card_annihilator]
  have := (Matrix.of u).rank_le_card_height
  rw [Fintype.card_fin] at this
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_annihilator_single {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    Nat.card {ψ : Fin n → ZMod 2 // ψ ⬝ᵥ v = 0} = 2 ^ (n - 1) := by
  have e : {ψ : Fin n → ZMod 2 // ψ ⬝ᵥ v = 0} ≃
      {ψ : Fin n → ZMod 2 // ∀ i : Fin 1, ψ ⬝ᵥ ![v] i = 0} :=
    Equiv.subtypeEquivRight fun ψ => by simp
  rw [Nat.card_congr e, card_annihilator, Matrix.rank_eq_finrank_span_row]
  have hr : Set.range (Matrix.of ![v]).row = {v} := by
    rw [Matrix.row_def, Set.range_unique]
    rfl
  rw [hr, finrank_span_singleton hv]

theorem card_kernel_single {φ : Fin n → ZMod 2} (hφ : φ ≠ 0) :
    Nat.card {x : Fin n → ZMod 2 // φ ⬝ᵥ x = 0} = 2 ^ (n - 1) := by
  rw [← card_annihilator_single hφ]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [dotProduct_comm])

theorem card_pointGroup {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    Nat.card (pointGroup v) = 2 ^ (n - 1) := by
  rw [← card_annihilator_single hv]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun ψ => ⟨tv v ψ.1, tv_mem_pointGroup v ψ.1⟩)
    ⟨fun ψ ψ' h => Subtype.ext (tv_right_injective hv ψ.2 ψ'.2 (congrArg Subtype.val h)), ?_⟩)
  rintro ⟨a, ha⟩
  obtain ⟨φ, hφ, rfl⟩ := mem_pointGroup.mp ha
  exact ⟨⟨φ, hφ⟩, rfl⟩

theorem card_hyperplaneGroup {φ : Fin n → ZMod 2} (hφ : φ ≠ 0) :
    Nat.card (hyperplaneGroup φ) = 2 ^ (n - 1) := by
  rw [← card_kernel_single hφ]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨tv x.1 φ, tv_mem_hyperplaneGroup x.1 φ⟩)
    ⟨fun x x' h => Subtype.ext (tv_left_injective hφ x.2 x'.2 (congrArg Subtype.val h)), ?_⟩)
  rintro ⟨a, ha⟩
  obtain ⟨v, hv, rfl⟩ := mem_hyperplaneGroup.mp ha
  exact ⟨⟨v, hv⟩, rfl⟩

theorem exists_ne_zero_annihilator {k : ℕ} (hk : k < n) (u : Fin k → Fin n → ZMod 2) :
    ∃ ψ : Fin n → ZMod 2, ψ ≠ 0 ∧ ∀ i, ψ ⬝ᵥ u i = 0 := by
  by_contra hcon
  have hzero : ∀ ψ : Fin n → ZMod 2, (∀ i, ψ ⬝ᵥ u i = 0) → ψ = 0 :=
    fun ψ hψ => by_contra fun h => hcon ⟨ψ, h, hψ⟩
  have hsub : Subsingleton {ψ : Fin n → ZMod 2 // ∀ i, ψ ⬝ᵥ u i = 0} :=
    ⟨fun a b => Subtype.ext (by rw [hzero a.1 a.2, hzero b.1 b.2])⟩
  have h1 := Finite.card_le_one_iff_subsingleton.mpr hsub
  have h2 := card_annihilator_ge u
  have h3 : 2 ^ 1 ≤ 2 ^ (n - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem exists_two_ne_zero_annihilator {k : ℕ} (hk : k + 2 ≤ n) (u : Fin k → Fin n → ZMod 2) :
    ∃ ψ ψ' : Fin n → ZMod 2, ψ ≠ 0 ∧ ψ' ≠ 0 ∧ ψ ≠ ψ' ∧ (∀ i, ψ ⬝ᵥ u i = 0) ∧
      ∀ i, ψ' ⬝ᵥ u i = 0 := by
  classical
  set s := Finset.univ.filter fun ψ : Fin n → ZMod 2 => ∀ i, ψ ⬝ᵥ u i = 0
  have hcard : 4 ≤ s.card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    have h3 : 2 ^ 2 ≤ 2 ^ (n - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans h3 (card_annihilator_ge u)
  have h0 : (0 : Fin n → ZMod 2) ∈ s := by simp [s]
  have hlt : 1 < (s.erase 0).card := by
    rw [Finset.card_erase_of_mem h0]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  simp only [Finset.mem_erase, s, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact ⟨a, b, ha.1, hb.1, hab, ha.2, hb.2⟩

theorem exists_ne_zero_dotProduct_eq_zero (hn : 2 ≤ n) (v : Fin n → ZMod 2) :
    ∃ ψ : Fin n → ZMod 2, ψ ≠ 0 ∧ ψ ⬝ᵥ v = 0 := by
  obtain ⟨ψ, hψ, h⟩ := exists_ne_zero_annihilator (k := 1) (by omega) ![v]
  exact ⟨ψ, hψ, by simpa using h 0⟩

theorem exists_ne_zero_dotProduct_eq_zero_two (hn : 3 ≤ n) (v w : Fin n → ZMod 2) :
    ∃ ψ : Fin n → ZMod 2, ψ ≠ 0 ∧ ψ ⬝ᵥ v = 0 ∧ ψ ⬝ᵥ w = 0 := by
  obtain ⟨ψ, hψ, h⟩ := exists_ne_zero_annihilator (k := 2) (by omega) ![v, w]
  exact ⟨ψ, hψ, by simpa using h 0, by simpa using h 1⟩

theorem exists_two_ne_zero_dotProduct_eq_zero (hn : 4 ≤ n) (v w : Fin n → ZMod 2) :
    ∃ ψ ψ' : Fin n → ZMod 2, ψ ≠ 0 ∧ ψ' ≠ 0 ∧ ψ ≠ ψ' ∧ ψ ⬝ᵥ v = 0 ∧ ψ ⬝ᵥ w = 0 ∧
      ψ' ⬝ᵥ v = 0 ∧ ψ' ⬝ᵥ w = 0 := by
  obtain ⟨ψ, ψ', hψ, hψ', hne, h, h'⟩ := exists_two_ne_zero_annihilator (k := 2) (by omega) ![v, w]
  exact ⟨ψ, ψ', hψ, hψ', hne, by simpa using h 0, by simpa using h 1, by simpa using h' 0,
    by simpa using h' 1⟩

end CFSG.LargeExtraspecial.A2Mod
