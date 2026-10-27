module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Matrix Subgroup Polynomial CFSG.SL2MinimalFaithful
open scoped MatrixGroups

section Defs

variable {k : Type*} [Field k]

@[expose] def mkSL (a b c d : k) (h : a * d - b * c = 1) : SL(2, k) :=
  ⟨!![a, b; c, d], by rwa [det_fin_two_of]⟩

theorem coe_mkSL (a b c d : k) (h : a * d - b * c = 1) :
    ((mkSL a b c d h : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![a, b; c, d] :=
  rfl

theorem exists_eq_mkSL (g : SL(2, k)) :
    ∃ (a b c d : k) (h : a * d - b * c = 1), g = mkSL a b c d h := by
  have hdet := g.det_coe
  rw [det_fin_two] at hdet
  refine ⟨_, _, _, _, hdet, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mkSL_inv (a b c d : k) (h : a * d - b * c = 1) :
    (mkSL a b c d h)⁻¹ = mkSL d (-b) (-c) a (by linear_combination h) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_mkSL, adjugate_fin_two]

@[expose] def diagSL (μ : kˣ) : SL(2, k) :=
  mkSL (μ : k) 0 0 ((μ⁻¹ : kˣ) : k) (by simp)

theorem coe_diagSL (μ : kˣ) :
    ((diagSL μ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![(μ : k), 0; 0, ((μ⁻¹ : kˣ) : k)] :=
  rfl

@[expose] def diagSLHom : kˣ →* SL(2, k) where
  toFun := diagSL
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagSL]
  map_mul' μ ν := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagSLHom_apply (μ : kˣ) : diagSLHom μ = diagSL μ := rfl

theorem diagSL_mul (μ ν : kˣ) : diagSL μ * diagSL ν = diagSL (μ * ν) :=
  (map_mul diagSLHom μ ν).symm

theorem diagSL_one : diagSL (1 : kˣ) = 1 := map_one diagSLHom

theorem diagSL_inv (μ : kˣ) : (diagSL μ)⁻¹ = diagSL μ⁻¹ := (map_inv diagSLHom μ).symm

theorem diagSL_injective : Function.Injective (diagSL : kˣ → SL(2, k)) := by
  intro μ ν h
  have := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
  exact Units.ext (by simpa [coe_diagSL] using this)

variable (k) in
@[expose] def torusSL : Subgroup SL(2, k) := (diagSLHom (k := k)).range

theorem mem_torusSL_iff {x : SL(2, k)} : x ∈ torusSL k ↔ ∃ μ : kˣ, diagSL μ = x := Iff.rfl

theorem diagSL_mem_torusSL (μ : kˣ) : diagSL μ ∈ torusSL k := ⟨μ, rfl⟩

theorem mkSL_mem_torusSL (a d : k) (h : a * d - 0 * 0 = 1) : mkSL a 0 0 d h ∈ torusSL k := by
  have had : a * d = 1 := by linear_combination h
  refine ⟨Units.mk0 a (left_ne_zero_of_mul_eq_one had), ?_⟩
  rw [diagSLHom_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagSL, coe_mkSL]
  exact (eq_inv_of_mul_eq_one_right had).symm

@[expose] def lowerUnipotent (c : k) : SL(2, k) :=
  mkSL 1 0 c 1 (by ring)

theorem coe_lowerUnipotent (c : k) :
    ((lowerUnipotent c : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![1, 0; c, 1] :=
  rfl

theorem lowerUnipotent_add (c c' : k) :
    lowerUnipotent (c + c') = lowerUnipotent c * lowerUnipotent c' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lowerUnipotent_zero : lowerUnipotent (0 : k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_lowerUnipotent]

theorem lowerUnipotent_injective : Function.Injective (lowerUnipotent : k → SL(2, k)) := by
  intro c c' h
  simpa [coe_lowerUnipotent] using
    congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 1 0) h

@[expose] def lowerUnipotentHom : Multiplicative k →* SL(2, k) where
  toFun c := lowerUnipotent c.toAdd
  map_one' := lowerUnipotent_zero
  map_mul' c c' := lowerUnipotent_add c.toAdd c'.toAdd

theorem lowerUnipotentHom_injective : Function.Injective (lowerUnipotentHom (k := k)) :=
  fun _ _ h => Multiplicative.toAdd.injective (lowerUnipotent_injective (k := k) h)

variable (k) in
@[expose] def upperSL : Subgroup SL(2, k) := (unipotentHom (F := k)).range

variable (k) in
@[expose] def lowerSL : Subgroup SL(2, k) := (lowerUnipotentHom (k := k)).range

theorem mem_upperSL_iff {x : SL(2, k)} : x ∈ upperSL k ↔ ∃ c : k, unipotent c = x :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem mem_lowerSL_iff {x : SL(2, k)} : x ∈ lowerSL k ↔ ∃ c : k, lowerUnipotent c = x :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem unipotent_mem_upperSL (c : k) : unipotent c ∈ upperSL k := mem_upperSL_iff.2 ⟨c, rfl⟩

theorem lowerUnipotent_mem_lowerSL (c : k) : lowerUnipotent c ∈ lowerSL k :=
  mem_lowerSL_iff.2 ⟨c, rfl⟩

theorem card_upperSL [Finite k] : Nat.card (upperSL k) = Nat.card k :=
  (Nat.card_congr (MonoidHom.ofInjective (unipotentHom_injective (F := k))).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem card_lowerSL [Finite k] : Nat.card (lowerSL k) = Nat.card k :=
  (Nat.card_congr (MonoidHom.ofInjective lowerUnipotentHom_injective).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem upperSL_ne_lowerSL : upperSL k ≠ lowerSL k := by
  intro h
  obtain ⟨c, hc⟩ := mem_lowerSL_iff.1 (h ▸ unipotent_mem_upperSL (1 : k))
  simpa [coe_lowerUnipotent, coe_unipotent] using
    congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 1) hc

theorem card_torusSL [Finite k] : Nat.card (torusSL k) = Nat.card k - 1 :=
  (Nat.card_congr (MonoidHom.ofInjective (f := diagSLHom (k := k))
    diagSL_injective).toEquiv).symm.trans (Nat.card_units k)

instance torusSL_isMulCommutative : IsMulCommutative (torusSL k) :=
  Subgroup.range_isMulCommutative _

theorem diagSL_conj_unipotent (μ : kˣ) (c : k) :
    diagSL μ * unipotent c * (diagSL μ)⁻¹ = unipotent ((μ : k) ^ 2 * c) := by
  rw [diagSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem diagSL_conj_lowerUnipotent (μ : kˣ) (c : k) :
    diagSL μ * lowerUnipotent c * (diagSL μ)⁻¹ = lowerUnipotent ((μ : k)⁻¹ ^ 2 * c) := by
  rw [diagSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagSL, coe_lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem eq_of_coe_eq {x y : SL(2, k)}
    (h : (x : Matrix (Fin 2) (Fin 2) k) = (y : Matrix (Fin 2) (Fin 2) k)) : x = y :=
  Subtype.ext h

theorem coe_diagSL_conj (μ : kˣ) (x : SL(2, k)) :
    ((diagSL μ * x * (diagSL μ)⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      !![(x : Matrix (Fin 2) (Fin 2) k) 0 0, (μ : k) ^ 2 * (x : Matrix (Fin 2) (Fin 2) k) 0 1;
        (μ : k)⁻¹ ^ 2 * (x : Matrix (Fin 2) (Fin 2) k) 1 0,
        (x : Matrix (Fin 2) (Fin 2) k) 1 1] := by
  obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_mkSL x
  rw [diagSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagSL, coe_mkSL, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem coe_mkSL_conj_unipotent {p q r s : k} (h : p * s - q * r = 1) (t : k) :
    ((mkSL p q r s h * unipotent t * (mkSL p q r s h)⁻¹ : SL(2, k)) :
      Matrix (Fin 2) (Fin 2) k) = !![1 - p * r * t, p ^ 2 * t; -(r ^ 2 * t), 1 + p * r * t] := by
  rw [mkSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mkSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (h₁ : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (h₂ : ∀ h ∈ H, x⁻¹ * h * x⁻¹⁻¹ ∈ H) :
    x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  refine fun h => ⟨h₁ h, fun hh => ?_⟩
  simpa [mul_assoc] using h₂ _ hh

theorem torusSL_le_normalizer_upperSL : torusSL k ≤ normalizer (upperSL k : Set SL(2, k)) := by
  have key : ∀ μ : kˣ, ∀ h ∈ upperSL k, diagSL μ * h * (diagSL μ)⁻¹ ∈ upperSL k := by
    rintro μ _ ⟨c, rfl⟩
    exact (diagSL_conj_unipotent μ c.toAdd).symm ▸ unipotent_mem_upperSL _
  rintro _ ⟨μ, rfl⟩
  refine mem_normalizer_of_conj_mem (key μ) fun h hh => ?_
  rw [diagSLHom_apply, diagSL_inv]
  exact key μ⁻¹ h hh

theorem torusSL_le_normalizer_lowerSL : torusSL k ≤ normalizer (lowerSL k : Set SL(2, k)) := by
  have key : ∀ μ : kˣ, ∀ h ∈ lowerSL k, diagSL μ * h * (diagSL μ)⁻¹ ∈ lowerSL k := by
    rintro μ _ ⟨c, rfl⟩
    exact (diagSL_conj_lowerUnipotent μ c.toAdd).symm ▸ lowerUnipotent_mem_lowerSL _
  rintro _ ⟨μ, rfl⟩
  refine mem_normalizer_of_conj_mem (key μ) fun h hh => ?_
  rw [diagSLHom_apply, diagSL_inv]
  exact key μ⁻¹ h hh

theorem mkSL_mul_eq_diagSL_mul {a b c d p q r s : k} (hg : a * d - b * c = 1)
    (hx : p * s - q * r = 1) (μ : kˣ) (h₁ : p * a + q * c = μ * p) (h₂ : p * b + q * d = μ * q)
    (h₃ : r * a + s * c = (μ : k)⁻¹ * r) (h₄ : r * b + s * d = (μ : k)⁻¹ * s) :
    mkSL p q r s hx * mkSL a b c d hg = diagSL μ * mkSL p q r s hx := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mkSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two] <;> assumption

end Defs

section Eigenvalue

theorem X_pow_card_sub_X_eq_prod {K : Type*} [Field K] [Fintype K] :
    (X ^ Fintype.card K - X : K[X]) = ∏ c : K, (X - C c) := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hm : (X ^ Fintype.card K - X : K[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hq)
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
    rw [FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq K hq]
    rfl)
  rw [FiniteField.roots_X_pow_card_sub_X] at h
  rw [← h]
  rfl

theorem exists_isRoot_of_aeval_eq_zero {K A : Type*} [Field K] [Fintype K] [Ring A] [Algebra K A]
    [Nontrivial A] {g : A} (hg : g ^ Fintype.card K = g) {P : K[X]} (hP : aeval g P = 0) :
    ∃ c : K, P.IsRoot c := by
  by_contra h
  have hcop : IsCoprime P (X ^ Fintype.card K - X) := by
    rw [X_pow_card_sub_X_eq_prod]
    refine IsCoprime.prod_right fun c _ => ?_
    exact ((irreducible_X_sub_C c).coprime_iff_not_dvd.2 fun hd =>
      h ⟨c, dvd_iff_isRoot.1 hd⟩).symm
  obtain ⟨u, v, huv⟩ := hcop
  have := congrArg (aeval g) huv
  rw [map_add, map_mul, map_mul, hP, map_sub, map_pow, aeval_X, hg, sub_self, mul_zero,
    mul_zero, add_zero, map_one] at this
  exact zero_ne_one this

theorem exists_eigenvalue_of_pow_card_eq_self {K : Type*} [Field K] [Fintype K]
    {M : Matrix (Fin 2) (Fin 2) K} (hM : M ^ Fintype.card K = M) :
    ∃ c : K, c ^ 2 - M.trace * c + M.det = 0 := by
  obtain ⟨c, hc⟩ := exists_isRoot_of_aeval_eq_zero hM (aeval_self_charpoly M)
  refine ⟨c, ?_⟩
  rw [IsRoot.def, charpoly_fin_two] at hc
  simpa using hc

end Eigenvalue

section CharTwo

variable {k : Type*} [Field k] [CharP k 2]

theorem units_sq_eq_one_iff (μ : kˣ) : μ ^ 2 = 1 ↔ μ = 1 := by
  refine ⟨fun h => Units.ext (CharTwo.sq_injective ?_), fun h => by rw [h, one_pow]⟩
  simpa using congrArg Units.val h

theorem units_inv_ne_self {μ : kˣ} (hμ : μ ≠ 1) : (μ : k)⁻¹ ≠ μ := by
  intro h
  refine hμ ((units_sq_eq_one_iff μ).1 (Units.ext ?_))
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
  nth_rw 1 [← h]
  exact inv_mul_cancel₀ μ.ne_zero

theorem odd_card_sub_one [Finite k] : Odd (Nat.card k - 1) := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨r, hr⟩ := (CharP.cast_eq_zero_iff k 2 _).1 (FiniteField.cast_card_eq_zero k)
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card]
  exact ⟨r - 1, by omega⟩

theorem pow_card_sub_one_eq_self [Finite k] {G : Type*} [Monoid G] {g : G} (hg : g * g = 1) :
    g ^ (Nat.card k - 1) = g := by
  obtain ⟨m, hm⟩ := odd_card_sub_one (k := k)
  rw [hm, pow_succ, pow_mul, sq, hg, one_pow, one_mul]

theorem mkSL_mul_self_eq_one {a b c d : k} (h : a * d - b * c = 1) (ht : a + d = 0) :
    mkSL a b c d h * mkSL a b c d h = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_mkSL, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination a * ht - h - h2
  · linear_combination b * ht
  · linear_combination c * ht
  · linear_combination d * ht - h - h2

theorem exists_conj_eq_diagSL [Finite k] {g : SL(2, k)} (hg1 : g ≠ 1)
    (hg : g ^ (Nat.card k - 1) = 1) :
    ∃ (x : SL(2, k)) (μ : kˣ), μ ≠ 1 ∧ x * g * x⁻¹ = diagSL μ := by
  have : Fintype k := Fintype.ofFinite k
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hgq' : g ^ Fintype.card k = g := by
    rw [← Nat.card_eq_fintype_card, ← Nat.sub_add_cancel hq1.le, pow_succ, hg, one_mul]
  have hgq : (g : Matrix (Fin 2) (Fin 2) k) ^ Fintype.card k = g := by
    simpa using congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k)) hgq'
  obtain ⟨l, hl⟩ := exists_eigenvalue_of_pow_card_eq_self hgq
  obtain ⟨a, b, c, d, hdet, rfl⟩ := exists_eq_mkSL g
  rw [coe_mkSL, trace_fin_two_of, det_fin_two_of, hdet] at hl
  have ht : a + d ≠ 0 := fun ht =>
    hg1 ((pow_card_sub_one_eq_self (k := k) (mkSL_mul_self_eq_one hdet ht)).symm.trans hg)
  by_cases hc : c = 0
  ·
    subst hc
    have had : a * d = 1 := by linear_combination hdet
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    have hne : a - d ≠ 0 := fun h => ht (by linear_combination h + d * h2)
    have hda : ((Units.mk0 a ha : kˣ) : k)⁻¹ = d := by
      rw [Units.val_mk0]
      exact (eq_inv_of_mul_eq_one_right had).symm
    refine ⟨mkSL 1 (b / (a - d)) 0 1 (by ring), Units.mk0 a ha, fun h1 => ?_,
      mul_inv_eq_of_eq_mul (mkSL_mul_eq_diagSL_mul _ _ _ ?_ ?_ ?_ ?_)⟩
    · have h1 : a = 1 := by simpa using congrArg Units.val h1
      subst h1
      exact ht (by linear_combination had + h2)
    · simp
    · rw [Units.val_mk0]
      field_simp
      ring
    · simp
    · rw [hda]
      ring
  ·
    have hl0 : l ≠ 0 := fun h => by simp [h] at hl
    set m : k := l⁻¹ with hm
    have hlm : l * m = 1 := mul_inv_cancel₀ hl0
    have hl1 : Units.mk0 l hl0 ≠ 1 := by
      intro h
      have : l = 1 := by simpa using congrArg Units.val h
      subst this
      exact ht (by linear_combination -hl + h2)
    have he : m - l ≠ 0 := by
      have := units_inv_ne_self hl1
      rw [Units.val_mk0] at this
      exact sub_ne_zero.2 this
    set s : k := (c * (m - l))⁻¹ with hs
    have hsc : s * (c * (m - l)) = 1 := inv_mul_cancel₀ (mul_ne_zero hc he)
    refine ⟨mkSL (c * s) ((l - a) * s) c (m - a) (by linear_combination hsc), Units.mk0 l hl0,
      hl1, mul_inv_eq_of_eq_mul (mkSL_mul_eq_diagSL_mul _ _ _ ?_ ?_ ?_ ?_)⟩
    · rw [Units.val_mk0]
      ring
    · rw [Units.val_mk0]
      linear_combination s * (-hl - hdet)
    · rw [Units.val_mk0, ← hm]
      ring
    · rw [Units.val_mk0, ← hm]
      linear_combination (-m ^ 2) * hl + (l * m + 1 - (a + d) * m) * hlm - hdet

theorem centralizer_diagSL {μ : kˣ} (hμ : μ ≠ 1) :
    centralizer ({diagSL μ} : Set SL(2, k)) = torusSL k := by
  have hne : (μ : k) - (μ : k)⁻¹ ≠ 0 := sub_ne_zero.2 (units_inv_ne_self hμ).symm
  ext x
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_mkSL x
    have h01 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 1) hx
    have h10 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 1 0) hx
    simp [coe_mkSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
    have hb : b = 0 := by
      have : b * ((μ : k) - (μ : k)⁻¹) = 0 := by linear_combination -h01
      exact (mul_eq_zero.1 this).resolve_right hne
    have hc : c = 0 := by
      have : c * ((μ : k) - (μ : k)⁻¹) = 0 := by linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right hne
    subst hb hc
    exact mkSL_mem_torusSL a d h
  · rintro ⟨ν, rfl⟩
    rw [diagSLHom_apply, diagSL_mul, diagSL_mul, mul_comm]

theorem centralizer_zpowers_diagSL {μ : kˣ} (hμ : μ ≠ 1) :
    centralizer (zpowers (diagSL μ) : Set SL(2, k)) = torusSL k := by
  rw [zpowers_eq_closure, centralizer_closure, centralizer_diagSL hμ]

theorem eq_upperSL_or_eq_lowerSL [Finite k] {W : Subgroup SL(2, k)}
    (hW : Nat.card W = Nat.card k) {μ : kˣ} (hμ : μ ≠ 1)
    (hWμ : diagSL μ ∈ normalizer (W : Set SL(2, k))) : W = upperSL k ∨ W = lowerSL k := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two
    (by rw [Nat.card_eq_fintype_card, hn]) hW
  have hWeq : (upperSL k).map (MulAut.conj g).toMonoidHom = W := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      exact hg t.toAdd
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_upperSL, hW]
  have h1 : diagSL μ * (g * unipotent 1 * g⁻¹) * (diagSL μ)⁻¹ ∈ W :=
    (mem_normalizer_iff.1 hWμ _).1 (hg 1)
  rw [← hWeq] at h1
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := h1
  obtain ⟨p, q, r, s, hdet, rfl⟩ := exists_eq_mkSL g
  have ht' : mkSL p q r s hdet * unipotent t.toAdd * (mkSL p q r s hdet)⁻¹ =
      diagSL μ * (mkSL p q r s hdet * unipotent 1 * (mkSL p q r s hdet)⁻¹) * (diagSL μ)⁻¹ :=
    ht
  have e00 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) ht'
  have e01 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 1) ht'
  simp only [coe_diagSL_conj, coe_mkSL_conj_unipotent] at e00 e01
  simp at e00 e01
  have hpr : p = 0 ∨ r = 0 := by
    by_contra! hpr
    have ht1 : t.toAdd = 1 := by
      have : p * r * (t.toAdd - 1) = 0 := by linear_combination e00
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hpr.1 hpr.2))
    rw [ht1] at e01
    apply hμ
    refine (units_sq_eq_one_iff μ).1 (Units.ext ?_)
    have : p ^ 2 * (1 - (μ : k) ^ 2) = 0 := by linear_combination e01
    have h3 := (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hpr.1)
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination -h3
  have hmem : ∀ x ∈ W, ∃ c : k, mkSL p q r s hdet * unipotent c * (mkSL p q r s hdet)⁻¹ = x := by
    rw [← hWeq]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c.toAdd, rfl⟩
  rcases hpr with hp | hr
  · subst hp
    right
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_lowerSL, hW])
    obtain ⟨c, rfl⟩ := hmem x hx
    refine mem_lowerSL_iff.2 ⟨-(r ^ 2 * c), eq_of_coe_eq ?_⟩
    rw [coe_mkSL_conj_unipotent, coe_lowerUnipotent]
    simp
  · subst hr
    left
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_upperSL, hW])
    obtain ⟨c, rfl⟩ := hmem x hx
    refine mem_upperSL_iff.2 ⟨p ^ 2 * c, eq_of_coe_eq ?_⟩
    rw [coe_mkSL_conj_unipotent, coe_unipotent]
    simp

theorem torusSL_le_normalizer [Finite k] {W : Subgroup SL(2, k)} (hW : Nat.card W = Nat.card k)
    {μ : kˣ} (hμ : μ ≠ 1) (hWμ : diagSL μ ∈ normalizer (W : Set SL(2, k))) :
    torusSL k ≤ normalizer (W : Set SL(2, k)) := by
  rcases eq_upperSL_or_eq_lowerSL hW hμ hWμ with rfl | rfl
  · exact torusSL_le_normalizer_upperSL
  · exact torusSL_le_normalizer_lowerSL

variable (k) in
@[expose] def weylSL : SL(2, k) :=
  mkSL 0 1 1 0 (by rw [mul_zero, one_mul, zero_sub, CharTwo.neg_eq])

theorem coe_weylSL : ((weylSL k : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; 1, 0] := rfl

theorem weylSL_mul_self : weylSL k * weylSL k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_weylSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylSL_inv : (weylSL k)⁻¹ = weylSL k := inv_eq_of_mul_eq_one_right weylSL_mul_self

theorem weylSL_conj_diagSL (μ : kˣ) : weylSL k * diagSL μ * (weylSL k)⁻¹ = diagSL μ⁻¹ := by
  rw [weylSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylSL_conj_unipotent (c : k) :
    weylSL k * unipotent c * (weylSL k)⁻¹ = lowerUnipotent c := by
  rw [weylSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_unipotent, coe_lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylSL_conj_lowerUnipotent (c : k) :
    weylSL k * lowerUnipotent c * (weylSL k)⁻¹ = unipotent c := by
  rw [weylSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_unipotent, coe_lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylSL_mem_normalizer_torusSL : weylSL k ∈ normalizer (torusSL k : Set SL(2, k)) := by
  have key : ∀ h ∈ torusSL k, weylSL k * h * (weylSL k)⁻¹ ∈ torusSL k := by
    rintro _ ⟨μ, rfl⟩
    rw [diagSLHom_apply, weylSL_conj_diagSL]
    exact diagSL_mem_torusSL _
  refine mem_normalizer_of_conj_mem key fun h hh => ?_
  rw [weylSL_inv]
  exact key h hh

theorem map_conj_weylSL_upperSL :
    (upperSL k).map (MulAut.conj (weylSL k)).toMonoidHom = lowerSL k := by
  ext x
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact mem_lowerSL_iff.2 ⟨c.toAdd, (weylSL_conj_unipotent c.toAdd).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨unipotent c.toAdd, unipotent_mem_upperSL _, weylSL_conj_unipotent c.toAdd⟩

theorem map_conj_weylSL_lowerSL :
    (lowerSL k).map (MulAut.conj (weylSL k)).toMonoidHom = upperSL k := by
  ext x
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact mem_upperSL_iff.2 ⟨c.toAdd, (weylSL_conj_lowerUnipotent c.toAdd).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨lowerUnipotent c.toAdd, lowerUnipotent_mem_lowerSL _,
      weylSL_conj_lowerUnipotent c.toAdd⟩

theorem weylSL_eq : weylSL k = unipotent 1 * lowerUnipotent 1 * unipotent 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_unipotent, coe_lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | linear_combination h2 | linear_combination -h2

theorem torusSL_inf_centralizer_upperSL :
    torusSL k ⊓ centralizer (upperSL k : Set SL(2, k)) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨⟨μ, rfl⟩, hc⟩ := mem_inf.1 hx
  rw [diagSLHom_apply] at hc ⊢
  have h1 := mem_centralizer_iff.1 hc (unipotent 1) (unipotent_mem_upperSL 1)
  have h2 : diagSL μ * unipotent 1 * (diagSL μ)⁻¹ = unipotent 1 := by
    rw [← h1, mul_inv_cancel_right]
  rw [diagSL_conj_unipotent, mul_one] at h2
  have hμ : μ = 1 := (units_sq_eq_one_iff μ).1 (Units.ext (by simpa using unipotent_injective h2))
  rw [Subgroup.mem_bot, hμ, diagSL_one]

theorem torusSL_inf_centralizer_lowerSL :
    torusSL k ⊓ centralizer (lowerSL k : Set SL(2, k)) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨⟨μ, rfl⟩, hc⟩ := mem_inf.1 hx
  rw [diagSLHom_apply] at hc ⊢
  have h1 := mem_centralizer_iff.1 hc (lowerUnipotent 1) (lowerUnipotent_mem_lowerSL 1)
  have h2 : diagSL μ * lowerUnipotent 1 * (diagSL μ)⁻¹ = lowerUnipotent 1 := by
    rw [← h1, mul_inv_cancel_right]
  rw [diagSL_conj_lowerUnipotent, mul_one] at h2
  have h3 : ((μ⁻¹ : kˣ) : k) ^ 2 = 1 := by simpa using lowerUnipotent_injective h2
  have hμ : μ⁻¹ = 1 := (units_sq_eq_one_iff μ⁻¹).1 (Units.ext (by simpa using h3))
  rw [Subgroup.mem_bot, inv_eq_one.1 hμ, diagSL_one]

theorem torusSL_inf_centralizer [Finite k] {W : Subgroup SL(2, k)} (hW : Nat.card W = Nat.card k)
    {μ : kˣ} (hμ : μ ≠ 1) (hWμ : diagSL μ ∈ normalizer (W : Set SL(2, k))) :
    torusSL k ⊓ centralizer (W : Set SL(2, k)) = ⊥ := by
  rcases eq_upperSL_or_eq_lowerSL hW hμ hWμ with rfl | rfl
  · exact torusSL_inf_centralizer_upperSL
  · exact torusSL_inf_centralizer_lowerSL

end CharTwo

end CFSG.LocalAnalysis.EvenBN.Common
