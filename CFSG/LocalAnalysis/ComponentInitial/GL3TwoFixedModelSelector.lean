module

public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel

open Matrix Subgroup LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

section Binary

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem det_eq_one_of_GL_two {m : Type*} [Fintype m] [DecidableEq m] (g : GL m (ZMod 2)) :
    (g : Matrix m m (ZMod 2)).det = 1 := by
  have h := Matrix.isUnits_det_units g
  rcases zmod_two_eq_zero_or_one (g : Matrix m m (ZMod 2)).det with h0 | h1
  · rw [h0] at h
    exact absurd h not_isUnit_zero
  · exact h1

variable (K : Type*) [Field K] [CharP K 2]

abbrev binaryHom : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

theorem binaryHom_apply_of_two (x : ZMod 2) : binaryHom (ZMod 2) x = x := by
  rcases zmod_two_eq_zero_or_one x with rfl | rfl <;> simp

@[expose] def binarySL (m : ℕ) : GL (Fin m) (ZMod 2) →* SpecialLinearGroup (Fin m) K where
  toFun g := ⟨(g : Matrix (Fin m) (Fin m) (ZMod 2)).map (binaryHom K), by
    have h := RingHom.map_det (binaryHom K) (g : Matrix (Fin m) (Fin m) (ZMod 2))
    rw [RingHom.mapMatrix_apply, det_eq_one_of_GL_two, map_one] at h
    exact h.symm⟩
  map_one' := Subtype.ext (by
    change ((1 : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).map (binaryHom K) = 1
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' g h := Subtype.ext (by
    change ((g * h : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).map (binaryHom K) =
      (g : Matrix (Fin m) (Fin m) (ZMod 2)).map (binaryHom K) *
        (h : Matrix (Fin m) (Fin m) (ZMod 2)).map (binaryHom K)
    rw [Units.val_mul, Matrix.map_mul])

@[simp]
theorem coe_binarySL (m : ℕ) (g : GL (Fin m) (ZMod 2)) :
    ((binarySL K m g : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      (g : Matrix (Fin m) (Fin m) (ZMod 2)).map (binaryHom K) :=
  rfl

@[expose] def binaryEmbed : ∀ {n : ℕ}, n = 3 → (GL (Fin 3) (ZMod 2) →* projectiveSL n K)
  | _, rfl => (proj 3 K).comp (binarySL K 3)

theorem binaryEmbed_apply (g : GL (Fin 3) (ZMod 2)) :
    binaryEmbed K (rfl : 3 = 3) g = proj 3 K (binarySL K 3 g) :=
  rfl

theorem binaryEmbed_injective : Function.Injective (binaryEmbed K (rfl : 3 = 3)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [binaryEmbed_apply, ← MonoidHom.mem_ker, ker_proj] at hg
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hg
  have hc' : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (binaryHom K) = scalar (Fin 3) (c : K) :=
    hc
  have h00 := congrFun (congrFun hc' 0) 0
  rw [Matrix.map_apply, scalar_apply, diagonal_apply_eq] at h00
  have hc1 : (c : K) = 1 := by
    rcases zmod_two_eq_zero_or_one ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0) with h | h
    · rw [h, map_zero] at h00
      exact absurd h00.symm c.ne_zero
    · rw [h, map_one] at h00
      exact h00.symm
  apply Units.ext
  apply Matrix.map_injective (binaryHom K).injective
  change (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (binaryHom K) =
    ((1 : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (binaryHom K)
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), hc', hc1, map_one]

theorem binaryEmbed_surjective_two : Function.Surjective (binaryEmbed (ZMod 2) (rfl : 3 = 3)) := by
  intro x
  obtain ⟨A, rfl⟩ := proj_surjective 3 (ZMod 2) x
  refine ⟨SpecialLinearGroup.toGL A, ?_⟩
  rw [binaryEmbed_apply]
  congr 1
  apply Subtype.ext
  change (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (binaryHom (ZMod 2)) =
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
  ext i j
  rw [Matrix.map_apply, binaryHom_apply_of_two]

theorem binaryEmbed_mem_autFixed (σ : K ≃+* K) (g : GL (Fin 3) (ZMod 2)) :
    binaryEmbed K (rfl : 3 = 3) g ∈ autFixed (fieldAut 3 K σ) := by
  rw [mem_autFixed, binaryEmbed_apply, fieldAut_proj]
  congr 1
  apply Subtype.ext
  change ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (binaryHom K)).map σ.toRingHom =
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (binaryHom K)
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply]
  rcases zmod_two_eq_zero_or_one ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) with h | h <;>
    rw [h] <;> simp

omit [CharP K 2] in
theorem eq_zero_or_eq_one_of_sq_eq {x : K} (h : x ^ 2 = x) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (mul_left_cancel₀ hx (by rw [mul_one, ← sq, h]))

theorem autFixed_le_range_binaryEmbed {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2) :
    autFixed (fieldAut 3 K σ) ≤ (binaryEmbed K (rfl : 3 = 3)).range := by
  intro x hx
  obtain ⟨A, rfl⟩ := proj_surjective 3 K x
  rw [mem_autFixed, fieldAut_proj] at hx
  have hx' : (SpecialLinearGroup.map σ.toRingHom A)⁻¹ * A ∈ scalars 3 K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
  obtain ⟨z, hz, hAz⟩ : ∃ z ∈ scalars 3 K, A = SpecialLinearGroup.map σ.toRingHom A * z :=
    ⟨_, hx', (mul_inv_cancel_left _ _).symm⟩
  obtain ⟨c, hc3, hzc⟩ := mem_scalars.1 hz
  have hzc' : (z : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (c : K) := hzc
  have hAij : ∀ i j, (A : Matrix (Fin 3) (Fin 3) K) i j =
      σ ((A : Matrix (Fin 3) (Fin 3) K) i j) * c := fun i j => by
    have h : (A : Matrix (Fin 3) (Fin 3) K) =
        (SpecialLinearGroup.map σ.toRingHom A : Matrix (Fin 3) (Fin 3) K) *
          (z : Matrix (Fin 3) (Fin 3) K) := by
      conv_lhs => rw [hAz]
      rfl
    rw [hzc', scalar_apply] at h
    have h2 := congrFun (congrFun h i) j
    rw [mul_diagonal] at h2
    exact h2
  obtain ⟨A', hA'⟩ : ∃ A' : SpecialLinearGroup (Fin 3) K, A' = scalarElement c hc3 * A :=
    ⟨_, rfl⟩
  have hA'ij : ∀ i j, (A' : Matrix (Fin 3) (Fin 3) K) i j =
      c * (A : Matrix (Fin 3) (Fin 3) K) i j := fun i j => by
    rw [hA']
    show (scalar (Fin 3) (c : K) * (A : Matrix (Fin 3) (Fin 3) K)) i j = _
    rw [scalar_apply, diagonal_mul]
  have hfix : ∀ i j, (A' : Matrix (Fin 3) (Fin 3) K) i j ^ 2 =
      (A' : Matrix (Fin 3) (Fin 3) K) i j := fun i j => by
    rw [← hσ, hA'ij, map_mul, hσ]
    conv_rhs => rw [hAij]
    ring
  have hex : ∀ i j, ∃ a : ZMod 2, binaryHom K a = (A' : Matrix (Fin 3) (Fin 3) K) i j :=
    fun i j => by
      rcases eq_zero_or_eq_one_of_sq_eq K (hfix i j) with h | h
      · exact ⟨0, by rw [map_zero, h]⟩
      · exact ⟨1, by rw [map_one, h]⟩
  choose g₀ hg₀ using hex
  have hg₀A : (Matrix.of g₀).map (binaryHom K) = (A' : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    rw [Matrix.map_apply, Matrix.of_apply, hg₀]
  have hdet1 : binaryHom K (Matrix.of g₀).det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hg₀A]
    exact A'.2
  have hdet : (Matrix.of g₀).det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdet1
    exact zero_ne_one hdet1
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.of g₀) hdet, ?_⟩
  rw [binaryEmbed_apply]
  have hSL : binarySL K 3 (GeneralLinearGroup.mkOfDetNeZero (Matrix.of g₀) hdet) = A' :=
    Subtype.ext (by
      change (Matrix.of g₀).map (binaryHom K) = _
      exact hg₀A)
  have hker : proj 3 K (scalarElement c hc3) = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj]
    exact scalarElement_mem_scalars c hc3
  rw [hSL, hA', map_mul, hker, one_mul]

theorem card_range_binaryEmbed : Nat.card (binaryEmbed K (rfl : 3 = 3)).range = 168 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (binaryEmbed_injective K)).toEquiv,
    card_GL_three_two]

end Binary

section BaseChange

variable (K : Type*) [Field K] [CharP K 2]

@[expose] def projBaseChange (n : ℕ) : projectiveSL n (ZMod 2) →* projectiveSL n K :=
  QuotientGroup.map (scalars n (ZMod 2)) (scalars n K) (SpecialLinearGroup.map (binaryHom K))
    (by
      rintro A ⟨c, hc, hA⟩
      have hA' : (A : Matrix (Fin n) (Fin n) (ZMod 2)) = scalar (Fin n) (c : ZMod 2) := hA
      refine ⟨Units.map (binaryHom K : ZMod 2 →* K) c, by rw [← map_pow, hc, map_one], ?_⟩
      change (A : Matrix (Fin n) (Fin n) (ZMod 2)).map (binaryHom K) = _
      rw [hA']
      ext i j
      rw [Matrix.map_apply, scalar_apply, scalar_apply, diagonal_apply, diagonal_apply]
      split_ifs <;> simp)

theorem projBaseChange_proj (n : ℕ) (A : SpecialLinearGroup (Fin n) (ZMod 2)) :
    projBaseChange K n (proj n (ZMod 2) A) = proj n K (SpecialLinearGroup.map (binaryHom K) A) :=
  rfl

theorem projBaseChange_conjAut (n : ℕ) (U : GL (Fin n) (ZMod 2)) (y : projectiveSL n (ZMod 2)) :
    projBaseChange K n (conjAut n (ZMod 2) U y) =
      conjAut n K (GeneralLinearGroup.map (binaryHom K) U) (projBaseChange K n y) := by
  obtain ⟨A, rfl⟩ := proj_surjective n (ZMod 2) y
  rw [conjAut_proj, projBaseChange_proj, projBaseChange_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  change ((slConjugation n (ZMod 2) U A :
      SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).map (binaryHom K) =
    ((slConjugation n K (GeneralLinearGroup.map (binaryHom K) U)
      (SpecialLinearGroup.map (binaryHom K) A) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)
  rw [coe_slConjugation, coe_slConjugation, Matrix.map_mul, Matrix.map_mul, ← map_inv]
  rfl

theorem projBaseChange_dualAut (n : ℕ) (y : projectiveSL n (ZMod 2)) :
    projBaseChange K n (dualAut n (ZMod 2) y) = dualAut n K (projBaseChange K n y) := by
  obtain ⟨A, rfl⟩ := proj_surjective n (ZMod 2) y
  rw [dualAut_proj, projBaseChange_proj, projBaseChange_proj, dualAut_proj, ← map_inv]
  rfl

theorem projBaseChange_binaryEmbed (g : GL (Fin 3) (ZMod 2)) :
    projBaseChange K 3 (binaryEmbed (ZMod 2) (rfl : 3 = 3) g) = binaryEmbed K (rfl : 3 = 3) g := by
  rw [binaryEmbed_apply, binaryEmbed_apply, projBaseChange_proj]
  congr 1
  apply Subtype.ext
  change ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (binaryHom (ZMod 2))).map (binaryHom K) =
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (binaryHom K)
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, binaryHom_apply_of_two]

theorem exists_binary_form (ω : MulAut (GL (Fin 3) (ZMod 2))) :
    ∃ (U : GL (Fin 3) (ZMod 2)) (v : ℕ), v ≤ 1 ∧ ∀ g, binaryEmbed K (rfl : 3 = 3) (ω g) =
      (conjAut 3 K (GeneralLinearGroup.map (binaryHom K) U) * dualAut 3 K ^ v)
        (binaryEmbed K (rfl : 3 = 3) g) := by
  set j₂ : GL (Fin 3) (ZMod 2) ≃* projectiveSL 3 (ZMod 2) :=
    MulEquiv.ofBijective (binaryEmbed (ZMod 2) (rfl : 3 = 3))
      ⟨binaryEmbed_injective (ZMod 2), binaryEmbed_surjective_two⟩ with hj₂
  obtain ⟨-, hform⟩ := automorphism_generation (K := ZMod 2) (n := 3) le_rfl
  obtain ⟨U, φ, v, hv, hω'⟩ := hform ((j₂.symm.trans ω).trans j₂)
  have hφ : φ = 1 := RingEquiv.ext fun x => by
    rcases zmod_two_eq_zero_or_one x with rfl | rfl <;> simp
  rw [hφ, map_one, mul_one] at hω'
  refine ⟨U, v, hv, fun g => ?_⟩
  have h1 : binaryEmbed (ZMod 2) (rfl : 3 = 3) (ω g) =
      (conjAut 3 (ZMod 2) U * dualAut 3 (ZMod 2) ^ v) (binaryEmbed (ZMod 2) (rfl : 3 = 3) g) := by
    rw [← hω']
    change _ = j₂ (ω (j₂.symm (j₂ g)))
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [← projBaseChange_binaryEmbed K (ω g), h1, ← projBaseChange_binaryEmbed K g]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with rfl | rfl
  · simp only [pow_zero, mul_one]
    exact projBaseChange_conjAut K 3 U _
  · simp only [pow_one, MulAut.mul_apply]
    rw [projBaseChange_conjAut, projBaseChange_dualAut]

theorem commute_binary_form (U : GL (Fin 3) (ZMod 2)) (v : ℕ) (σ : K ≃+* K) :
    Commute (conjAut 3 K (GeneralLinearGroup.map (binaryHom K) U) * dualAut 3 K ^ v)
      (fieldAut 3 K σ) := by
  obtain ⟨-, -, hfc, -⟩ := standard_automorphism_transport (n := 3) (K := K)
  have hU : GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.map (binaryHom K) U) =
      GeneralLinearGroup.map (binaryHom K) U := by
    ext i j
    rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply]
    rcases zmod_two_eq_zero_or_one ((U : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) with h | h <;>
      rw [h] <;> simp
  have hc : Commute (conjAut 3 K (GeneralLinearGroup.map (binaryHom K) U)) (fieldAut 3 K σ) := by
    have h := hfc σ (GeneralLinearGroup.map (binaryHom K) U)
    rw [hU] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  exact hc.mul_left
    ((CFSG.ComponentClassification.UnbalancedCatalog.fieldAut_commute_dualAut σ).symm.pow_left v)

end BaseChange

section Small

theorem exists_conjAut_dualAut_inv {n : ℕ} {K : Type*} [Field K] (W : GL (Fin n) K) {v : ℕ}
    (hv : v ≤ 1) : ∃ (B : GL (Fin n) K) (e : ℕ), e ≤ 1 ∧
      (conjAut n K W * dualAut n K ^ v)⁻¹ = conjAut n K B * dualAut n K ^ e := by
  obtain ⟨-, -, -, hdd, hdc, -⟩ := standard_automorphism_transport (n := n) (K := K)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with rfl | rfl
  · exact ⟨W⁻¹, 0, zero_le_one, by rw [pow_zero, mul_one, mul_one, map_inv]⟩
  · refine ⟨GeneralLinearGroup.inverseTranspose W⁻¹, 1, le_rfl, ?_⟩
    have hδinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hdd
    simp only [pow_one]
    rw [← hdc, _root_.mul_inv_rev, hδinv, map_inv,
      mul_assoc (dualAut n K * (conjAut n K W)⁻¹), hdd, mul_one]

theorem card_projectiveSL_three_four {K : Type*} [Field K] (hK : Nat.card K = 4) :
    Nat.card (projectiveSL 3 K) = 20160 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := finite_field_prime_power_characteristic (k := 2) Nat.prime_two
    (by norm_num) (by rw [hK]; norm_num)
  obtain ⟨-, hSL, -, hZ, hP, -⟩ := linear_order 2 4 hK (n := 3) (by norm_num)
  have hunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hunits]; norm_num)
  obtain ⟨c, hc⟩ := exists_ne (1 : Kˣ)
  have hc3 : c ^ 3 = 1 := by
    rw [← hunits]
    exact pow_card_eq_one'
  have hne : scalarElement c hc3 ≠ 1 := by
    intro h
    have h00 := congrArg (fun A : SpecialLinearGroup (Fin 3) K =>
      (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
    change (scalar (Fin 3) (c : K)) 0 0 = (1 : Matrix (Fin 3) (Fin 3) K) 0 0 at h00
    rw [scalar_apply, diagonal_apply_eq, one_apply_eq] at h00
    exact hc (Units.ext h00)
  have h1 : 1 < Nat.card (scalars 3 K) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨⟨_, scalarElement_mem_scalars c hc3⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  have hZ3 : Nat.card (scalars 3 K) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h | h
    · omega
    · exact h
  rw [hP, hSL, hZ3]
  decide

theorem ordProj_two_20160 : ordProj[2] 20160 = 64 := by
  rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  norm_num

variable {P : Type*} [Group P]

theorem conj_comm_aut (α : MulAut P) (p : P) :
    α * MulAut.conj p = MulAut.conj (α p) * α := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_injective_of_center_eq_bot (hZ : center P = ⊥) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : x ∈ center P := by
    rw [mem_center_iff]
    intro y
    have h := congrArg (fun φ : MulAut P => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [hZ, mem_bot] at hxZ
  exact hxZ

theorem conj_mem_centralizer_iff (hconj : Function.Injective (MulAut.conj : P →* MulAut P))
    (α : MulAut P) (p : P) : MulAut.conj p ∈ centralizer {α} ↔ p ∈ autFixed α := by
  rw [mem_centralizer_singleton_iff, mem_autFixed, conj_comm_aut]
  constructor
  · intro h
    exact (hconj (mul_right_cancel h)).symm
  · intro h
    rw [h]

theorem conj_map_le_and_normal (hconj : Function.Injective (MulAut.conj : P →* MulAut P))
    {α : MulAut P} {S : Subgroup P} (hS : S ≤ autFixed α)
    (hSn : (S.subgroupOf (autFixed α)).Normal) :
    S.map (MulAut.conj : P →* MulAut P) ≤ inner P ⊓ centralizer {α} ∧
      ((S.map (MulAut.conj : P →* MulAut P)).subgroupOf (inner P ⊓ centralizer {α})).Normal := by
  refine ⟨?_, ⟨fun x hx y => ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact mem_inf.2 ⟨⟨s, rfl⟩, (conj_mem_centralizer_iff hconj α s).2 (hS hs)⟩
  · rw [mem_subgroupOf] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨p, hp⟩, hpC⟩ := mem_inf.1 y.2
    have hpfix : p ∈ autFixed α := (conj_mem_centralizer_iff hconj α p).1 (by rw [hp]; exact hpC)
    have h1 := hSn.conj_mem ⟨s, hS hs⟩ (mem_subgroupOf.2 hs) ⟨p, hpfix⟩
    rw [mem_subgroupOf] at h1
    refine ⟨p * s * p⁻¹, h1, ?_⟩
    rw [map_mul, map_mul, map_inv, hp, hsx]
    rfl

theorem map_fixed_transport {D : Type*} [Group D] (η : D ≃* P) {α : MulAut D} {S : Subgroup D}
    (hS : S ≤ autFixed α) (hSn : (S.subgroupOf (autFixed α)).Normal) {α' : MulAut P}
    (hα' : ∀ x, α' x = η (α (η.symm x))) :
    S.map η.toMonoidHom ≤ autFixed α' ∧
      ((S.map η.toMonoidHom).subgroupOf (autFixed α')).Normal := by
  have hfix : ∀ y, y ∈ autFixed α' ↔ η.symm y ∈ autFixed α := fun y => by
    rw [mem_autFixed, mem_autFixed, hα', ← η.symm.injective.eq_iff, MulEquiv.symm_apply_apply]
  refine ⟨?_, ⟨fun x hx y => ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [hfix]
    change η.symm (η s) ∈ autFixed α
    rw [MulEquiv.symm_apply_apply]
    exact hS hs
  · rw [mem_subgroupOf] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    have hd : η.symm (y : P) ∈ autFixed α := (hfix _).1 y.2
    have h1 := hSn.conj_mem ⟨s, hS hs⟩ (mem_subgroupOf.2 hs) ⟨_, hd⟩
    rw [mem_subgroupOf] at h1
    refine ⟨_, h1, ?_⟩
    change η (η.symm (y : P) * s * (η.symm (y : P))⁻¹) = _
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    change _ * η s * _ = _
    rw [show η s = (x : P) from hsx]
    rfl

end Small

theorem not_mem_inner_of_normal_simple_fixed {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) {K : Type*}
    [Field K] (hK : Nat.card K = 2 ^ f) {α : MulAut (projectiveSL n K)} (hα2 : α ^ 2 = 1)
    (hα1 : α ≠ 1) (hZ : center (projectiveSL n K) = ⊥) {S : Subgroup (projectiveSL n K)}
    (hS : S ≤ autFixed α) (hSn : (S.subgroupOf (autFixed α)).Normal) [IsSimpleGroup S]
    (hSnab : ∃ a b : S, a * b ≠ b * a) : α ∉ inner (projectiveSL n K) := by
  rintro ⟨x, rfl⟩
  have hconj := conj_injective_of_center_eq_bot hZ
  have hx2 : x ^ 2 = 1 := hconj (by rw [map_pow, hα2, map_one])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hox : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hfix : autFixed (MulAut.conj x) = centralizer {x} := by
    ext y
    rw [mem_autFixed, MulAut.conj_apply, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc y * x = x * y * x⁻¹ * x := by rw [h]
        _ = x * y := by group
    · intro h
      rw [← h]
      group
  rw [hfix] at hS hSn
  have : IsSimpleGroup (S.subgroupOf (centralizer {x})) :=
    (subgroupOfEquivOfLe hS).isSimpleGroup
  have hBnab : ∃ a b : S.subgroupOf (centralizer {x}), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    set e := subgroupOfEquivOfLe hS
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  exact CFSG.ComponentClassification.OutcomeLocal.even_linear_involution_centralizers_component_free
    hf (by omega) hK x hox _ ⟨isQuasisimple_of_isSimpleGroup hBnab, hSn.isSubnormal⟩

theorem even_projective_linear_involution_normal_GL3_two_fixed_model_selector {n f : ℕ}
    (hn : 2 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) {D : Type}
    [Group D] [Finite D] (η : D ≃* projectiveSL n K) {α : MulAut D} (hα : orderOf α = 2)
    {S : Subgroup D} (hSα : S ≤ autFixed α) (hSn : (S.subgroupOf (autFixed α)).Normal)
    [IsSimpleGroup S] (hSnab : ∃ a b : S, a * b ≠ b * a) (κ : S ≃* GL (Fin 3) (ZMod 2)) :
    n = 3 ∧ f = 2 ∧ S = autFixed α ∧
      α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner D ∧ Nat.card D = 20160 ∧
      ordProj[2] (Nat.card D) = 64 ∧
      ∃ (hn3 : n = 3) (_ : CharP K 2) (σ : K ≃+* K), (∀ c, σ c = c ^ 2) ∧
        Function.Injective (binaryEmbed K hn3) ∧
        (binaryEmbed K hn3).range = autFixed (fieldAut n K σ) ∧
        ∃ (B : GL (Fin n) K) (e : ℕ), e ≤ 1 ∧
          (∀ d : D, (conjAut n K B * dualAut n K ^ e) (η (α d)) =
            fieldAut n K σ ((conjAut n K B * dualAut n K ^ e) (η d))) ∧
          ∀ s : S, (conjAut n K B * dualAut n K ^ e) (η s) = binaryEmbed K hn3 (κ s) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hcardS : Nat.card S = 168 := (Nat.card_congr κ.toEquiv).trans card_GL_three_two
  obtain ⟨α', hα'⟩ : ∃ α' : MulAut (projectiveSL n K), ∀ x, α' x = η (α (η.symm x)) :=
    ⟨(η.symm.trans α).trans η, fun x => rfl⟩
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hα
    exact absurd hα (by norm_num)
  have hα'2 : α' ^ 2 = 1 := by
    ext x
    rw [pow_two, MulAut.mul_apply, hα', hα', MulEquiv.symm_apply_apply, ← MulAut.mul_apply,
      ← pow_two, hα2, MulAut.one_apply, MulEquiv.apply_symm_apply, MulAut.one_apply]
  have hα'1 : α' ≠ 1 := by
    intro h
    apply hα1
    ext d
    have h1 := congrArg (fun φ : MulAut (projectiveSL n K) => φ (η d)) h
    simp only [hα', MulEquiv.symm_apply_apply, MulAut.one_apply] at h1
    exact η.injective h1
  obtain ⟨hS'fix, hS'n⟩ := map_fixed_transport η hSα hSn hα'
  set eS := S.equivMapOfInjective η.toMonoidHom η.injective with heS
  have : IsSimpleGroup (S.map η.toMonoidHom) := eS.symm.isSimpleGroup
  have hS'nab : ∃ a b : S.map η.toMonoidHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨eS a, eS b, fun h => hab (eS.injective (by rw [map_mul, map_mul, h]))⟩
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have h2 : n = 2 := by omega
    subst h2
    obtain ⟨h4, h2⟩ := unipotentThree_pow_four
    have hu4 : (η (κ.symm unipotentThree : D)) ^ 4 = 1 := by
      rw [← map_pow, ← SubgroupClass.coe_pow, ← map_pow, h4, map_one, OneMemClass.coe_one,
        map_one]
    have hu2 := sq_eq_one_of_pow_four_eq_one _ hu4
    apply h2
    apply κ.symm.injective
    apply Subtype.ext
    apply η.injective
    rw [map_one, OneMemClass.coe_one, map_one, map_pow, SubgroupClass.coe_pow, map_pow]
    exact hu2
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin n) K) :=
    (CFSG.LinearGroups.linear_projective_simple (by omega) (Or.inl hn3)).2.1
  have : IsSimpleGroup (projectiveSL n K) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.isSimpleGroup
  have hPnab : ∃ x y : projectiveSL n K, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hS'nab
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hZ : center (projectiveSL n K) = ⊥ := center_eq_bot_of_isSimpleGroup hPnab
  have hconj := conj_injective_of_center_eq_bot hZ
  have hout : α' ∉ inner (projectiveSL n K) :=
    not_mem_inner_of_normal_simple_fixed hn3 hf hK hα'2 hα'1 hZ hS'fix hS'n hS'nab
  obtain ⟨hTF, hTn⟩ := conj_map_le_and_normal hconj hS'fix hS'n
  set eT := (S.map η.toMonoidHom).equivMapOfInjective _ hconj with heT
  have : IsSimpleGroup ((S.map η.toMonoidHom).map
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) := eT.symm.isSimpleGroup
  have hTnab : ∃ a b : (S.map η.toMonoidHom).map
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hS'nab
    exact ⟨eT a, eT b, fun h => hab (eT.injective (by rw [map_mul, map_mul, h]))⟩
  have hcardT : Nat.card ((S.map η.toMonoidHom).map
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) = 168 := by
    rw [← Nat.card_congr eT.toEquiv, ← Nat.card_congr eS.toEquiv, hcardS]
  obtain ⟨rfl, rfl, H, σ, hσ, hα'H⟩ := even_linear_cases hn3 hf hK hα'2 hout hTF hTn hTnab hcardT
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : D ≃* projectiveSL 3 K, ∀ d, χ₀ d = (conjAut 3 K H)⁻¹ (η d) :=
    ⟨η.trans (conjAut 3 K H)⁻¹, fun d => rfl⟩
  have hχ₀α : ∀ d, χ₀ (α d) = fieldAut 3 K σ (χ₀ d) := by
    intro d
    have h1 : η (α d) = α' (η d) := by rw [hα', MulEquiv.symm_apply_apply]
    rw [hχ₀, hχ₀, h1, hα'H, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hrange : (binaryEmbed K (rfl : 3 = 3)).range = autFixed (fieldAut 3 K σ) :=
    le_antisymm (by
      rintro _ ⟨g, rfl⟩
      exact binaryEmbed_mem_autFixed K σ g) (autFixed_le_range_binaryEmbed K hσ)
  have hfixχ : ∀ d, d ∈ autFixed α ↔ χ₀ d ∈ autFixed (fieldAut 3 K σ) := fun d => by
    rw [mem_autFixed, mem_autFixed, ← hχ₀α]
    exact χ₀.injective.eq_iff.symm
  have hmapfix : (autFixed α).map χ₀.toMonoidHom = autFixed (fieldAut 3 K σ) := by
    ext y
    rw [mem_map_equiv, hfixχ, MulEquiv.apply_symm_apply]
  have hcardFix : Nat.card (autFixed α) = 168 := by
    rw [Nat.card_congr ((autFixed α).equivMapOfInjective χ₀.toMonoidHom χ₀.injective).toEquiv,
      hmapfix,
      ← hrange, card_range_binaryEmbed]
  have hSeq : S = autFixed α :=
    Subgroup.eq_of_le_of_card_ge hSα (by rw [hcardFix, hcardS])
  have hαout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner D := by
    rintro ⟨d, hd⟩
    apply hout
    refine ⟨η d, ?_⟩
    ext x
    rw [hα', ← hd, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hcardD : Nat.card D = 20160 :=
    (Nat.card_congr η.toEquiv).trans (card_projectiveSL_three_four hK4)
  have hinj := binaryEmbed_injective K
  have hmemR : ∀ s : S, χ₀ s ∈ (binaryEmbed K (rfl : 3 = 3)).range := fun s => by
    rw [hrange]
    exact (hfixχ s).1 (hSα s.2)
  set ψ : S →* (binaryEmbed K (rfl : 3 = 3)).range :=
    (χ₀.toMonoidHom.comp S.subtype).codRestrict _ hmemR with hψ
  have hψinj : Function.Injective ψ := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (χ₀.injective h1)
  have hψbij : Function.Bijective ψ := by
    refine ⟨hψinj, ?_⟩
    have := Fintype.ofFinite S
    have := Fintype.ofFinite (binaryEmbed K (rfl : 3 = 3)).range
    refine (Fintype.bijective_iff_injective_and_card ψ).2 ⟨hψinj, ?_⟩ |>.2
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardS, card_range_binaryEmbed]
  set ω : MulAut (GL (Fin 3) (ZMod 2)) :=
    (κ.symm.trans (MulEquiv.ofBijective ψ hψbij)).trans (MonoidHom.ofInjective hinj).symm with hω
  have hωκ : ∀ s : S, binaryEmbed K (rfl : 3 = 3) (ω (κ s)) = χ₀ s := by
    intro s
    rw [← MonoidHom.ofInjective_apply hinj, hω, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply]
    rfl
  obtain ⟨U, v, hv, hUv⟩ := exists_binary_form K ω
  set ω' := conjAut 3 K (GeneralLinearGroup.map (binaryHom K) U) * dualAut 3 K ^ v with hω'
  have hcomm : Commute ω'⁻¹ (fieldAut 3 K σ) := (commute_binary_form K U v σ).inv_left
  obtain ⟨B, e, he, hBe⟩ := exists_conjAut_dualAut_inv
    (H * GeneralLinearGroup.map (binaryHom K) U) hv
  have hχ : ∀ d, (conjAut 3 K B * dualAut 3 K ^ e) (η d) = ω'⁻¹ (χ₀ d) := by
    intro d
    rw [← hBe, hχ₀, map_mul, mul_assoc, ← hω', _root_.mul_inv_rev, MulAut.mul_apply]
  refine ⟨rfl, rfl, hSeq, hαout, hcardD, by rw [hcardD]; exact ordProj_two_20160, rfl, hchar, σ,
    hσ, hinj, hrange, B, e, he, fun d => ?_, fun s => ?_⟩
  · rw [hχ, hχ, hχ₀α, ← MulAut.mul_apply, hcomm.eq, MulAut.mul_apply]
  · rw [hχ, ← hωκ s, hUv, MulAut.inv_apply_self]

end CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel
