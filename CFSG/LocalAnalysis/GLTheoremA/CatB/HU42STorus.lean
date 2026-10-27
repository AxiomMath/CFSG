module

public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.Unitary.Finite
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S

open Matrix CFSG.Open

section Basic

variable {K : Type} [Field K] [Finite K]

theorem units_pow_three (hK : Nat.card K = 4) (c : Kˣ) : c ^ 3 = 1 := by
  have h : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hd : orderOf c ∣ 3 := by
    rw [← h]
    exact orderOf_dvd_natCard c
  exact orderOf_dvd_iff_pow_eq_one.1 hd

theorem card_units_eq_three (hK : Nat.card K = 4) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]

theorem diag_mul_inv_aux (a : Fin 6 → Kˣ) :
    Matrix.diagonal (fun i => (a i : K)) * Matrix.diagonal (fun i => (((a i)⁻¹ : Kˣ) : K)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp

theorem diag_inv_mul_aux (a : Fin 6 → Kˣ) :
    Matrix.diagonal (fun i => (((a i)⁻¹ : Kˣ) : K)) * Matrix.diagonal (fun i => (a i : K)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp

@[expose] def diagGL (a : Fin 6 → Kˣ) : GL (Fin 6) K :=
  ⟨Matrix.diagonal (fun i => (a i : K)), Matrix.diagonal (fun i => (((a i)⁻¹ : Kˣ) : K)),
    diag_mul_inv_aux a, diag_inv_mul_aux a⟩

theorem diagGL_val (a : Fin 6 → Kˣ) :
    ((diagGL a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal (fun i => (a i : K)) :=
  rfl

@[expose] def diagHom : (Fin 6 → Kˣ) →* GL (Fin 6) K where
  toFun := diagGL
  map_one' := by
    apply Units.ext
    simp [diagGL_val]
  map_mul' a b := by
    apply Units.ext
    simp [diagGL_val, Matrix.diagonal_mul_diagonal]

@[expose] def prodHom : (Fin 6 → Kˣ) →* Kˣ where
  toFun a := ∏ i, a i
  map_one' := by simp
  map_mul' a b := by
    simp [Finset.prod_mul_distrib]

abbrev T₀ : Subgroup (Fin 6 → Kˣ) := MonoidHom.ker (prodHom (K := K))

theorem mem_T₀ {a : Fin 6 → Kˣ} : a ∈ T₀ (K := K) ↔ ∏ i, a i = 1 := by
  rw [MonoidHom.mem_ker]
  rfl

end Basic

section SU

variable {K : Type} [Field K] [Finite K]

theorem diagGL_mem_SU (hK : Nat.card K = 4) {a : Fin 6 → Kˣ} (ha : ∏ i, a i = 1) :
    diagGL a ∈ StatedSU 6 (2 ^ 1) K := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [diagGL_val, Matrix.det_diagonal]
    have hprod : ∏ i, (a i : K) = ((∏ i, a i : Kˣ) : K) :=
      (map_prod (Units.coeHom K) (fun i => a i) Finset.univ).symm
    rw [hprod, ha, Units.val_one]
  · rw [diagGL_val]
    rw [Matrix.diagonal_map (by simp), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    have hc : ∀ i, ((a i : K)) ^ (2 ^ 1) * (a i : K) = 1 := by
      intro i
      have h3 : ((a i : K)) ^ 3 = 1 := by
        have := congrArg Units.val (units_pow_three hK (a i))
        simpa [Units.val_pow_eq_pow_val] using this
      calc ((a i : K)) ^ (2 ^ 1) * (a i : K) = (a i : K) ^ 3 := by ring
        _ = 1 := h3
    simp only [hc]
    simp

theorem scalar_eq_diagGL (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c = diagGL (fun _ => c) := by
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.GeneralLinearGroup.scalar, diagGL_val]
  · simp [Matrix.GeneralLinearGroup.scalar, diagGL_val, Matrix.diagonal_apply, h]

theorem scalar_mem_SU (hK : Nat.card K = 4) (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ StatedSU 6 (2 ^ 1) K := by
  rw [scalar_eq_diagGL]
  apply diagGL_mem_SU hK
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h3 := units_pow_three hK c
  calc c ^ 6 = (c ^ 3) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [h3, one_pow]

end SU

section Torus

variable {K : Type} [Field K] [Finite K]

abbrev TT (K : Type) [Field K] [Finite K] : Type := ↥(T₀ (K := K))

@[expose] def torusY (hK : Nat.card K = 4) : TT K →* StatedSU 6 (2 ^ 1) K :=
  MonoidHom.codRestrict ((diagHom (K := K)).comp (T₀ (K := K)).subtype) _
    (fun a => diagGL_mem_SU hK (mem_T₀.1 a.2))

theorem torusY_apply (hK : Nat.card K = 4) (a : TT K) :
    ((torusY hK a : StatedSU 6 (2 ^ 1) K) : GL (Fin 6) K) = diagGL a.1 :=
  rfl

theorem diag_entry (a : Fin 6 → Kˣ) (i : Fin 6) :
    ((diagGL a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = (a i : K) := by
  simp [diagGL_val, Matrix.diagonal_apply]

theorem torusY_injective (hK : Nat.card K = 4) : Function.Injective (torusY hK) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply Units.ext
  have ha := congrArg (fun g : StatedSU 6 (2 ^ 1) K =>
    (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i)) hab
  change ((diagGL a.1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i =
    ((diagGL b.1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i at ha
  rw [diag_entry, diag_entry] at ha
  exact ha

abbrev W6 (hK : Nat.card K = 4) : Subgroup (StatedSU 6 (2 ^ 1) K) := (torusY hK).range

abbrev T₁ (K : Type) [Field K] [Finite K] : Subgroup (TT K) :=
  MonoidHom.ker ((Pi.evalMonoidHom (fun _ : Fin 6 => Kˣ) 0).comp (T₀ (K := K)).subtype)

abbrev W4 (hK : Nat.card K = 4) : Subgroup (StatedSU 6 (2 ^ 1) K) :=
  ((torusY hK).comp (T₁ K).subtype).range

@[expose] def scalY (hK : Nat.card K = 4) : Kˣ →* StatedSU 6 (2 ^ 1) K :=
  MonoidHom.codRestrict (Matrix.GeneralLinearGroup.scalar (Fin 6)) _ (scalar_mem_SU hK)

abbrev scalSub (hK : Nat.card K = 4) : Subgroup (StatedSU 6 (2 ^ 1) K) := (scalY hK).range

theorem scalY_injective (hK : Nat.card K = 4) : Function.Injective (scalY hK) := by
  intro c d h
  have h' := congrArg (fun g : StatedSU 6 (2 ^ 1) K => ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 0 0) h
  simp [scalY, Matrix.GeneralLinearGroup.scalar] at h'
  exact Units.ext h'

end Torus

section Counts

variable {K : Type} [Field K] [Finite K]

theorem card_range_of_injective' {G H : Type} [Group G] [Finite G] [Group H] (f : G →* H)
    (hf : Function.Injective f) : Nat.card f.range = Nat.card G := by
  have h := Subgroup.card_ker_mul_card_range f
  rw [(MonoidHom.ker_eq_bot_iff f).2 hf, Subgroup.card_bot, one_mul] at h
  exact h

theorem card_fun_six (hK : Nat.card K = 4) : Nat.card (Fin 6 → Kˣ) = 3 ^ 6 := by
  rw [Nat.card_fun, card_units_eq_three hK]
  simp

theorem prodHom_surjective : Function.Surjective (prodHom (K := K)) := by
  intro c
  refine ⟨fun i => if i = 0 then c else 1, ?_⟩
  simp [prodHom]

theorem card_T₀ (hK : Nat.card K = 4) : Nat.card (T₀ (K := K)) = 3 ^ 5 := by
  have h := Subgroup.card_ker_mul_card_range (prodHom (K := K))
  rw [MonoidHom.range_eq_top.2 prodHom_surjective, Subgroup.card_top, card_fun_six hK,
    card_units_eq_three hK] at h
  have h3 : (3 : ℕ) ^ 6 = 3 ^ 5 * 3 := by norm_num
  rw [h3] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem card_TT (hK : Nat.card K = 4) : Nat.card (TT K) = 3 ^ 5 := card_T₀ hK

theorem card_W6 (hK : Nat.card K = 4) : Nat.card (W6 hK) = 3 ^ 5 := by
  rw [W6, card_range_of_injective' (torusY hK) (torusY_injective hK), card_TT hK]

theorem eval_zero_surjective :
    Function.Surjective ((Pi.evalMonoidHom (fun _ : Fin 6 => Kˣ) 0).comp (T₀ (K := K)).subtype) := by
  intro c
  refine ⟨⟨fun i => if i = 0 then c else if i = 1 then c⁻¹ else 1, ?_⟩, ?_⟩
  · rw [mem_T₀]
    simp [Fin.prod_univ_six]
  · simp

theorem card_T₁ (hK : Nat.card K = 4) : Nat.card (T₁ K) = 3 ^ 4 := by
  have h := Subgroup.card_ker_mul_card_range
    ((Pi.evalMonoidHom (fun _ : Fin 6 => Kˣ) 0).comp (T₀ (K := K)).subtype)
  rw [MonoidHom.range_eq_top.2 eval_zero_surjective, Subgroup.card_top, card_TT hK,
    card_units_eq_three hK] at h
  have h3 : (3 : ℕ) ^ 5 = 3 ^ 4 * 3 := by norm_num
  rw [h3] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem card_scalSub (hK : Nat.card K = 4) : Nat.card (scalSub hK) = 3 := by
  rw [scalSub, card_range_of_injective' (scalY hK) (scalY_injective hK), card_units_eq_three hK]

end Counts

section Elem

variable {K : Type} [Field K] [Finite K]

theorem isMulCommutative_range {G H : Type} [CommGroup G] [Group H] (f : G →* H) :
    IsMulCommutative f.range :=
  ⟨⟨fun x y => by
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]⟩⟩

theorem pow_three_TT (hK : Nat.card K = 4) (a : TT K) : a ^ 3 = 1 := by
  apply Subtype.ext
  funext i
  simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
  exact units_pow_three hK _

theorem isElemAbelian_range_of_cube {G H : Type} [CommGroup G] [Group H] (f : G →* H)
    (h3 : ∀ a : G, a ^ 3 = 1) : CFSG.Open.IsElemAbelian 3 f.range := by
  refine ⟨isMulCommutative_range f, ?_⟩
  intro x hx
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
  rw [← map_pow, h3 a, map_one]

theorem W6_isElemAbelian (hK : Nat.card K = 4) : CFSG.Open.IsElemAbelian 3 (W6 hK) :=
  isElemAbelian_range_of_cube (torusY hK) (pow_three_TT hK)

theorem scalSub_le_center (hK : Nat.card K = 4) :
    scalSub hK ≤ Subgroup.center (StatedSU 6 (2 ^ 1) K) := by
  rintro y ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈
      Subgroup.center (GL (Fin 6) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  apply Subtype.ext
  have := (Subgroup.mem_center_iff.1 hz) (g : GL (Fin 6) K)
  simpa [scalY] using this

theorem mem_scalSub_iff (hK : Nat.card K = 4) (y : StatedSU 6 (2 ^ 1) K) :
    y ∈ scalSub hK ↔ ((y : GL (Fin 6) K)) ∈ StatedScalars (Fin 6) K := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, Subtype.ext ?_⟩
    simpa [scalY] using hc

theorem scalY_apply (hK : Nat.card K = 4) (c : Kˣ) :
    ((scalY hK c : StatedSU 6 (2 ^ 1) K) : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c :=
  rfl

theorem scalar_entry (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 0 0
      = (c : K) := by
  rw [scalar_eq_diagGL, diag_entry]

theorem W4_inf_scalSub (hK : Nat.card K = 4) {y : StatedSU 6 (2 ^ 1) K} (hW : y ∈ W4 hK)
    (hs : y ∈ scalSub hK) : y = 1 := by
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hW
  obtain ⟨c, hc⟩ := hs
  have ht0 : (t.1.1 0 : Kˣ) = 1 := by
    have h := t.2
    rw [MonoidHom.mem_ker] at h
    simpa using h
  have hc1 : c = 1 := by
    apply Units.ext
    have h1 := congrArg (fun g : StatedSU 6 (2 ^ 1) K =>
      (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 0 0)) hc
    simp only [scalY_apply, scalar_entry] at h1
    have h2 : (((((torusY hK).comp (T₁ K).subtype) t : StatedSU 6 (2 ^ 1) K) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) 0 0 = ((t.1.1 0 : Kˣ) : K) := by
      change (((torusY hK t.1 : StatedSU 6 (2 ^ 1) K) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) 0 0 = _
      rw [torusY_apply, diag_entry]
    rw [h2, ht0, Units.val_one] at h1
    exact h1
  rw [← hc, hc1, map_one]

end Elem

end CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S
