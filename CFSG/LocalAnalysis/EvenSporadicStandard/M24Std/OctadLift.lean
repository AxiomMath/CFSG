module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NoLift4

public section

namespace CFSG.EvenSporadicStandard.M24Std.Octad

open Subgroup CFSG.EvenSporadicStandard.M23Std

section Eps

variable {Y : Type*} [CommGroup Y]

@[expose] def eps4 (y : Fin 4 → Y) (a : Fin 4 → ZMod 4) : Y := ∏ i, y i ^ (a i).val

theorem eps4_zero (y : Fin 4 → Y) : eps4 y 0 = 1 := by simp [eps4]

theorem eps4_add {y : Fin 4 → Y} (hy : ∀ i, y i ^ 4 = 1) (a b : Fin 4 → ZMod 4) :
    eps4 y (a + b) = eps4 y a * eps4 y b := by
  unfold eps4
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hy i)]

theorem eps4_nsmul {y : Fin 4 → Y} (hy : ∀ i, y i ^ 4 = 1) (n : ℕ) (a : Fin 4 → ZMod 4) :
    eps4 y (n • a) = eps4 y a ^ n := by
  induction n with
  | zero => simp [eps4_zero]
  | succ n ih => rw [succ_nsmul, eps4_add hy, ih, pow_succ]

theorem eps4_sum {y : Fin 4 → Y} (hy : ∀ i, y i ^ 4 = 1) {ι : Type*} (s : Finset ι)
    (f : ι → Fin 4 → ZMod 4) : eps4 y (∑ j ∈ s, f j) = ∏ j ∈ s, eps4 y (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eps4_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, eps4_add hy, ih]

theorem eps4_castHom {y : Fin 4 → Y} (hy : ∀ i, y i ^ 2 = 1) (a : Fin 4 → ZMod 4) :
    eps4 y a = ∏ i, y i ^ (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (a i)).val := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, pow_eq_pow_mod _ (hy i)]

theorem eps4_single (y : Fin 4 → Y) (i : Fin 4) : eps4 y (Pi.single i 1) = y i := by
  unfold eps4
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same]
    rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Eps

structure LiftSetting4 {Y : Type*} [CommGroup Y] (U : Subgroup Y) (φ : Y →* Y)
    (e : Fin 4 → Y) : Prop where
  φ_mem : ∀ y, φ y ∈ U
  φ_one : ∀ u ∈ U, φ u = 1
  ker_le : ∀ y, φ y = 1 → y ∈ U
  surj : ∀ u ∈ U, ∃ y, φ y = u
  U_sq : ∀ u ∈ U, u * u = 1
  sq_mem : ∀ y : Y, y * y ∈ U
  sq_eq_one : ∀ y : Y, y * y = 1 → y ∈ U
  card_U : Nat.card U = 2 ^ 4
  e_mem : ∀ i, e i ∈ U
  e_inj : ∀ c d : Fin 4 → ZMod 2, (∏ i, e i ^ (c i).val) = ∏ i, e i ^ (d i).val → c = d

namespace LiftSetting4

variable {Y : Type*} [CommGroup Y] {U : Subgroup Y} {φ : Y →* Y} {e : Fin 4 → Y}
  (h : LiftSetting4 U φ e)
include h

theorem pow_four (y : Y) : y ^ 4 = 1 := by
  calc y ^ 4 = (y * y) * (y * y) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    _ = 1 := h.U_sq _ (h.sq_mem y)

theorem pow_two_of_mem {u : Y} (hu : u ∈ U) : u ^ 2 = 1 := by
  rw [sq]; exact h.U_sq u hu

theorem ker_eq : φ.ker = U := by
  ext y
  rw [MonoidHom.mem_ker]
  exact ⟨h.ker_le y, h.φ_one y⟩

theorem range_eq : φ.range = U := by
  ext u
  constructor
  · rintro ⟨y, rfl⟩
    exact h.φ_mem y
  · intro hu
    obtain ⟨y, hy⟩ := h.surj u hu
    exact ⟨y, hy⟩

theorem card_Y : Nat.card Y = 2 ^ 8 := by
  have := Subgroup.card_ker_mul_card_range φ
  rw [h.ker_eq, h.range_eq, h.card_U] at this
  rw [← this]
  norm_num

theorem sq_surj [Finite Y] (u : Y) (hu : u ∈ U) : ∃ y : Y, y * y = u := by
  let f : Y →* Y := powMonoidHom 2
  have hker : f.ker = U := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro hy
      exact h.sq_eq_one y (by simpa [f, sq] using hy)
    · intro hy
      simpa [f, sq] using h.U_sq y hy
  have hle : f.range ≤ U := by
    rintro _ ⟨y, rfl⟩
    simpa [f, sq] using h.sq_mem y
  have hc := Subgroup.card_ker_mul_card_range f
  rw [hker, h.card_U, h.card_Y] at hc
  have hr : Nat.card f.range = 2 ^ 4 := by
    have : 2 ^ 4 * Nat.card f.range = 2 ^ 4 * 2 ^ 4 := by rw [hc]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have heq : f.range = U := Subgroup.eq_of_le_of_card_ge hle (by rw [hr, h.card_U])
  rw [← heq] at hu
  obtain ⟨y, hy⟩ := hu
  exact ⟨y, by simpa [f, sq] using hy⟩

theorem e_surj [Finite Y] (u : Y) (hu : u ∈ U) :
    ∃ c : Fin 4 → ZMod 2, ∏ i, e i ^ (c i).val = u := by
  let f : (Fin 4 → ZMod 2) → U := fun c =>
    ⟨∏ i, e i ^ (c i).val, prod_mem fun i _ => pow_mem (h.e_mem i) _⟩
  have hf : Function.Injective f := fun c d hcd => h.e_inj c d (congrArg Subtype.val hcd)
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by
      rw [h.card_U, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4),
        Fintype.card_fin])
  obtain ⟨c, hc⟩ := hbij.2 ⟨u, hu⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem exists_lift : ∃ yy : Fin 4 → Y, ∀ i, φ (yy i) = e i := by
  choose yy hyy using fun i => h.surj (e i) (h.e_mem i)
  exact ⟨yy, hyy⟩

omit h in
theorem phi_eps {yy : Fin 4 → Y} (hyy : ∀ i, φ (yy i) = e i) (a : Fin 4 → ZMod 4) :
    φ (eps4 yy a) = eps4 e a := by
  unfold eps4
  simp only [map_prod, map_pow, hyy]

theorem eps4_surjective [Finite Y] {yy : Fin 4 → Y} (hyy : ∀ i, φ (yy i) = e i) :
    Function.Surjective (eps4 yy) := by
  have hy4 : ∀ i, yy i ^ 4 = 1 := fun i => h.pow_four _
  have h1 : ∀ y : Y, ∃ a, φ (eps4 yy a) = φ y := by
    intro y
    obtain ⟨c, hc⟩ := h.e_surj (φ y) (h.φ_mem y)
    refine ⟨fun i => ((c i).val : ZMod 4), ?_⟩
    rw [phi_eps hyy, ← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast_of_lt]
    exact lt_of_lt_of_le (ZMod.val_lt _) (by norm_num)
  intro y
  obtain ⟨a, ha⟩ := h1 y
  have hu : y * (eps4 yy a)⁻¹ ∈ U := h.ker_le _ (by rw [map_mul, map_inv, ha, mul_inv_cancel])
  obtain ⟨w, hw⟩ := h.sq_surj _ hu
  obtain ⟨b, hb⟩ := h1 w
  have hw' : w * (eps4 yy b)⁻¹ ∈ U := h.ker_le _ (by rw [map_mul, map_inv, hb, mul_inv_cancel])
  have hww : w * w = eps4 yy b * eps4 yy b := by
    have h2 : (w / eps4 yy b) ^ 2 = 1 := by rw [div_eq_mul_inv, sq]; exact h.U_sq _ hw'
    rw [div_pow, div_eq_one] at h2
    simpa [sq] using h2
  refine ⟨a + (b + b), ?_⟩
  rw [eps4_add hy4, eps4_add hy4, ← hww, hw, mul_comm y, mul_inv_cancel_left]

theorem eps4_bijective [Finite Y] {yy : Fin 4 → Y} (hyy : ∀ i, φ (yy i) = e i) :
    Function.Bijective (eps4 yy) :=
  (eps4_surjective h hyy).bijective_of_nat_card_le (by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
      h.card_Y]
    norm_num)

end LiftSetting4

section Rep

variable {Y : Type*} [CommGroup Y]

theorem exists_rep {yy : Fin 4 → Y} (hy : ∀ i, yy i ^ 4 = 1)
    (hsurj : Function.Surjective (eps4 yy)) (σ : Y →* Y) :
    ∃ A : Matrix (Fin 4) (Fin 4) (ZMod 4), ∀ a, σ (eps4 yy a) = eps4 yy (Matrix.vecMul a A) := by
  choose r hr using fun j => hsurj (σ (yy j))
  refine ⟨Matrix.of r, fun a => ?_⟩
  have h1 : σ (eps4 yy a) = ∏ j, (σ (yy j)) ^ (a j).val := by
    unfold eps4
    simp only [map_prod, map_pow]
  rw [h1, Matrix.vecMul_eq_sum, eps4_sum hy]
  refine Finset.prod_congr rfl fun j _ => ?_
  have : a j • (Matrix.of r) j = (a j).val • r j := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 4), ZMod.natCast_zmod_val]
    rfl
  rw [this, eps4_nsmul hy, hr]

theorem rep_comp {yy : Fin 4 → Y} {σ₁ σ₂ : Y →* Y}
    {A₁ A₂ : Matrix (Fin 4) (Fin 4) (ZMod 4)}
    (h₁ : ∀ a, σ₁ (eps4 yy a) = eps4 yy (Matrix.vecMul a A₁))
    (h₂ : ∀ a, σ₂ (eps4 yy a) = eps4 yy (Matrix.vecMul a A₂)) (a : Fin 4 → ZMod 4) :
    σ₁ (σ₂ (eps4 yy a)) = eps4 yy (Matrix.vecMul a (A₂ * A₁)) := by
  rw [h₂, h₁, Matrix.vecMul_vecMul]

theorem mul_eq_one_of_comp {yy : Fin 4 → Y}
    (hinj : Function.Injective (eps4 yy)) {σ₁ σ₂ : Y →* Y}
    {A₁ A₂ : Matrix (Fin 4) (Fin 4) (ZMod 4)}
    (h₁ : ∀ a, σ₁ (eps4 yy a) = eps4 yy (Matrix.vecMul a A₁))
    (h₂ : ∀ a, σ₂ (eps4 yy a) = eps4 yy (Matrix.vecMul a A₂)) (hcomp : ∀ y, σ₁ (σ₂ y) = y) :
    A₂ * A₁ = 1 := by
  have key : ∀ a, Matrix.vecMul a (A₂ * A₁) = a := fun a =>
    hinj (by rw [← rep_comp h₁ h₂, hcomp])
  ext i j
  have h1 := Matrix.single_one_vecMul i (A₂ * A₁)
  have h3 := Matrix.single_one_vecMul i (1 : Matrix (Fin 4) (Fin 4) (ZMod 4))
  rw [Matrix.vecMul_one] at h3
  have : (A₂ * A₁).row i = (1 : Matrix (Fin 4) (Fin 4) (ZMod 4)).row i := by
    rw [← h1, key, h3]
  exact congrFun this j

theorem rep_map_castHom {U : Subgroup Y} {φ : Y →* Y} {e : Fin 4 → Y} (h : LiftSetting4 U φ e)
    {yy : Fin 4 → Y} (hyy : ∀ i, φ (yy i) = e i) {σ : Y →* Y}
    (hσφ : ∀ y, φ (σ y) = σ (φ y)) {S : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hσe : ∀ i, σ (e i) = ∏ j, e j ^ (S i j).val) {A : Matrix (Fin 4) (Fin 4) (ZMod 4)}
    (hA : ∀ a, σ (eps4 yy a) = eps4 yy (Matrix.vecMul a A)) :
    A.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = S := by
  ext i j
  have h1 : σ (yy i) = eps4 yy (A i) := by
    have := hA (Pi.single i 1)
    rwa [eps4_single, Matrix.single_one_vecMul] at this
  have h2 : (∏ k, e k ^ (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (A i k)).val) =
      ∏ k, e k ^ (S i k).val := by
    rw [← eps4_castHom (fun k => h.pow_two_of_mem (h.e_mem k)), ← LiftSetting4.phi_eps hyy, ← h1,
      hσφ, hyy, hσe]
  exact congrFun (h.e_inj _ _ h2) j

theorem LiftSetting4.false_of_involutions [Finite Y] {U : Subgroup Y} {φ : Y →* Y}
    {e : Fin 4 → Y} (h : LiftSetting4 U φ e) (σ τ : Y →* Y)
    (hσσ : ∀ y, σ (σ y) = y) (hττ : ∀ y, τ (τ y) = y) (hστ : ∀ y, σ (τ (σ (τ y))) = y)
    (hσφ : ∀ y, φ (σ y) = σ (φ y)) (hτφ : ∀ y, φ (τ y) = τ (φ y))
    (hσe : ∀ i, σ (e i) = ∏ j, e j ^ (liftA1 i j).val)
    (hτe : ∀ i, τ (e i) = ∏ j, e j ^ (liftA2 i j).val) : False := by
  obtain ⟨yy, hyy⟩ := h.exists_lift
  have hy4 : ∀ i, yy i ^ 4 = 1 := fun i => h.pow_four _
  have hbij := h.eps4_bijective hyy
  obtain ⟨A, hA⟩ := exists_rep hy4 hbij.2 σ
  obtain ⟨B, hB⟩ := exists_rep hy4 hbij.2 τ
  have hAA : A * A = 1 := mul_eq_one_of_comp hbij.1 hA hA hσσ
  have hBB : B * B = 1 := mul_eq_one_of_comp hbij.1 hB hB hττ
  have hρ : ∀ a, (σ.comp τ) (eps4 yy a) = eps4 yy (Matrix.vecMul a (B * A)) :=
    fun a => rep_comp hA hB a
  have hρρ : ∀ y, (σ.comp τ) ((σ.comp τ) y) = y := fun y => hστ y
  have hBABA : (B * A) * (B * A) = 1 := mul_eq_one_of_comp hbij.1 hρ hρ hρρ
  have hABAB : (A * B) * (A * B) = 1 := by
    calc (A * B) * (A * B) = (A * B) * (A * B) * (A * A) := by rw [hAA, Matrix.mul_one]
      _ = A * ((B * A) * (B * A)) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBABA, Matrix.mul_one, hAA]
  exact no_lift4 A B (rep_map_castHom h hyy hσφ hσe hA) (rep_map_castHom h hyy hτφ hτe hB) hAA
    hBB hABAB

end Rep

end CFSG.EvenSporadicStandard.M24Std.Octad
