module

public import CFSG.LieType.SeitzGeneration.HeisTorusIdent
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {ℓ f : ℕ} {K : Type} [Field K]

instance ug81_neZero (r : ℕ) [Fact r.Prime] : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩

section Character

variable {r : ℕ} {ζ : K}

@[expose] def ug81_psi [NeZero r] (hζ : IsPrimitiveRoot ζ r) : AddChar (ZMod r) K where
  toFun x := ζ ^ x.val
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    show ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hζ.pow_eq_one).symm

theorem ug81_psi_apply [NeZero r] (hζ : IsPrimitiveRoot ζ r) (x : ZMod r) :
    ug81_psi hζ x = ζ ^ x.val := rfl

theorem ug81_psi_natCast [NeZero r] (hζ : IsPrimitiveRoot ζ r) (n : ℕ) :
    ug81_psi hζ (n : ZMod r) = ζ ^ n := by
  rw [ug81_psi_apply, ZMod.val_natCast]
  exact (pow_eq_pow_mod n hζ.pow_eq_one).symm

theorem ug81_psi_one [NeZero r] (hζ : IsPrimitiveRoot ζ r) (hr : 2 ≤ r) :
    ug81_psi hζ 1 = ζ := by
  rw [ug81_psi_apply, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < r), pow_one]

theorem ug81_prod_psi [NeZero r] (hζ : IsPrimitiveRoot ζ r) {ι : Type*} (s : Finset ι)
    (g : ι → ZMod r) : ∏ i ∈ s, ug81_psi hζ (g i) = ug81_psi hζ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, AddChar.map_add_eq_mul]

theorem ug81_sum_fin [NeZero r] {M : Type*} [AddCommMonoid M] (g : ZMod r → M) :
    ∑ i : Fin r, g ((i : ℕ) : ZMod r) = ∑ x : ZMod r, g x := by
  refine Fintype.sum_bijective (fun i : Fin r => ((i : ℕ) : ZMod r)) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j hij => ?_, by rw [Fintype.card_fin, ZMod.card]⟩
  have h := (ZMod.natCast_eq_natCast_iff' (i : ℕ) (j : ℕ) r).mp hij
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at h
  exact Fin.ext h

theorem ug81_natCast_inj [NeZero r] {i j : Fin r} :
    ((i : ℕ) : ZMod r) = ((j : ℕ) : ZMod r) ↔ i = j := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt, Fin.ext_iff]

theorem ug81_natCast_ne_zero [NeZero r] {n : ℕ} (hn : 0 < n) (hnr : n < r) :
    (n : ZMod r) ≠ 0 := by
  intro h
  exact absurd (Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n r).mp h)) (by omega)

theorem ug81_sum_char [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (t : ZMod r) :
    ∑ x : ZMod r, ug81_psi hζ (x * t) = if t = 0 then (r : K) else 0 := by
  split_ifs with ht
  · subst ht
    simp [ZMod.card]
  · have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
    have hst : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
    have h1 : ∑ x : ZMod r, ug81_psi hζ (x * t) =
        ∑ x : ZMod r, ug81_psi hζ ((x + t⁻¹) * t) :=
      (Equiv.sum_comp (Equiv.addRight t⁻¹) (fun y : ZMod r => ug81_psi hζ (y * t))).symm
    have h2 : ∑ x : ZMod r, ug81_psi hζ ((x + t⁻¹) * t) =
        ug81_psi hζ (t⁻¹ * t) * ∑ x : ZMod r, ug81_psi hζ (x * t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by rw [add_mul, AddChar.map_add_eq_mul]; ring)
    rw [hst, ug81_psi_one hζ hr2] at h2
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
    have h3 : (1 - ζ) * ∑ x : ZMod r, ug81_psi hζ (x * t) = 0 := by
      linear_combination h1 + h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4).symm hζ1
    · exact h4

theorem ug81_gauss [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) {b : ZMod r}
    (hb : b ≠ 0) (t : ZMod r) :
    ∑ x : ZMod r, ug81_psi hζ (b * x * x + t * x) =
      ug81_psi hζ (-(t * t) / (4 * b)) * ∑ x : ZMod r, ug81_psi hζ (b * x * x) := by
  have h2 : (2 : ZMod r) ≠ 0 := by
    exact_mod_cast ug81_natCast_ne_zero (by norm_num) (by omega : 2 < r)
  have h4 : (4 : ZMod r) ≠ 0 := by
    exact_mod_cast ug81_natCast_ne_zero (by norm_num) (by omega : 4 < r)
  have hkey : ∀ x : ZMod r, b * (x + -t / (2 * b)) * (x + -t / (2 * b)) +
      t * (x + -t / (2 * b)) = b * x * x + -(t * t) / (4 * b) := by
    intro x
    field_simp
    ring
  calc ∑ x : ZMod r, ug81_psi hζ (b * x * x + t * x)
      = ∑ x : ZMod r, ug81_psi hζ (b * (x + -t / (2 * b)) * (x + -t / (2 * b)) +
          t * (x + -t / (2 * b))) :=
        (Equiv.sum_comp (Equiv.addRight (-t / (2 * b)))
          (fun y : ZMod r => ug81_psi hζ (b * y * y + t * y))).symm
    _ = ∑ x : ZMod r, ug81_psi hζ (b * x * x + -(t * t) / (4 * b)) :=
        Finset.sum_congr rfl (fun x _ => by rw [hkey x])
    _ = ∑ x : ZMod r, ug81_psi hζ (b * x * x) * ug81_psi hζ (-(t * t) / (4 * b)) :=
        Finset.sum_congr rfl (fun x _ => AddChar.map_add_eq_mul _ _ _)
    _ = ug81_psi hζ (-(t * t) / (4 * b)) * ∑ x : ZMod r, ug81_psi hζ (b * x * x) := by
        rw [← Finset.sum_mul, mul_comm]

theorem ug81_sum_sq [Fact r.Prime] (hr : 5 ≤ r) : ∑ x : ZMod r, x * x = 0 := by
  have h2 : (2 : ZMod r) ≠ 0 := by
    exact_mod_cast ug81_natCast_ne_zero (by norm_num) (by omega : 2 < r)
  have h3 : (3 : ZMod r) ≠ 0 := by
    exact_mod_cast ug81_natCast_ne_zero (by norm_num) (by omega : 3 < r)
  have hone : ∑ _x : ZMod r, (1 : ZMod r) = 0 := by simp [ZMod.card]
  have hA : ∑ x : ZMod r, (x + 1) * (x + 1) = ∑ x : ZMod r, x * x :=
    Equiv.sum_comp (Equiv.addRight 1) (fun y : ZMod r => y * y)
  have hB : ∑ x : ZMod r, (x + 1) ^ 3 = ∑ x : ZMod r, x ^ 3 :=
    Equiv.sum_comp (Equiv.addRight 1) (fun y : ZMod r => y ^ 3)
  have hA0 : ∑ x : ZMod r, ((x + 1) * (x + 1) - x * x) = 0 := by
    rw [Finset.sum_sub_distrib, hA, sub_self]
  have hB0 : ∑ x : ZMod r, ((x + 1) ^ 3 - x ^ 3) = 0 := by
    rw [Finset.sum_sub_distrib, hB, sub_self]
  have hA2 : ∑ x : ZMod r, ((x + 1) * (x + 1) - x * x) =
      2 * ∑ x : ZMod r, x + ∑ _x : ZMod r, (1 : ZMod r) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have hB2 : ∑ x : ZMod r, ((x + 1) ^ 3 - x ^ 3) =
      3 * ∑ x : ZMod r, x * x + 3 * ∑ x : ZMod r, x + ∑ _x : ZMod r, (1 : ZMod r) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have hS1 : ∑ x : ZMod r, x = 0 := by
    have h : 2 * ∑ x : ZMod r, x = 0 := by linear_combination hA0 - hA2 - hone
    exact (mul_eq_zero.mp h).resolve_left h2
  have hS2 : ∑ x : ZMod r, x * x = 0 := by
    have h : 3 * ∑ x : ZMod r, x * x = 0 := by
      linear_combination hB0 - hB2 - 3 * hS1 - hone
    exact (mul_eq_zero.mp h).resolve_left h3
  exact hS2

theorem ug81_sum_exp [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (T e : ZMod r) :
    ∑ k : Fin r, ug81_psi hζ (T * ((k : ℕ) : ZMod r) + e) =
      (if T = 0 then (r : K) else 0) * ug81_psi hζ e := by
  have h1 : ∀ k : Fin r, ug81_psi hζ (T * ((k : ℕ) : ZMod r) + e) =
      ug81_psi hζ (((k : ℕ) : ZMod r) * T) * ug81_psi hζ e := by
    intro k
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.sum_mul]
  congr 1
  exact (ug81_sum_fin (fun y : ZMod r => ug81_psi hζ (y * T))).trans (ug81_sum_char hζ T)

theorem ug81_bar_psi (h : UnitaryFieldData ℓ f K) (hrq : r ∣ ℓ ^ f + 1) [NeZero r]
    (hζ : IsPrimitiveRoot ζ r) (x : ZMod r) :
    h.bar (ug81_psi hζ x) = ug81_psi hζ (-x) := by
  have hq : ((ℓ ^ f : ℕ) : ZMod r) = -1 := by
    have h0 := (ZMod.natCast_eq_zero_iff (ℓ ^ f + 1) r).mpr hrq
    rw [Nat.cast_add, Nat.cast_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  rw [UnitaryFieldData.bar_apply, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hq, neg_one_mul]

end Character

section Matrices

variable {r : ℕ} {ζ : K}

@[expose] def ug81_chirp [NeZero r] (hζ : IsPrimitiveRoot ζ r) (b : ZMod r) :
    Matrix (Fin r) (Fin r) K :=
  Matrix.diagonal fun j : Fin r => ug81_psi hζ (b * ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r))

@[expose] noncomputable def ug81_conj [NeZero r] (hζ : IsPrimitiveRoot ζ r) (b : ZMod r) :
    Matrix (Fin r) (Fin r) K :=
  (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) * ug81_chirp hζ b *
    (heisFourierMat ζ : Matrix (Fin r) (Fin r) K)⁻¹

@[expose] def ug81_G [NeZero r] (hζ : IsPrimitiveRoot ζ r) (b : ZMod r) : K :=
  ∑ x : ZMod r, ug81_psi hζ (b * x * x)

theorem ug81_fourier_entry [NeZero r] (hζ : IsPrimitiveRoot ζ r) (i j : Fin r) :
    (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) i j =
      ug81_psi hζ (((i : ℕ) : ZMod r) * ((j : ℕ) : ZMod r)) := by
  rw [← Nat.cast_mul, ug81_psi_natCast]
  rfl

theorem ug81_fourier_inv_entry [NeZero r] (hζ : IsPrimitiveRoot ζ r) (hr : 2 ≤ r) (m k : Fin r) :
    (heisFourierMat ζ : Matrix (Fin r) (Fin r) K)⁻¹ m k =
      (r : K)⁻¹ * ug81_psi hζ (-(((m : ℕ) : ZMod r) * ((k : ℕ) : ZMod r))) := by
  rw [heisFourierMat_inv hζ hr, Matrix.of_apply, AddChar.map_neg_eq_inv, ← Nat.cast_mul,
    ug81_psi_natCast]

theorem ug81_conj_entry [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 2 ≤ r) (b : ZMod r)
    (i k : Fin r) : ug81_conj hζ b i k = (r : K)⁻¹ * ∑ x : ZMod r,
      ug81_psi hζ (b * x * x + (((i : ℕ) : ZMod r) - ((k : ℕ) : ZMod r)) * x) := by
  have hterm : ∀ m : Fin r,
      (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) i m * ug81_psi hζ
          (b * ((m : ℕ) : ZMod r) * ((m : ℕ) : ZMod r)) *
        (heisFourierMat ζ : Matrix (Fin r) (Fin r) K)⁻¹ m k =
      (r : K)⁻¹ * ug81_psi hζ (b * ((m : ℕ) : ZMod r) * ((m : ℕ) : ZMod r) +
        (((i : ℕ) : ZMod r) - ((k : ℕ) : ZMod r)) * ((m : ℕ) : ZMod r)) := by
    intro m
    rw [ug81_fourier_entry hζ, ug81_fourier_inv_entry hζ hr]
    have e : ug81_psi hζ (b * ((m : ℕ) : ZMod r) * ((m : ℕ) : ZMod r) +
        (((i : ℕ) : ZMod r) - ((k : ℕ) : ZMod r)) * ((m : ℕ) : ZMod r)) =
        ug81_psi hζ (((i : ℕ) : ZMod r) * ((m : ℕ) : ZMod r)) *
          ug81_psi hζ (b * ((m : ℕ) : ZMod r) * ((m : ℕ) : ZMod r)) *
          ug81_psi hζ (-(((m : ℕ) : ZMod r) * ((k : ℕ) : ZMod r))) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [e]
    ring
  unfold ug81_conj
  rw [Matrix.mul_apply]
  simp only [ug81_chirp, Matrix.mul_diagonal]
  rw [Finset.mul_sum]
  exact (Finset.sum_congr rfl (fun m _ => hterm m)).trans
    (ug81_sum_fin (fun x : ZMod r => (r : K)⁻¹ * ug81_psi hζ
      (b * x * x + (((i : ℕ) : ZMod r) - ((k : ℕ) : ZMod r)) * x)))

theorem ug81_conj_closed [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) {b : ZMod r}
    (hb : b ≠ 0) (i k : Fin r) :
    ug81_conj hζ b i k = (r : K)⁻¹ * (ug81_psi hζ
      (-((((i : ℕ) : ZMod r) - ((k : ℕ) : ZMod r)) * (((i : ℕ) : ZMod r) - ((k : ℕ) : ZMod r))) /
        (4 * b)) * ug81_G hζ b) := by
  rw [ug81_conj_entry hζ (by omega) b i k, ug81_gauss hζ hr hb, ug81_G]

end Matrices

section Unitary

variable {r : ℕ} {ζ : K}

theorem ug81_fourier_unitary [Fact r.Prime] (h : UnitaryFieldData ℓ f K) (hrq : r ∣ ℓ ^ f + 1)
    (hζ : IsPrimitiveRoot ζ r) :
    ((heisFourierMat ζ : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ *
      (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) = (r : K) • 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  simp only [Matrix.transpose_apply, Matrix.map_apply, ug81_fourier_entry hζ,
    ug81_bar_psi h hrq hζ]
  have hterm : ∀ i : Fin r, ug81_psi hζ (-(((i : ℕ) : ZMod r) * ((j : ℕ) : ZMod r))) *
      ug81_psi hζ (((i : ℕ) : ZMod r) * ((k : ℕ) : ZMod r)) =
      ug81_psi hζ (((i : ℕ) : ZMod r) * (((k : ℕ) : ZMod r) - ((j : ℕ) : ZMod r))) := by
    intro i
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  refine (ug81_sum_fin (fun y : ZMod r =>
    ug81_psi hζ (y * (((k : ℕ) : ZMod r) - ((j : ℕ) : ZMod r))))).trans ?_
  rw [ug81_sum_char hζ]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hne : ((k : ℕ) : ZMod r) - ((j : ℕ) : ZMod r) ≠ 0 := fun h0 =>
      hjk (ug81_natCast_inj.mp (sub_eq_zero.mp h0).symm)
    rw [if_neg hne, if_neg hjk]

theorem ug81_chirp_unitary [NeZero r] (h : UnitaryFieldData ℓ f K) (hrq : r ∣ ℓ ^ f + 1)
    (hζ : IsPrimitiveRoot ζ r) (b : ZMod r) :
    ((ug81_chirp hζ b).map h.bar)ᵀ * ug81_chirp hζ b = 1 := by
  unfold ug81_chirp
  rw [Matrix.diagonal_map (_root_.map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.one_apply, Function.comp_apply, ug81_bar_psi h hrq hζ]
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem ug81_unitary_conj {n : ℕ} (h : UnitaryFieldData ℓ f K) (F D : Matrix (Fin n) (Fin n) K)
    (r0 : K) (hF : IsUnit F.det) (hFF : (F.map h.bar)ᵀ * F = r0 • 1)
    (hD : (D.map h.bar)ᵀ * D = 1) :
    ((F * D * F⁻¹).map h.bar)ᵀ * (F * D * F⁻¹) = 1 := by
  have hFF' : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hF
  have hstar : ((F⁻¹).map h.bar)ᵀ * (F.map h.bar)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hFF', Matrix.map_one _
      (_root_.map_zero h.bar) (_root_.map_one h.bar), Matrix.transpose_one]
  have e1 : ((F * D * F⁻¹).map h.bar)ᵀ =
      ((F⁻¹).map h.bar)ᵀ * ((D.map h.bar)ᵀ * (F.map h.bar)ᵀ) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  rw [e1]
  calc ((F⁻¹).map h.bar)ᵀ * ((D.map h.bar)ᵀ * (F.map h.bar)ᵀ) * (F * D * F⁻¹)
      = ((F⁻¹).map h.bar)ᵀ * ((D.map h.bar)ᵀ * ((F.map h.bar)ᵀ * F) * D) * F⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((F⁻¹).map h.bar)ᵀ * ((D.map h.bar)ᵀ * (r0 • 1) * D) * F⁻¹ := by rw [hFF]
    _ = ((F⁻¹).map h.bar)ᵀ * (r0 • 1) * F⁻¹ := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hD]
    _ = ((F⁻¹).map h.bar)ᵀ * ((F.map h.bar)ᵀ * F) * F⁻¹ := by rw [hFF]
    _ = ((F⁻¹).map h.bar)ᵀ * (F.map h.bar)ᵀ * (F * F⁻¹) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hstar, hFF', Matrix.one_mul]

theorem ug81_conj_unitary [Fact r.Prime] (h : UnitaryFieldData ℓ f K) (hrq : r ∣ ℓ ^ f + 1)
    (hζ : IsPrimitiveRoot ζ r) (b : ZMod r) :
    ((ug81_conj hζ b).map h.bar)ᵀ * ug81_conj hζ b = 1 := by
  unfold ug81_conj
  exact ug81_unitary_conj h _ _ _ (isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ))
    (ug81_fourier_unitary h hrq hζ) (ug81_chirp_unitary h hrq hζ b)

theorem ug81_det_chirp [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) (b : ZMod r) :
    (ug81_chirp hζ b).det = 1 := by
  have hs : ∑ j : Fin r, b * ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r) = 0 := by
    have e1 : ∑ j : Fin r, b * ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r) =
        ∑ j : Fin r, b * (((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r)) :=
      Finset.sum_congr rfl (fun j _ => mul_assoc _ _ _)
    have e2 : ∑ j : Fin r, ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r) =
        ∑ x : ZMod r, x * x := ug81_sum_fin (fun x : ZMod r => x * x)
    rw [e1, ← Finset.mul_sum, e2, ug81_sum_sq hr, mul_zero]
  unfold ug81_chirp
  rw [Matrix.det_diagonal, ug81_prod_psi hζ, hs, AddChar.map_zero_eq_one]

theorem ug81_det_conj [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) (b : ZMod r) :
    (ug81_conj hζ b).det = 1 := by
  have hF : (heisFourierMat ζ : Matrix (Fin r) (Fin r) K).det ≠ 0 :=
    det_heisFourierMat_ne_zero hζ
  unfold ug81_conj
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    ug81_det_chirp hζ hr b, mul_one, mul_inv_cancel₀ hF]

end Unitary

section GLSection

variable {r : ℕ} {ζ : K}

@[expose] noncomputable def ug81GLChirp [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r)
    (b : ZMod r) : GL (Fin r) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (ug81_chirp hζ b)
    (by rw [ug81_det_chirp hζ hr b]; exact one_ne_zero)

@[expose] noncomputable def ug81GLConj [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r)
    (b : ZMod r) : GL (Fin r) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (ug81_conj hζ b)
    (by rw [ug81_det_conj hζ hr b]; exact one_ne_zero)

theorem ug81GLChirp_val [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) (b : ZMod r) :
    (ug81GLChirp hζ hr b : Matrix (Fin r) (Fin r) K) = ug81_chirp hζ b := rfl

theorem ug81GLConj_val [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) (b : ZMod r) :
    (ug81GLConj hζ hr b : Matrix (Fin r) (Fin r) K) = ug81_conj hζ b := rfl

theorem ug81GLChirp_mem [Fact r.Prime] (h : UnitaryFieldData ℓ f K) (hrq : r ∣ ℓ ^ f + 1)
    (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) (b : ZMod r) :
    ug81GLChirp hζ hr b ∈ unitarySU ℓ f K r := by
  rw [mem_unitarySU_iff h]
  exact ⟨ug81_det_chirp hζ hr b, ug81_chirp_unitary h hrq hζ b⟩

theorem ug81GLConj_mem [Fact r.Prime] (h : UnitaryFieldData ℓ f K) (hrq : r ∣ ℓ ^ f + 1)
    (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) (b : ZMod r) :
    ug81GLConj hζ hr b ∈ unitarySU ℓ f K r := by
  rw [mem_unitarySU_iff h]
  exact ⟨ug81_det_conj hζ hr b, ug81_conj_unitary h hrq hζ b⟩

theorem ug81GLConj_fourier [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) (b : ZMod r) :
    (ug81GLConj hζ hr b : Matrix (Fin r) (Fin r) K) *
        (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) =
      (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) *
        Matrix.diagonal fun j : Fin r =>
          ug81_psi hζ (b * ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r)) := by
  have hF : IsUnit (heisFourierMat ζ : Matrix (Fin r) (Fin r) K).det :=
    isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ)
  show ug81_conj hζ b * (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) =
    (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) * ug81_chirp hζ b
  unfold ug81_conj
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hF, Matrix.mul_one]

end GLSection

section Perm

variable {r : ℕ} {ζ : K}

@[expose] def ug81MulFun (r k : ℕ) (j : Fin r) : Fin r :=
  ⟨(k * (j : ℕ)) % r, Nat.mod_lt _ j.pos⟩

theorem ug81MulFun_injective (r : ℕ) [Fact r.Prime] {k : ℕ} (hk : ¬ r ∣ k) :
    Function.Injective (ug81MulFun r k) := by
  intro i j hij
  have h1 : (k * (i : ℕ)) % r = (k * (j : ℕ)) % r := congrArg Fin.val hij
  have hcop : Nat.gcd r k = 1 := (Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)).mpr hk
  have h2 : (i : ℕ) ≡ (j : ℕ) [MOD r] := Nat.ModEq.cancel_left_of_coprime hcop h1
  apply Fin.ext
  have h3 : (i : ℕ) % r = (j : ℕ) % r := h2
  rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at h3

@[expose] noncomputable def mulPerm (r : ℕ) [Fact r.Prime] (k : ℕ) (hk : ¬ r ∣ k) :
    Equiv.Perm (Fin r) :=
  Equiv.ofBijective (ug81MulFun r k)
    (Finite.injective_iff_bijective.mp (ug81MulFun_injective r hk))

theorem mulPerm_val [Fact r.Prime] (k : ℕ) (hk : ¬ r ∣ k) (i : Fin r) :
    ((mulPerm r k hk i : Fin r) : ℕ) = (k * (i : ℕ)) % r := rfl

theorem mulPerm_apply_eq_iff [Fact r.Prime] (k : ℕ) (hk : ¬ r ∣ k) (i j : Fin r) :
    mulPerm r k hk i = j ↔ ((j : ℕ) : ZMod r) = ((k : ℕ) : ZMod r) * ((i : ℕ) : ZMod r) := by
  have key : (k * (i : ℕ)) % r = (j : ℕ) ↔
      ((k * (i : ℕ) : ℕ) : ZMod r) = ((j : ℕ) : ZMod r) := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt]
  rw [Fin.ext_iff, mulPerm_val, key, Nat.cast_mul, eq_comm]

theorem ug81_perm_entry (σ : Equiv.Perm (Fin r)) (i j : Fin r) :
    Equiv.Perm.permMatrix K σ i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

end Perm

section Word

variable {r : ℕ} {ζ : K}

@[expose] def ug81T [Fact r.Prime] (kk i j : ZMod r) : ZMod r := i / 2 - j / (2 * kk)

@[expose] def ug81E [Fact r.Prime] (kk i j : ZMod r) : ZMod r :=
  -(kk * i * i) / 4 + j * j / (4 * kk)

theorem ug81T_mul [Fact r.Prime] {kk : ZMod r} (hkk : kk ≠ 0) (h2 : (2 : ZMod r) ≠ 0)
    (i j : ZMod r) : ug81T kk i j * (2 * kk) = kk * i - j := by
  unfold ug81T
  field_simp

theorem ug81_exponent [Fact r.Prime] {kk : ZMod r} (hkk : kk ≠ 0) (h2 : (2 : ZMod r) ≠ 0)
    (h4 : (4 : ZMod r) ≠ 0) (i j x : ZMod r) :
    (1 - kk) / 4 * i * i + -((i - x) * (i - x)) / (4 * 1) +
      (kk - 1) / (4 * kk) * x * x + -((x - j) * (x - j)) / (4 * -kk) =
      ug81T kk i j * x + ug81E kk i j := by
  unfold ug81T ug81E
  field_simp
  ring

theorem ug81_word_entry [Fact r.Prime] (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) {kk : ZMod r}
    (hkk : kk ≠ 0) (i j : Fin r) :
    (ug81_chirp hζ ((1 - kk) / 4) * ug81_conj hζ 1 * ug81_chirp hζ ((kk - 1) / (4 * kk)) *
      ug81_conj hζ (-kk)) i j =
    (r : K)⁻¹ * (ug81_G hζ 1 * ug81_G hζ (-kk)) *
      (if ((j : ℕ) : ZMod r) = kk * ((i : ℕ) : ZMod r) then 1 else 0) := by
  have h2 : (2 : ZMod r) ≠ 0 := by
    exact_mod_cast ug81_natCast_ne_zero (by norm_num) (by omega : 2 < r)
  have h4 : (4 : ZMod r) ≠ 0 := by
    exact_mod_cast ug81_natCast_ne_zero (by norm_num) (by omega : 4 < r)
  have hrK : (r : K) ≠ 0 := heis_natCast_ne_zero hζ (by omega)
  have hnk : -kk ≠ 0 := neg_ne_zero.mpr hkk
  have hexp : (ug81_chirp hζ ((1 - kk) / 4) * ug81_conj hζ 1 * ug81_chirp hζ ((kk - 1) / (4 * kk)) *
      ug81_conj hζ (-kk)) i j = ∑ k : Fin r,
      ug81_psi hζ ((1 - kk) / 4 * ((i : ℕ) : ZMod r) * ((i : ℕ) : ZMod r)) * ug81_conj hζ 1 i k *
        ug81_psi hζ ((kk - 1) / (4 * kk) * ((k : ℕ) : ZMod r) * ((k : ℕ) : ZMod r)) *
        ug81_conj hζ (-kk) k j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [ug81_chirp, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hsum : ∀ k : Fin r,
      ug81_psi hζ ((1 - kk) / 4 * ((i : ℕ) : ZMod r) * ((i : ℕ) : ZMod r)) * ug81_conj hζ 1 i k *
        ug81_psi hζ ((kk - 1) / (4 * kk) * ((k : ℕ) : ZMod r) * ((k : ℕ) : ZMod r)) *
        ug81_conj hζ (-kk) k j =
      (r : K)⁻¹ * (r : K)⁻¹ * (ug81_G hζ 1 * ug81_G hζ (-kk)) *
        ug81_psi hζ (ug81T kk ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r) * ((k : ℕ) : ZMod r) +
          ug81E kk ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r)) := by
    intro k
    rw [ug81_conj_closed hζ hr one_ne_zero i k, ug81_conj_closed hζ hr hnk k j]
    have e : ug81_psi hζ ((1 - kk) / 4 * ((i : ℕ) : ZMod r) * ((i : ℕ) : ZMod r)) *
        ug81_psi hζ (-((((i : ℕ) : ZMod r) - ((k : ℕ) : ZMod r)) *
          (((i : ℕ) : ZMod r) - ((k : ℕ) : ZMod r))) / (4 * 1)) *
        ug81_psi hζ ((kk - 1) / (4 * kk) * ((k : ℕ) : ZMod r) * ((k : ℕ) : ZMod r)) *
        ug81_psi hζ (-((((k : ℕ) : ZMod r) - ((j : ℕ) : ZMod r)) *
          (((k : ℕ) : ZMod r) - ((j : ℕ) : ZMod r))) / (4 * -kk)) =
        ug81_psi hζ (ug81T kk ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r) * ((k : ℕ) : ZMod r) +
          ug81E kk ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      exact congrArg (ug81_psi hζ) (ug81_exponent hkk h2 h4 ((i : ℕ) : ZMod r)
        ((j : ℕ) : ZMod r) ((k : ℕ) : ZMod r))
    rw [← e]
    ring
  rw [hexp, Finset.sum_congr rfl (fun k _ => hsum k), ← Finset.mul_sum,
    ug81_sum_exp hζ]
  by_cases hc : ((j : ℕ) : ZMod r) = kk * ((i : ℕ) : ZMod r)
  · have hT0 : ug81T kk ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r) = 0 := by
      have hm := ug81T_mul hkk h2 ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r)
      have hm2 : ug81T kk ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r) * (2 * kk) = 0 := by
        rw [hm, hc, sub_self]
      exact (mul_eq_zero.mp hm2).resolve_right (mul_ne_zero h2 hkk)
    have hE0 : ug81E kk ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r) = 0 := by
      unfold ug81E
      rw [hc]
      field_simp
      ring
    rw [if_pos hT0, hE0, AddChar.map_zero_eq_one, if_pos hc]
    field_simp
  · have hT0 : ug81T kk ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r) ≠ 0 := by
      intro h0
      have hm := ug81T_mul hkk h2 ((i : ℕ) : ZMod r) ((j : ℕ) : ZMod r)
      rw [h0, zero_mul] at hm
      exact hc (by linear_combination hm)
    rw [if_neg hT0, if_neg hc]
    simp

theorem ug81_shift_mem (h : UnitaryFieldData ℓ f K) {r : ℕ} [Fact r.Prime] (hr : 5 ≤ r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ r) (H : Subgroup (GL (Fin r) K))
    (hTw : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → g ∈ H) :
    ∃ g ∈ H, (g : Matrix (Fin r) (Fin r) K) = heisShiftMat K r := by
  have hodd : Odd r := (Fact.out : r.Prime).odd_of_ne_two (by omega)
  have hdet : (heisShiftMat K r).det = 1 := det_heisShiftMat K hodd
  have hbar : (heisShiftMat K r).map h.bar = heisShiftMat K r := by
    ext i j
    rw [Matrix.map_apply, heisShiftMat_entry]
    split_ifs <;> simp
  have hunit : ((heisShiftMat K r).map h.bar)ᵀ * heisShiftMat K r = 1 := by
    rw [hbar, heisShiftMat, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul,
      mul_inv_cancel, Matrix.permMatrix_one]
  let g : GL (Fin r) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (heisShiftMat K r)
    (by rw [hdet]; exact one_ne_zero)
  have hg : g ∈ unitarySU ℓ f K r := by
    rw [mem_unitarySU_iff h]
    exact ⟨hdet, hunit⟩
  exact ⟨g, hTw g hg ⟨fun j => ζ ^ (j : ℕ), heisShiftMat_mul_heisFourierMat hζ.pow_eq_one⟩, rfl⟩

theorem ug81_mult_mem (h : UnitaryFieldData ℓ f K) {r : ℕ} [Fact r.Prime] (hr : 5 ≤ r)
    (hrq : r ∣ ℓ ^ f + 1) {ζ : K} (hζ : IsPrimitiveRoot ζ r) (H : Subgroup (GL (Fin r) K))
    (hT : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) = diagonal t) → g ∈ H)
    (hTw : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → g ∈ H)
    (k : ℕ) (hk : ¬ r ∣ k) :
    ∃ c : K, ∃ g ∈ H,
      (g : Matrix (Fin r) (Fin r) K) = c • (Equiv.Perm.permMatrix K (mulPerm r k hk)) := by
  set kk : ZMod r := ((k : ℕ) : ZMod r) with hkk_def
  have hkk : kk ≠ 0 := fun h0 => hk ((ZMod.natCast_eq_zero_iff k r).mp h0)
  have hA : ug81GLChirp hζ hr ((1 - kk) / 4) ∈ H :=
    hT _ (ug81GLChirp_mem h hrq hζ hr _)
      ⟨fun j => ug81_psi hζ ((1 - kk) / 4 * ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r)), rfl⟩
  have hB : ug81GLConj hζ hr 1 ∈ H :=
    hTw _ (ug81GLConj_mem h hrq hζ hr 1)
      ⟨fun j => ug81_psi hζ (1 * ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r)),
        ug81GLConj_fourier hζ hr 1⟩
  have hC : ug81GLChirp hζ hr ((kk - 1) / (4 * kk)) ∈ H :=
    hT _ (ug81GLChirp_mem h hrq hζ hr _)
      ⟨fun j => ug81_psi hζ ((kk - 1) / (4 * kk) * ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r)), rfl⟩
  have hD : ug81GLConj hζ hr (-kk) ∈ H :=
    hTw _ (ug81GLConj_mem h hrq hζ hr _)
      ⟨fun j => ug81_psi hζ (-kk * ((j : ℕ) : ZMod r) * ((j : ℕ) : ZMod r)),
        ug81GLConj_fourier hζ hr _⟩
  refine ⟨(r : K)⁻¹ * (ug81_G hζ 1 * ug81_G hζ (-kk)),
    ug81GLChirp hζ hr ((1 - kk) / 4) * ug81GLConj hζ hr 1 *
      ug81GLChirp hζ hr ((kk - 1) / (4 * kk)) * ug81GLConj hζ hr (-kk),
    H.mul_mem (H.mul_mem (H.mul_mem hA hB) hC) hD, ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [Units.val_mul, ug81GLChirp_val, ug81GLConj_val]
  rw [ug81_word_entry hζ hr hkk i j, Matrix.smul_apply, smul_eq_mul, ug81_perm_entry]
  by_cases hc : ((j : ℕ) : ZMod r) = kk * ((i : ℕ) : ZMod r)
  · rw [if_pos hc, if_pos ((mulPerm_apply_eq_iff k hk i j).mpr hc)]
  · rw [if_neg hc, if_neg (fun h' => hc ((mulPerm_apply_eq_iff k hk i j).mp h'))]

end Word

end CFSG.LieType.SeitzGeneration

end
