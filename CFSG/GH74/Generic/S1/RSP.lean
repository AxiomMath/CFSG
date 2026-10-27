module

public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.ClassicalInvolution.Phan.StandardPair
public import CFSG.ClassicalInvolution.Phan.Torus

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

theorem sp_noncomm_lin {F : Type} [Field F] [Finite F] (hF : 3 ≤ Nat.card F) {X : Type} [Group X]
    {W U V : Subgroup X} (hP : LinearBlockStandardPair F W U V) {z : X} (hzU : z ∈ U)
    (hz2 : orderOf z = 2) (hzc : ∀ a ∈ U, a * z = z * a) :
    (2 : F) ≠ 0 ∧ ¬ ∀ v ∈ V, v * z = z * v := by
  have _ := hF
  obtain ⟨θ, -, hker, hU, hV⟩ := CFSG.ClassicalInvolution.WeakCT.pair_normalize hP
  obtain ⟨hi₀, hr₀, hi₁, hr₁⟩ := CFSG.ClassicalInvolution.WeakCT.pair_block_inj hker hU hV
  have hmem₀ : ∀ A : SL(2, F), θ (blockSL F 3 2 0 (by omega) A) ∈ U := fun A => by
    rw [← hr₀]; exact ⟨A, rfl⟩
  have hmem₁ : ∀ A : SL(2, F), θ (blockSL F 3 2 1 (by omega) A) ∈ V := fun A => by
    rw [← hr₁]; exact ⟨A, rfl⟩
  rw [← hr₀] at hzU
  obtain ⟨A0, hz⟩ := hzU
  subst hz
  simp only [MonoidHom.comp_apply] at hz2 hzc ⊢
  have hcent : A0 ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro A
    apply hi₀
    have := hzc _ (hmem₀ A)
    simpa [map_mul] using this
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcent
  have hA0 : A0 ≠ 1 := by
    rintro rfl
    simp at hz2
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hA0
    apply Subtype.ext
    rw [← hr]
    simp
  have hrr : r * r = 1 := by
    simpa [sq] using hr2
  have hrneg : r = -1 := by
    have h : (r - 1) * (r + 1) = 0 := by linear_combination hrr
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hr1
    · exact eq_neg_of_add_eq_zero_left h
  have h2 : (2 : F) ≠ 0 := by
    intro h
    exact hr1 (by rw [hrneg]; linear_combination (-1 : F) * h)
  refine ⟨h2, fun hall => ?_⟩
  obtain ⟨E, hE⟩ : ∃ E : SL(2, F), (E : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] :=
    ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
  have hcomm := hall _ (hmem₁ E)
  set b0 : SL(3, F) := blockSL F 3 2 0 (by omega) A0 with hb0
  set b1 : SL(3, F) := blockSL F 3 2 1 (by omega) E with hb1
  have hθ : θ (b1 * b0) = θ (b0 * b1) := by
    rw [map_mul, map_mul]
    exact hcomm
  have hmem : (b0 * b1)⁻¹ * (b1 * b0) ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, inv_mul_cancel]
  obtain ⟨s, -, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hmem)
  have hmat : ((b1 * b0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((b0 * b1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) s := by
    rw [hs, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have h00 : (A0 : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 := by
    rw [← hr, hrneg]; simp [Matrix.scalar_apply]
  have h01 : (A0 : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    rw [← hr]; simp [Matrix.scalar_apply]
  have h10 : (A0 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [← hr]; simp [Matrix.scalar_apply]
  have h11 : (A0 : Matrix (Fin 2) (Fin 2) F) 1 1 = -1 := by
    rw [← hr, hrneg]; simp [Matrix.scalar_apply]
  have hE00 : (E : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by rw [hE]; rfl
  have hE01 : (E : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by rw [hE]; rfl
  have hE10 : (E : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by rw [hE]; rfl
  have hE11 : (E : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by rw [hE]; rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hb0, hb1,
    coe_blockSL_three_zero, coe_blockSL_three_one, h00, h01, h10, h11, hE00, hE01, hE10,
    hE11] at hmat
  have e22 := congrFun (congrFun hmat 2) 2
  have e12 := congrFun (congrFun hmat 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] at e22 e12
  exact h2 (by linear_combination e22 + e12)

theorem sp_exists_normOne_mul_self_ne_one {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    ∃ s : normOne (unitaryInvolution F p f), ((s : Fˣ) : F) * ((s : Fˣ) : F) ≠ 1 := by
  by_contra h
  have h : ∀ s : normOne (unitaryInvolution F p f),
      ((s : Fˣ) : F) * ((s : Fˣ) : F) = 1 := fun s => by
    by_contra hs
    exact h ⟨s, hs⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := normOne (unitaryInvolution F p f))
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq]
    exact h g
  have hd := orderOf_dvd_of_pow_eq_one hg2
  have hle := Nat.le_of_dvd (by norm_num) hd
  rw [hg, card_normOne hF] at hle
  omega

theorem sp_su2_scalar_of_commute {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {A : Su F p f 2}
    (hA : ∀ B : Su F p f 2, B * A = A * B) :
    ∃ a : F, ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a ∧
      a * a = 1 := by
  obtain ⟨s, hs⟩ := sp_exists_normOne_mul_self_ne_one hF hq
  have h1 := congrArg (fun g : Su F p f 2 => ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (hA (torusTwo (unitaryInvolution F p f) s))
  have h2 := congrArg (fun g : Su F p f 2 => ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (hA (rotSU (unitaryInvolution F p f)))
  have hrot : (((rotSU (unitaryInvolution F p f) : Su F p f 2) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = rotMat := rfl
  simp only [Subgroup.coe_mul, Units.val_mul, coe_torusTwo, hrot] at h1 h2
  have hdet := A.2.1
  set M : Matrix (Fin 2) (Fin 2) F := ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  have e01 := congrFun (congrFun h1 0) 1
  have f00 := congrFun (congrFun h2 0) 0
  have f01 := congrFun (congrFun h2 0) 1
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal] at e01
  simp [Matrix.mul_apply, Fin.sum_univ_two, rotMat] at f00 f01
  rw [Matrix.det_fin_two] at hdet
  have hx : M 0 1 = 0 := by
    have h : (((s : Fˣ) : F) * ((s : Fˣ) : F) - 1) * M 0 1 = 0 := by
      have hs0 : ((s : Fˣ) : F) ≠ 0 := Units.ne_zero _
      field_simp at e01
      linear_combination e01
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hs
    · exact h
  have hy : M 1 0 = 0 := by linear_combination -f00 - hx
  refine ⟨M 0 0, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hx, hy, f01]
  · rw [hx, hy, f01] at hdet
    linear_combination hdet

theorem sp_noncomm_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X] {W U V : Subgroup X}
    (hP : UnitaryBlockStandardPair F p f W U V) {z : X} (hzU : z ∈ U) (hz2 : orderOf z = 2)
    (hzc : ∀ a ∈ U, a * z = z * a) : p ≠ 2 ∧ ¬ ∀ v ∈ V, v * z = z * v := by
  obtain ⟨θ, -, hker, hU, hV⟩ := CFSG.ClassicalInvolution.Phan.pair_normalize hP
  obtain ⟨hi₀, hr₀, hi₁, hr₁⟩ := CFSG.ClassicalInvolution.Phan.pair_block_inj hF hker hU hV
  have hmem₀ : ∀ A : Su F p f 2, θ (embSUid (unitaryInvolution F p f) 2 A) ∈ U := fun A => by
    rw [← hr₀]; exact ⟨A, rfl⟩
  have hmem₁ : ∀ A : Su F p f 2, θ (embSUid (unitaryInvolution F p f) 0 A) ∈ V := fun A => by
    rw [← hr₁]; exact ⟨A, rfl⟩
  rw [← hr₀] at hzU
  obtain ⟨A0, hz⟩ := hzU
  subst hz
  simp only [MonoidHom.comp_apply] at hz2 hzc ⊢
  have hcomm : ∀ B : Su F p f 2, B * A0 = A0 * B := by
    intro B
    apply hi₀
    have := hzc _ (hmem₀ B)
    simpa [map_mul] using this
  obtain ⟨a, ha, haa⟩ := sp_su2_scalar_of_commute hF hq hcomm
  have hA0 : A0 ≠ 1 := by
    rintro rfl
    simp at hz2
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hA0
    apply Subtype.ext
    apply Units.ext
    rw [ha]
    simp
  have haneg : a = -1 := by
    have h : (a - 1) * (a + 1) = 0 := by linear_combination haa
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) ha1
    · exact eq_neg_of_add_eq_zero_left h
  have h2 : (2 : F) ≠ 0 := by
    intro h
    exact ha1 (by rw [haneg]; linear_combination (-1 : F) * h)
  refine ⟨?_, fun hall => ?_⟩
  · rintro rfl
    exact h2 (by simpa using CharP.cast_eq_zero F 2)
  · have hcomm' := hall _ (hmem₁ (rotSU (unitaryInvolution F p f)))
    set b0 : Su F p f 3 := embSUid (unitaryInvolution F p f) 2 A0 with hb0
    set b1 : Su F p f 3 :=
      embSUid (unitaryInvolution F p f) 0 (rotSU (unitaryInvolution F p f)) with hb1
    have hθ : θ (b1 * b0) = θ (b0 * b1) := by
      rw [map_mul, map_mul]
      exact hcomm'
    have hmem : (b0 * b1)⁻¹ * (b1 * b0) ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, inv_mul_cancel]
    obtain ⟨u, hu⟩ := exists_scalar_of_mem_center (isUnitaryInvolution_unitaryInvolution hF)
      (le_refl 3) (hker hmem)
    have hmat : (((b1 * b0 : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (((b0 * b1 : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          Matrix.scalar (Fin 3) (u : F) := by
      rw [← hu, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
    have e00 := congrFun (congrFun hmat 0) 0
    have e12 := congrFun (congrFun hmat 1) 2
    have hrot : (((rotSU (unitaryInvolution F p f) : Su F p f 2) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = rotMat := rfl
    simp only [hb0, hb1, Subgroup.coe_mul, Units.val_mul, coe_embSUid, ha, haneg, hrot]
      at e00 e12
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, rotMat, Matrix.scalar_apply] at e00 e12
    exact h2 (by linear_combination e00 - e12)

end CFSG.GH74.Generic.S1
