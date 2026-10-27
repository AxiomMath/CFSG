module

public import CFSG.GH74.Generic.S3.Rank5
public import CFSG.GH74.GLS.LU.Ident

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Filter.ClassicalOdd CFSG.ClassicalInvolution.WeakCT
  Subgroup
open scoped MatrixGroups

section M
variable {F : Type} [Field F]

@[expose] def s0 (ι : F) (hι : ι ^ 2 = -1) : SL(2, F) :=
  ⟨!![ι, 0; 0, -ι], by rw [Matrix.det_fin_two_of]; linear_combination (-1 : F) * hι⟩

theorem coe_s0 (ι : F) (hι : ι ^ 2 = -1) : (s0 ι hι : Matrix (Fin 2) (Fin 2) F) = !![ι, 0; 0, -ι] := rfl

theorem s0_mul_self (ι : F) (hι : ι ^ 2 = -1) : s0 ι hι * s0 ι hι = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_s0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hι

theorem blk0_neg_one_sq : (blockSL F 3 2 0 (by omega) (-1)) * (blockSL F 3 2 0 (by omega) (-1)) = 1 := by
  rw [← map_mul]
  have : (-1 : SL(2, F)) * (-1) = 1 := by apply Subtype.ext; simp
  rw [this, map_one]

theorem blk_conj (ι : F) (hι : ι ^ 2 = -1) (A : SL(2, F)) :
    blockSL F 3 2 0 (by omega) (-1) * blockSL F 3 2 1 (by omega) A *
        (blockSL F 3 2 0 (by omega) (-1))⁻¹ =
      blockSL F 3 2 1 (by omega) (s0 ι hι * A * (s0 ι hι)⁻¹) := by
  rw [inv_eq_of_mul_eq_one_right blk0_neg_one_sq]
  apply Subtype.ext
  have hι0 : ι ≠ 0 := by
    intro h; rw [h] at hι; simp at hι
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_blockSL_three_zero, coe_blockSL_three_one, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, coe_s0, Matrix.vecMul, dotProduct] <;>
    first
      | linear_combination ((A : Matrix (Fin 2) (Fin 2) F) 0 0) * hι
      | linear_combination (-((A : Matrix (Fin 2) (Fin 2) F) 0 1)) * hι
      | linear_combination (-((A : Matrix (Fin 2) (Fin 2) F) 1 0)) * hι
      | linear_combination ((A : Matrix (Fin 2) (Fin 2) F) 1 1) * hι


theorem central_inv_eq_neg_one {G : Type} [Group G] (ι : SL(2, F) →* G)
    (hinj : Function.Injective ι) {c : G} (hc : c ∈ ι.range) (hord : orderOf c = 2)
    (hcc : ∀ y ∈ ι.range, y * c = c * y) : c = ι (-1) := by
  obtain ⟨A, rfl⟩ := hc
  have hA : A ∈ center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply hinj
    rw [map_mul, map_mul]
    exact hcc _ ⟨B, rfl⟩
  rcases sl2_center_eq hA with rfl | rfl
  · exfalso
    rw [map_one, orderOf_one] at hord
    omega
  · rfl

end M

theorem exists_refl_conj_lin {G : Type} [Group G] {F : Type} [Field F] [Finite F] {z u : G}
    {Y : Fin 3 → Subgroup G} (h : GLS.LU.IsLinearA3Neighborhood F z u Y) (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 1) :
    ∃ j ∈ Y 2, j * j = z ∧ ∀ g ∈ Y 2, u * g * u⁻¹ = j * g * j⁻¹ := by
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have h4 : 4 ∣ Nat.card F - 1 := by rw [hF]; omega
  obtain ⟨u0, hu0⟩ := exists_units_orderOf (F := F) (d := 4) h4
  have hu4 : u0 ^ 4 = 1 := hu0 ▸ pow_orderOf_eq_one u0
  have hu2 : u0 ^ 2 ≠ 1 := by
    intro h'
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hu0] at this
    omega
  have hι : ((u0 : F)) ^ 2 = -1 := by
    have h1 : ((u0 : F) ^ 2) * ((u0 : F) ^ 2) = 1 := by
      rw [← pow_add]
      have := congrArg Units.val hu4
      simpa using this
    rcases mul_self_eq_one_iff.1 h1 with h' | h'
    · exfalso
      apply hu2
      apply Units.ext
      simpa using h'
    · exact h'
  obtain ⟨hcomm, hpair⟩ := h.comm_pairs (by rw [hF]; omega) h2
  obtain ⟨-, hz0, hz2, hu1, -⟩ := h
  obtain ⟨Fam, hFam⟩ := CFSG.GH74.L5U5.exists_ctFamily_of_pairs_ge_three (X := G) (K := F)
    (by rw [hF]; omega) (n := 3) (by norm_num) hcomm hpair
  have hz : z = Fam.ι 2 (-1) :=
    central_inv_eq_neg_one (Fam.ι 2) (hFam 2).2 ((hFam 2).1 ▸ hz2.1) hz2.2.1
      (fun y hy => hz2.2.2 y ((hFam 2).1 ▸ hy))
  have hu : u = Fam.ι 1 (-1) :=
    central_inv_eq_neg_one (Fam.ι 1) (hFam 1).2 ((hFam 1).1 ▸ hu1.1) hu1.2.1
      (fun y hy => hu1.2.2 y ((hFam 1).1 ▸ hy))
  have hθ1 := Fam.left 1 (by norm_num)
  have hθ2 := Fam.right 1 (by norm_num)
  have hθ2' : ∀ A, Fam.θ 1 (blockSL F 3 2 1 (by omega) A) = Fam.ι 2 A := fun A =>
    DFunLike.congr_fun hθ2 A
  have hum : Fam.θ 1 (blockSL F 3 2 0 (by omega) (-1)) = u := by
    have := DFunLike.congr_fun hθ1 (-1)
    rw [MonoidHom.comp_apply] at this
    rw [this, hu]
  refine ⟨Fam.ι 2 (s0 (u0 : F) hι), ?_, ?_, ?_⟩
  · rw [← (hFam 2).1]
    exact ⟨_, rfl⟩
  · rw [← map_mul, s0_mul_self, ← hz]
  · intro g hg
    rw [← (hFam 2).1] at hg
    obtain ⟨A, rfl⟩ := hg
    calc u * Fam.ι 2 A * u⁻¹
        = Fam.θ 1 (blockSL F 3 2 0 (by omega) (-1) * blockSL F 3 2 1 (by omega) A *
            (blockSL F 3 2 0 (by omega) (-1))⁻¹) := by
          rw [map_mul, map_mul, map_inv, hum, hθ2' A]
      _ = Fam.θ 1 (blockSL F 3 2 1 (by omega) (s0 (u0 : F) hι * A * (s0 (u0 : F) hι)⁻¹)) := by
          rw [blk_conj (u0 : F) hι A]
      _ = Fam.ι 2 (s0 (u0 : F) hι * A * (s0 (u0 : F) hι)⁻¹) := hθ2' _
      _ = Fam.ι 2 (s0 (u0 : F) hι) * Fam.ι 2 A * (Fam.ι 2 (s0 (u0 : F) hι))⁻¹ := by
          rw [map_mul, map_mul, map_inv]

end CFSG.GH74.Generic.S3
