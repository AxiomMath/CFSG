module

public import CFSG.GH74.Generic.S3.ReflLin

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Filter.ClassicalOdd CFSG.ClassicalInvolution.WeakCT
  Subgroup
open scoped MatrixGroups

section M
variable {F : Type} [Field F]

@[expose] def cdSL (A : SL(2, F)) : SL(2, F) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) F) 0 0, -(A : Matrix (Fin 2) (Fin 2) F) 0 1;
      -(A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1], by
    rw [Matrix.det_fin_two_of]
    have := A.2
    rw [Matrix.det_fin_two] at this
    linear_combination this⟩

theorem coe_cdSL (A : SL(2, F)) : (cdSL A : Matrix (Fin 2) (Fin 2) F) =
    !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, -(A : Matrix (Fin 2) (Fin 2) F) 0 1;
      -(A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1] := rfl

theorem blk_conj_d (A : SL(2, F)) :
    blockSL F 3 2 0 (by omega) (-1) * blockSL F 3 2 1 (by omega) A *
        (blockSL F 3 2 0 (by omega) (-1))⁻¹ =
      blockSL F 3 2 1 (by omega) (cdSL A) := by
  rw [inv_eq_of_mul_eq_one_right blk0_neg_one_sq]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_blockSL_three_zero, coe_blockSL_three_one, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, coe_cdSL]

end M

theorem exists_refl_action_lin {G : Type} [Group G] {F : Type} [Field F] [Finite F] {z u : G}
    {Y : Fin 3 → Subgroup G} (h : GLS.LU.IsLinearA3Neighborhood F z u Y) (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) :
    ∃ ι : SL(2, F) →* G, Function.Injective ι ∧ ι.range = Y 2 ∧
      ∀ A : SL(2, F), u * ι A * u⁻¹ = ι (cdSL A) := by
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  obtain ⟨hcomm, hpair⟩ := h.comm_pairs (by rw [hF]; omega) h2
  obtain ⟨-, hz0, hz2, hu1, -⟩ := h
  obtain ⟨Fam, hFam⟩ := CFSG.GH74.L5U5.exists_ctFamily_of_pairs_ge_three (X := G) (K := F)
    (by rw [hF]; omega) (n := 3) (by norm_num) hcomm hpair
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
  refine ⟨Fam.ι 2, (hFam 2).2, (hFam 2).1, fun A => ?_⟩
  calc u * Fam.ι 2 A * u⁻¹
      = Fam.θ 1 (blockSL F 3 2 0 (by omega) (-1) * blockSL F 3 2 1 (by omega) A *
          (blockSL F 3 2 0 (by omega) (-1))⁻¹) := by
        rw [map_mul, map_mul, map_inv, hum, hθ2' A]
    _ = Fam.θ 1 (blockSL F 3 2 1 (by omega) (cdSL A)) := by rw [blk_conj_d A]
    _ = Fam.ι 2 (cdSL A) := hθ2' _

theorem not_inner_lin {G : Type} [Group G] {F : Type} [Field F] [Finite F] {z u : G}
    {Y : Fin 3 → Subgroup G} (h : GLS.LU.IsLinearA3Neighborhood F z u Y) (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 3) :
    ¬ ∃ x₀ ∈ Y 2, ∀ g ∈ Y 2, u * g * u⁻¹ = x₀ * g * x₀⁻¹ := by
  obtain ⟨ι, hinj, hrange, hact⟩ := exists_refl_action_lin h p f hp hp2 hF hq
  rintro ⟨x₀, hx₀, hall⟩
  rw [← hrange] at hx₀
  obtain ⟨A₀, rfl⟩ := hx₀
  let T : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have hTι : ι (cdSL T) = ι (A₀ * T * A₀⁻¹) := by
    have h1 := hact T
    have h2 := hall (ι T) (by rw [← hrange]; exact ⟨T, rfl⟩)
    rw [map_mul, map_mul, map_inv]
    rw [← h1, h2]
  have hTe : cdSL T = A₀ * T * A₀⁻¹ := hinj hTι
  have hTm : (cdSL T : Matrix (Fin 2) (Fin 2) F) * (A₀ : Matrix (Fin 2) (Fin 2) F) =
      (A₀ : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) := by
    have : cdSL T * A₀ = A₀ * T := by rw [hTe]; group
    simpa [Matrix.SpecialLinearGroup.coe_mul] using congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) this
  rw [coe_cdSL] at hTm
  have e00 := congrFun (congrFun hTm 0) 0
  have e01 := congrFun (congrFun hTm 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, T] at e00 e01
  have hdet := A₀.2
  rw [Matrix.det_fin_two] at hdet
  have hsq : IsSquare (-1 : F) := by
    refine ⟨(A₀ : Matrix (Fin 2) (Fin 2) F) 0 0, ?_⟩
    linear_combination hdet + ((A₀ : Matrix (Fin 2) (Fin 2) F) 0 1) * e00 +
      ((A₀ : Matrix (Fin 2) (Fin 2) F) 0 0) * e01
  have : Fintype F := Fintype.ofFinite F
  have h34 := (FiniteField.isSquare_neg_one_iff (F := F)).1 hsq
  rw [← Nat.card_eq_fintype_card, hF] at h34
  exact h34 hq4

end CFSG.GH74.Generic.S3
