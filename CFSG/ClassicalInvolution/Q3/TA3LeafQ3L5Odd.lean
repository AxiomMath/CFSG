module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Fin
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinFrame
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open CFSG CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem exists_conj_sl2 (A : GL (Fin 2) (ZMod 3)) (B : SL(2, ZMod 3)) :
    ∃ B' : SL(2, ZMod 3), Matrix.SpecialLinearGroup.toGL B' =
      A * Matrix.SpecialLinearGroup.toGL B * A⁻¹ := by
  have h1 : Matrix.GeneralLinearGroup.det (A * Matrix.SpecialLinearGroup.toGL B * A⁻¹) =
      Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL B) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  have hdet : ((A * Matrix.SpecialLinearGroup.toGL B * A⁻¹ : GL (Fin 2) (ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h1, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, B.2]
  exact ⟨⟨_, hdet⟩, Units.ext rfl⟩

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.oddCore_eq_one_of_gl2 (hD : TightDatum R S t) {N H : Subgroup Y} [N.Normal]
    (hRH : R ≤ Subgroup.centralizer (H : Set Y)) {θ : GL (Fin 2) (ZMod 3) →* Y}
    (hθ : Function.Injective θ)
    (hθr : θ.range = N ⊓ Subgroup.centralizer {t} ⊓ Subgroup.centralizer (H : Set Y))
    (hθ1 : θ (-1) = t) {o : Y} (ho : o ∈ oddCoreImg R) (hoN : o ∈ N) : o = 1 := by
  have hNn : N.Normal := inferInstance
  have hθt : ∀ A, θ A ∈ Subgroup.centralizer ({t} : Set Y) := fun A => by
    have : θ A ∈ θ.range := ⟨A, rfl⟩
    rw [hθr] at this
    exact this.1.2
  have hpull : ∀ r ∈ R, r ∈ N → ∃ A, θ A = r := fun r hr hrN => by
    have : r ∈ N ⊓ Subgroup.centralizer {t} ⊓ Subgroup.centralizer (H : Set Y) :=
      ⟨⟨hrN, hD.cent hr⟩, hRH hr⟩
    rw [← hθr] at this
    exact this
  set ψ := θ.comp Matrix.SpecialLinearGroup.toGL with hψ
  have hψi : Function.Injective ψ := hθ.comp Matrix.SpecialLinearGroup.toGL_injective
  set J := ψ.range
  let e : J ≃* SL(2, ZMod 3) := (MonoidHom.ofInjective hψi).symm
  set N' := oddCoreImg R ⊓ N
  have hNodd : Odd (Nat.card N') :=
    (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hNJ : ∀ j ∈ J, ∀ n ∈ N', j * n * j⁻¹ ∈ N' := by
    rintro _ ⟨B, rfl⟩ n ⟨hnO, hnN⟩
    exact ⟨datum_conj_mem_oddCoreImg hD (hθt _) hnO, hNn.conj_mem n hnN _⟩
  have hJN : ∀ n ∈ N', ∀ j ∈ J, n * j * n⁻¹ ∈ J := by
    rintro n ⟨hnO, hnN⟩ _ ⟨B, rfl⟩
    obtain ⟨A, rfl⟩ := hpull n (oddCoreImg_le R hnO) hnN
    obtain ⟨B', hB'⟩ := exists_conj_sl2 A B
    refine ⟨B', ?_⟩
    simp only [hψ, MonoidHom.comp_apply, hB', map_mul, map_inv]
  have hc := TwinFr.comm_of_odd_of_sl2 (F' := ZMod 3) (by rw [Nat.card_zmod]; decide)
    (by rw [Nat.card_zmod]) e hNJ hJN hNodd
  obtain ⟨A, rfl⟩ := hpull o (oddCoreImg_le R ho) hoN
  rcases eq_or_of_comm_sl2 (A := A) (fun B => hθ (by
      rw [map_mul, map_mul]
      exact hc _ ⟨ho, hoN⟩ _ ⟨B, rfl⟩)) with rfl | rfl
  · exact map_one θ
  · exfalso
    rw [hθ1] at ho
    have h8 : orderOf t ∣ 8 := by rw [hD.order]; norm_num
    have := hD.order
    rw [eq_one_of_mem_oddCoreImg ho h8, orderOf_one] at this
    exact absurd this (by norm_num)

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5
