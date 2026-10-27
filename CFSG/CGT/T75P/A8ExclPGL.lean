module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Class
public import CFSG.RankThree.Classical.SteinbergCFProjectiveElementary

public section

namespace CFSG.CGT.T75P

open CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups

section PGL

variable {F : Type} [Field F]

theorem a8x_mk_eq_of_glConjSL_eq {D E : GL (Fin 2) F}
    (h : ∀ C : SL2 F, glConjSL D C = glConjSL E C) :
    ProjGenLinGroup.mk D = ProjGenLinGroup.mk E := by
  obtain ⟨c, hc0, hc⟩ := exists_scalar_of_glConjSL_eq h
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  exact hc.symm

theorem a8x_glConjSL_eq_of_mk_eq_one {D : GL (Fin 2) F} (h : ProjGenLinGroup.mk D = 1)
    (C : SL2 F) : glConjSL D C = C := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, rfl⟩ := h
  apply Subtype.ext
  rw [glConjSL_coe, ← map_inv (GeneralLinearGroup.scalar (Fin 2)) u, GeneralLinearGroup.coe_scalar,
    GeneralLinearGroup.coe_scalar]
  have hc := (Matrix.scalar_commute (u : F) (fun r' => Commute.all _ _)
    (C : Matrix (Fin 2) (Fin 2) F)).eq
  rw [hc, Matrix.mul_assoc, ← map_mul, Units.mul_inv, map_one, Matrix.mul_one]

end PGL

section Card

variable {Γ : Type*} [Group Γ]

theorem a8x_comm_of_mul_self {x y : Γ} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) * (x * y) = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxy' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  calc x * y = (x * y)⁻¹ := hxy'.symm
    _ = y⁻¹ * x⁻¹ := _root_.mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

theorem a8x_isElementaryAbelian_of_mul_self (R : Subgroup Γ) (hR : ∀ x ∈ R, x * x = 1) :
    CFSG.IsElementaryAbelian 2 R := by
  refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
  · exact Subtype.ext (a8x_comm_of_mul_self (hR a a.2) (hR b b.2) (hR (a * b) (a * b).2))
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_
    have h := hR x x.2
    rw [← sq] at h
    exact h

variable {F : Type} [Field F]

theorem a8x_card_le_eight_of_linAct (hF : ringChar F ≠ 2) (Φ : SL2 F →* Γ)
    (hΦ : Function.Injective Φ) (E : Subgroup Γ) (hsq : ∀ x ∈ E, x * x = 1)
    (hlin : ∀ x ∈ E, LinAct Φ x)
    (hcen : ∀ x ∈ E, (∀ A, x * Φ A = Φ A * x) → x = 1 ∨ x = Φ (-1)) : Nat.card E ≤ 8 := by
  classical
  choose D hD using fun x : E => hlin x.1 x.2
  have hone : ∀ A : SL2 F, glConjSL (D 1) A = glConjSL 1 A := fun A => by
    apply hΦ
    have h := hD 1 A
    rw [glConjSL_one]
    simpa using h.symm
  have hmul : ∀ (x y : E) (A : SL2 F), glConjSL (D (x * y)) A = glConjSL (D x * D y) A :=
    fun x y A => by
      apply hΦ
      rw [← hD (x * y) A, glConjSL_mul, ← hD x (glConjSL (D y) A), ← hD y A]
      simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
      group
  let ψ : E →* PGL(2, F) :=
    { toFun := fun x => ProjGenLinGroup.mk (D x)
      map_one' := by
        show ProjGenLinGroup.mk (D 1) = 1
        rw [a8x_mk_eq_of_glConjSL_eq (E := 1) hone, map_one]
      map_mul' := fun x y => by
        show ProjGenLinGroup.mk (D (x * y)) = ProjGenLinGroup.mk (D x) * ProjGenLinGroup.mk (D y)
        rw [← map_mul]
        exact a8x_mk_eq_of_glConjSL_eq (hmul x y) }
  have hψsq : ∀ y ∈ ψ.range, y * y = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have hx : x * x = 1 := Subtype.ext (hsq x.1 x.2)
    rw [hx, map_one]
  have : CFSG.IsElementaryAbelian 2 ψ.range := a8x_isElementaryAbelian_of_mul_self _ hψsq
  obtain ⟨-, hle4, -⟩ :=
    CFSG.RankThree.Classical.odd_projective_linear_elementary_two_subgroups_and_centralizers F hF
      ψ.range
  have hker : Nat.card ψ.ker ≤ 2 := by
    let R : Subgroup Γ := ψ.ker.map E.subtype
    have hR : ∀ y ∈ R, y ∈ ({1, Φ (-1)} : Finset Γ) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : ProjGenLinGroup.mk (D x) = 1 := hx
      have hc : ∀ A, (x : Γ) * Φ A = Φ A * (x : Γ) := fun A => by
        have h := hD x A
        rw [a8x_glConjSL_eq_of_mk_eq_one hx1 A, mul_inv_eq_iff_eq_mul] at h
        exact h
      simpa using hcen x.1 x.2 hc
    have hcard := (CFSG.RankThree.Classical.finite_and_card_le_of_forall_mem R _ hR).2
    have hkR : Nat.card ψ.ker = Nat.card R :=
      Nat.card_congr (ψ.ker.equivMapOfInjective E.subtype E.subtype_injective).toEquiv
    exact (hkR.trans_le hcard).trans Finset.card_le_two
  calc Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hker hle4

theorem a8x_card_le_eight_of_chart (hF : ringChar F ≠ 2) (Φ : SL2 F →* Γ)
    (hΦ : Function.Injective Φ) (hτsq : Φ (-1) * Φ (-1) = 1) (hτ1 : Φ (-1) ≠ 1)
    (hconj : ∀ x y : Γ, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → ∃ g, g * x * g⁻¹ = y)
    (hlin : ∀ x : Γ, x * Φ (-1) = Φ (-1) * x → LinAct Φ x)
    (hcen : ∀ x : Γ, x * x = 1 → (∀ A, x * Φ A = Φ A * x) → x = 1 ∨ x = Φ (-1))
    (E : Subgroup Γ) (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 8 := by
  by_cases hE : ∀ x ∈ E, x = 1
  · rw [(Subgroup.eq_bot_iff_forall E).2 hE, Subgroup.card_bot]
    norm_num
  push Not at hE
  obtain ⟨x₀, hx₀E, hx₀1⟩ := hE
  obtain ⟨g, hg⟩ := hconj x₀ (Φ (-1)) (hsq x₀ hx₀E) hτsq hx₀1 hτ1
  let ψ : Γ →* Γ := (MulAut.conj g).toMonoidHom
  have hψ : Function.Injective ψ := (MulAut.conj g).injective
  let E' : Subgroup Γ := E.map ψ
  have hE'card : Nat.card E = Nat.card E' := Nat.card_congr (E.equivMapOfInjective ψ hψ).toEquiv
  have hτ : Φ (-1) ∈ E' := ⟨x₀, hx₀E, hg⟩
  have hsq' : ∀ y ∈ E', y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]
  have hcomm : ∀ y ∈ E', y * Φ (-1) = Φ (-1) * y := fun y hy =>
    a8x_comm_of_mul_self (hsq' y hy) hτsq (hsq' _ (E'.mul_mem hy hτ))
  rw [hE'card]
  exact a8x_card_le_eight_of_linAct hF Φ hΦ E' hsq' (fun y hy => hlin y (hcomm y hy))
    (fun y hy hc => hcen y (hsq' y hy) hc)

end Card

end CFSG.CGT.T75P
