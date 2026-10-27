module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4L
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4F3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open scoped commutatorElement

variable {F : Type} [Field F]

theorem trace_conj (P x : GL (Fin 4) F) :
    ((P⁻¹ * x * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace =
      (x : Matrix (Fin 4) (Fin 4) F).trace := by
  rw [Units.val_mul, trace_mul_comm, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul P,
    mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem caseL (hK : ringChar F ≠ 2) {H : Subgroup (GL (Fin 4) F)}
    {N : Submodule F (Fin 4 → F)} (hN0 : N ≠ ⊥) (hNt : N ≠ ⊤)
    (hHN : ∀ x ∈ H, ∀ v ∈ N, (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N)
    {A₁ A₂ : GL (Fin 4) F} (hA₁N : ∀ v ∈ N, (A₁ : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N)
    (hA₂N : ∀ v ∈ N, (A₂ : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N)
    (hA₁H : ∀ x ∈ H, A₁ * x = x * A₁) (hA₂H : ∀ x ∈ H, A₂ * x = x * A₂)
    (hT₁ : IsT12 A₁) (hT₂ : IsT12 A₂)
    (hlam : ∃ lam : Fˣ, A₁ * A₂ = GeneralLinearGroup.scalar (Fin 4) lam * (A₂ * A₁))
    (hT₃ : ∃ (B₃ : GL (Fin 4) F) (μ : Fˣ), IsT12 B₃ ∧
      B₃ = GeneralLinearGroup.scalar (Fin 4) μ * (A₁ * A₂)) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  rcases eig_or_comm hN0 hNt hHN hA₁N hA₂N hA₁H hA₂H with hc | heig
  · exact hc
  obtain ⟨lam, hlam⟩ := hlam
  have hlamM : (A₁ : Matrix (Fin 4) (Fin 4) F) * A₂ =
      (lam : F) • ((A₂ : Matrix (Fin 4) (Fin 4) F) * A₁) := by
    rw [← Units.val_mul, hlam, coe_scalar_mul, Units.val_mul]
  have h₁ := sq_one_of_eig hT₁ (heig.imp (fun ⟨v, hv0, ν₁, _, h1, _⟩ => ⟨v, hv0, ν₁, h1⟩)
    (fun ⟨v, hv0, ν₁, _, h1, _⟩ => ⟨v, hv0, ν₁, h1⟩))
  have h₂ := sq_one_of_eig hT₂ (heig.imp (fun ⟨v, hv0, _, ν₂, _, h2⟩ => ⟨v, hv0, ν₂, h2⟩)
    (fun ⟨v, hv0, _, ν₂, _, h2⟩ => ⟨v, hv0, ν₂, h2⟩))
  have hl1 : (lam : F) = 1 := by
    rcases heig with ⟨v, hv0, ν₁, ν₂, e1, e2⟩ | ⟨v, hv0, ν₁, ν₂, e1, e2⟩
    · exact eq_one_of_common_eigvec hlamM hv0 e1 e2
    · exact eq_one_of_common_roweig hlamM hv0 e1 e2
  have hcomm : A₁ * A₂ = A₂ * A₁ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hlamM, hl1, one_smul]
  obtain ⟨B₃, μ, hT₃, hB₃⟩ := hT₃
  have h12sq : A₁ * A₂ * (A₁ * A₂) = 1 := by
    calc A₁ * A₂ * (A₁ * A₂) = A₁ * (A₂ * A₁) * A₂ := by group
      _ = A₁ * (A₁ * A₂) * A₂ := by rw [hcomm]
      _ = (A₁ * A₁) * (A₂ * A₂) := by group
      _ = 1 := by rw [h₁.1, h₂.1, one_mul]
  have hsc : ∀ (a : Fˣ) (X : GL (Fin 4) F), GeneralLinearGroup.scalar (Fin 4) a * X =
      X * GeneralLinearGroup.scalar (Fin 4) a := fun a X => GeneralLinearGroup.scalar_commute a X
  have h₃ : B₃ * B₃ = 1 ∧ finrank F (LinearMap.ker (toLin' B₃.val - 1)) = 2 := by
    rcases hT₃ with h | ⟨c, hc, hns⟩
    · exact h
    · exfalso
      apply hns
      have e : GeneralLinearGroup.scalar (Fin 4) c = GeneralLinearGroup.scalar (Fin 4) (μ * μ) := by
        rw [← hc, hB₃, mul_assoc, ← mul_assoc (A₁ * A₂), ← hsc, mul_assoc, h12sq, mul_one,
          ← map_mul]
      have e00 := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F) 0 0) e
      simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
        Units.val_mul] at e00
      exact ⟨μ, e00⟩
  have htr₃ := trace_eq_zero_of_finrank hK h₃.1 h₃.2
  have htr12 : ((A₁ * A₂ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace = 0 := by
    rw [hB₃, coe_scalar_mul, trace_smul, smul_eq_mul] at htr₃
    exact (mul_eq_zero.mp htr₃).resolve_left μ.ne_zero
  have htr2 := trace_eq_zero_of_finrank hK h₂.1 h₂.2
  obtain ⟨P, hP⟩ := exists_conj_diag4 hK h₁.1 h₁.2
  let ψ : GL (Fin 4) F →* GL (Fin 2 ⊕ Fin 2) F := bvGL.comp (MulAut.conj P⁻¹).toMonoidHom
  have hψ : ∀ x, ((ψ x : GL (Fin 2 ⊕ Fin 2) F) : MB F) =
      bv ((P⁻¹ * x * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro x
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      coe_bvGL]
  have hψinj : Function.Injective ψ := bvGL_injective.comp (MulAut.conj P⁻¹).injective
  have hD : ((ψ A₁ : GL (Fin 2 ⊕ Fin 2) F) : MB F) = dD := by rw [hψ, hP, bv_diag4]
  have hcψ : ∀ x y : GL (Fin 4) F, x * y = y * x →
      ((ψ x : GL (Fin 2 ⊕ Fin 2) F) : MB F) * ((ψ y : GL (Fin 2 ⊕ Fin 2) F) : MB F) =
        ((ψ y : GL (Fin 2 ⊕ Fin 2) F) : MB F) * ((ψ x : GL (Fin 2 ⊕ Fin 2) F) : MB F) := by
    intro x y hxy
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hxy]
  have hB2 : ((ψ A₂ : GL (Fin 2 ⊕ Fin 2) F) : MB F) * ((ψ A₂ : GL (Fin 2 ⊕ Fin 2) F) : MB F) =
      1 := by rw [← Units.val_mul, ← map_mul, h₂.1, map_one, Units.val_one]
  have htrB : ((ψ A₂ : GL (Fin 2 ⊕ Fin 2) F) : MB F).trace = 0 := by
    rw [hψ, trace_bv, trace_conj, htr2]
  have htrDB : (dD * ((ψ A₂ : GL (Fin 2 ⊕ Fin 2) F) : MB F)).trace = 0 := by
    rw [← hD, ← Units.val_mul, ← map_mul, hψ, trace_bv, trace_conj, htr12]
  have hHc : ∀ z ∈ H, ∀ w ∈ H, z * w = w * z := by
    intro z hz w hw
    apply hψinj
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    have hDB := hcψ A₁ A₂ hcomm
    rw [hD] at hDB
    have hz1 := hcψ A₁ z (hA₁H z hz)
    have hw1 := hcψ A₁ w (hA₁H w hw)
    rw [hD] at hz1 hw1
    exact comm_of_two_involutions h2 hB2 hDB htrB htrDB hz1 (hcψ A₂ z (hA₂H z hz)) hw1
      (hcψ A₂ w (hA₂H w hw))
  intro z hz w hw
  exact hHc z (Subgroup.commutator_le_self H hz) w (Subgroup.commutator_le_self H hw)

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
