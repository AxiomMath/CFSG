module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4C2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4Adm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4G5
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4L2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4N3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4T

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {F : Type} [Field F]

theorem transpose_inv_of_symm {A : GL (Fin 4) F} (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) :
    ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  calc ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ
      = ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * (A : Matrix (Fin 4) (Fin 4) F)ᵀ *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [hA, Matrix.mul_assoc, mul_inv_self, Matrix.mul_one]
    _ = ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [← transpose_mul, mul_inv_self, transpose_one, Matrix.one_mul]

theorem selfAdj_of_symm {A B : GL (Fin 4) F} (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A)
    (hBA : ((B * A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (B * A : GL (Fin 4) F)) :
    (B : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) := by
  rw [Units.val_mul, transpose_mul, hA] at hBA
  calc (B : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      = ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((A : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F)ᵀ) *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [← Matrix.mul_assoc, inv_mul_self, Matrix.one_mul]
    _ = ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) := by
        rw [hBA, Matrix.mul_assoc, Matrix.mul_assoc, mul_inv_self, Matrix.mul_one]

variable [Finite F]

theorem symm_of_graph_pair {A B : GL (Fin 4) F}
    (hS : Surv4Orth (conjAut 4 F B * (conjAut 4 F A * dualAut 4 F))) :
    ((B * A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (B * A : GL (Fin 4) F) := by
  have hrel : conjAut 4 F B * (conjAut 4 F A * dualAut 4 F) =
      conjAut 4 F (B * A) * dualAut 4 F := by rw [map_mul, mul_assoc]
  rcases lin_or_graph hS with ⟨B', -, hB'⟩ | ⟨A', hA's, hA'⟩
  · exact absurd (hrel.symm.trans hB') (conjAut_dualAut_ne (B * A) B')
  · have hc : conjAut 4 F A' = conjAut 4 F (B * A) := mul_right_cancel (hA'.symm.trans hrel)
    obtain ⟨μ, hμ⟩ := exists_scalar_of_conjAut_eq hc
    rw [hμ, coe_scalar_mul, transpose_smul] at hA's
    exact smul_right_injective _ μ.ne_zero hA's

theorem not_btConfig_l4 {k : Kind} (hk : IsClassicalKind k) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq8 : p ^ f % 8 ≠ 1) (hcard : Nat.card F = p ^ f) :
    ¬ BTConfig k p (projectiveSL 4 F) := by
  rintro ⟨W, I, Q, U, hW, hWp, hI, hIW, hQI, hQ, hU, hUW, hUI, hadm⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hK : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
  have hIne : I ≠ ⊥ := by
    rintro rfl
    have h4 := hQ.2
    rw [le_bot_iff.mp hQI, Subgroup.card_bot] at h4
    norm_num at h4
  obtain ⟨N, hN0, hNt, hNlin, hNgr⟩ := exists_subspace hp2 hW hWp
  have hHN := stab_of_mem_Hc hIW hNlin
  have hfin := false_of_comm hI hIne
  have hlinU : ∀ A : GL (Fin 4) F, conjAut 4 F A ∈ U →
      (∀ v ∈ N, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N) ∧ ∀ x ∈ Hc I, A * x = x * A :=
    fun A hA => ⟨hNlin A (mem_normalizer_preGL_of_conjAut (hUW _ hA)), comm_of_lin (hUI _ hA)⟩
  have hS : ∀ v ∈ U, v ≠ 1 → v * v = 1 → Surv4Orth v := fun v hv hv1 hvv =>
    surv4Orth_of_admAut hk hp hp2 hf hq8 hcard hvv (hadm v hv hv1)
  have hG : ∀ B A : GL (Fin 4) F, IsT12 B → (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A →
      conjAut 4 F B ∈ U → conjAut 4 F A * dualAut 4 F ∈ U →
      Surv4Orth (conjAut 4 F B * (conjAut 4 F A * dualAut 4 F)) → False := by
    intro B A hTB hAs hBU hAU hSv
    obtain ⟨hBN, hBH⟩ := hlinU B hBU
    have hdet : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp (A⁻¹ : GL (Fin 4) F).isUnit).ne_zero
    exact hfin (caseG hK hN0 hNt hHN hBN hBH hTB (transpose_inv_of_symm hAs) hdet
      (form_of_graph (hUI _ hAU)) (selfAdj_of_symm hAs (symm_of_graph_pair hSv))
      (hNgr A (hUW _ hAU)))
  obtain ⟨u₁, hu₁, u₂, hu₂, h1, h2, h12, hsq1, hsq2, hsq12⟩ := exists_pair_four hU
  have hcomm : u₁ * u₂ = u₂ * u₁ := by
    have := hU.1.toIsMulCommutative
    exact congrArg Subtype.val (mul_comm' (⟨u₁, hu₁⟩ : ↥U) ⟨u₂, hu₂⟩)
  have hu12 : u₁ * u₂ ∈ U := mul_mem hu₁ hu₂
  have hS12 := hS _ hu12 h12 hsq12
  rcases lin_or_graph (hS u₁ hu₁ h1 hsq1) with ⟨A₁, hT₁, rfl⟩ | ⟨A₁, hA₁s, rfl⟩ <;>
    rcases lin_or_graph (hS u₂ hu₂ h2 hsq2) with ⟨A₂, hT₂, rfl⟩ | ⟨A₂, hA₂s, rfl⟩
  · obtain ⟨hA₁N, hA₁H⟩ := hlinU A₁ hu₁
    obtain ⟨hA₂N, hA₂H⟩ := hlinU A₂ hu₂
    have hlam := exists_scalar_of_conjAut_eq (X := A₁ * A₂) (Y := A₂ * A₁)
      (by rw [map_mul, map_mul, hcomm])
    have hT₃ : ∃ (B₃ : GL (Fin 4) F) (μ : Fˣ), IsT12 B₃ ∧
        B₃ = GeneralLinearGroup.scalar (Fin 4) μ * (A₁ * A₂) := by
      rcases lin_or_graph hS12 with ⟨B₃, hT₃, hB₃⟩ | ⟨A₃, -, hA₃⟩
      · obtain ⟨μ, hμ⟩ := exists_scalar_of_conjAut_eq (X := B₃) (Y := A₁ * A₂)
          (by rw [← hB₃, map_mul])
        exact ⟨B₃, μ, hT₃, hμ⟩
      · exact absurd (hA₃.symm.trans (map_mul _ _ _).symm) (conjAut_dualAut_ne A₃ (A₁ * A₂))
    exact hfin (caseL hK hN0 hNt hHN hA₁N hA₂N hA₁H hA₂H hT₁ hT₂ hlam hT₃)
  · exact hG A₁ A₂ hT₁ hA₂s hu₁ hu₂ hS12
  · exact hG A₂ A₁ hT₂ hA₁s hu₂ hu₁ (by rw [← hcomm]; exact hS12)
  · rcases lin_or_graph hS12 with ⟨B₃, hT₃, hB₃⟩ | ⟨A₃, -, hA₃⟩
    · have hv : conjAut 4 F B₃ * (conjAut 4 F A₁ * dualAut 4 F) =
          conjAut 4 F A₂ * dualAut 4 F := by
        rw [← hB₃, hcomm, mul_assoc, hsq1, mul_one]
      exact hG B₃ A₁ hT₃ hA₁s (hB₃ ▸ hu12) hu₁ (by rw [hv]; exact hS _ hu₂ h2 hsq2)
    · have hdd : dualAut 4 F * dualAut 4 F = 1 :=
        (standard_automorphism_transport (n := 4) (K := F)).2.2.2.1
      have hlin : conjAut 4 F A₁ * dualAut 4 F * (conjAut 4 F A₂ * dualAut 4 F) =
          conjAut 4 F (A₁ * GeneralLinearGroup.inverseTranspose A₂) := by
        rw [mul_assoc, ← mul_assoc (dualAut 4 F), dualAut_mul_conjAut, mul_assoc, hdd, mul_one,
          ← map_mul]
      exact conjAut_dualAut_ne A₃ _ (hA₃.symm.trans hlin)

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
