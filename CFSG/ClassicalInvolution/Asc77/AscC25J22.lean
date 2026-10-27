module

public import CFSG.ClassicalInvolution.Asc77.AscC25J21
public import CFSG.ClassicalInvolution.Asc77.AscC25J20
public import CFSG.ClassicalInvolution.Asc77.AscC25J7
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.C25V
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911 CFSG.ClassicalInvolution.Asc77.T3CII
open scoped MatrixGroups commutatorElement

section S4

variable {E : Type} [Group E] [Finite E] {Φ : Set (Subgroup E)}


theorem s4_excl3 {tg : StatedLieTag} {k : ℕ} (M : Ih8Model 3 1 Φ tg k 1) (hne' : Φ.Nonempty)
    (hS4 : (tg = .PSU ∧ k = 4) ∨ (tg = .POmegaOdd ∧ k = 3) ∨ (tg = .POmegaPlus ∧ k = 4) ∨
      (tg = .POmegaMinus ∧ k = 4)) :
    ∃ J₁ ∈ Φ, ∃ J₂ ∈ Φ, ∃ y ∈ J₁, ∃ z₂ ∈ J₂, y * y * y * y = 1 ∧ y * y ≠ 1 ∧
      z₂ * z₂ = 1 ∧ z₂ ≠ 1 ∧ z₂ ≠ y * y ∧ z₂ * y = y * z₂ := by
  classical
  have hG2 : tg ≠ .G2 := by
    rintro rfl
    rcases hS4 with h | h | h | h <;> simp at h
  have hD4 : tg ≠ .trialityD4 := by
    rintro rfl
    rcases hS4 with h | h | h | h <;> simp at h
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases hS4 with h | h | h | h <;> simp at h
  have hnc4 : NC4At 3 tg k 1 := by
    rcases hS4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact nc4SU_three M.admissible (by norm_num) (by norm_num)
    · exact nc4Spin7_three (by norm_num) M.admissible
    · exact nc4D4P_three (by norm_num) M.admissible
    · exact nc4D4M_three (by norm_num) M.admissible
  obtain ⟨R₁, hR₁, R₂, hR₂, y, hy, x₂, hx₂, hy4, hy2, hx₂2, hx₂1, hcomm, hnc⟩ := hnc4
  have hR₁cls : R₁ ∈ M.cls := M.fund_subset_cls hne' hG2 hD4 hR₁
  have hR₂cls : R₂ ∈ M.cls := M.fund_subset_cls hne' hG2 hD4 hR₂
  have hinj₁ := M.injOn_fund hnpsl hR₁
  have hinj₂ := M.injOn_fund hnpsl hR₂
  have hyy : y * y ∈ R₁ := R₁.mul_mem hy hy
  refine ⟨R₁.map M.ψ, M.map_mem hR₁cls, R₂.map M.ψ, M.map_mem hR₂cls, M.ψ y,
    Subgroup.mem_map_of_mem _ hy, M.ψ x₂, Subgroup.mem_map_of_mem _ hx₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← map_mul, hy4, map_one]
  · intro h
    rw [← map_mul] at h
    exact hy2 (hinj₁ (y * y) hyy h)
  · rw [← map_mul, hx₂2, map_one]
  · intro h
    exact hx₂1 (hinj₂ x₂ hx₂ h)
  · intro h
    apply hnc
    rw [← map_mul] at h
    have hker : x₂ * (y * y)⁻¹ ∈ Subgroup.center (modelUniv tg k 3 1 Fact.out).K := by
      apply M.ker_le_center
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    have hxinv : (y * y)⁻¹ = y * y := by
      apply inv_eq_of_mul_eq_one_right
      calc y * y * (y * y) = y * y * y * y := by simp only [mul_assoc]
        _ = 1 := hy4
    rw [hxinv] at hker
    have hc : (y * y) * x₂ = x₂ * (y * y) := by
      calc y * y * x₂ = y * (y * x₂) := by simp only [mul_assoc]
        _ = y * (x₂ * y) := by rw [hcomm]
        _ = (y * x₂) * y := by simp only [mul_assoc]
        _ = (x₂ * y) * y := by rw [hcomm]
        _ = x₂ * (y * y) := by simp only [mul_assoc]
    rw [hc]
    exact hker
  · rw [← map_mul, ← map_mul, hcomm]

end S4

section NC4Sec

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem crossIn_nc4_excl (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G)) :
    ∀ {J₁ J₂ : Subgroup (↥(conjGen (crossIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (crossIn K' a)))},
      J₁ ∈ oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
        (conjGen (crossIn K' a))) →
      J₂ ∈ oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
        (conjGen (crossIn K' a))) →
      ∀ {y z₂ : ↥(conjGen (crossIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (crossIn K' a))},
        y ∈ J₁ → y * y * y * y = 1 → y * y ≠ 1 → z₂ ∈ J₂ → z₂ * z₂ = 1 → z₂ ≠ 1 →
        z₂ ≠ y * y → z₂ * y = y * z₂ → False := by
  have hzKa : z ∈ K' ⊓ Subgroup.centralizer ({a} : Set G) := ⟨h.hz'.mem, hzA⟩
  intro J₁ J₂ hJ₁ hJ₂ y z₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
  have hNC4 : ∀ c₁ c₂ y₁ : ↥(Subgroup.centralizer ({a} : Set G)),
      y₁ ∈ conjSub c₁ (crossIn K' a) → orderOf y₁ = 4 →
      y₁ * (c₂ * ⟨z, hzA⟩ * c₂⁻¹) = (c₂ * ⟨z, hzA⟩ * c₂⁻¹) * y₁ →
      c₂ * ⟨z, hzA⟩ * c₂⁻¹ = c₁ * ⟨z, hzA⟩ * c₁⁻¹ := by
    intro c₁ c₂ y₁ hy₁ hy₁4 hcomm
    have hy₁4' : orderOf (y₁ : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hy₁4
    have hcomm' : ((c₂ : G) * z * (c₂ : G)⁻¹) * (y₁ : G) =
        (y₁ : G) * ((c₂ : G) * z * (c₂ : G)⁻¹) := (congrArg Subtype.val hcomm).symm
    have := eq_conj_z_of_commute_order_four h (c := (c₁ : G)) (g := (c₂ : G)) (y₀ := (y₁ : G))
      (le_conjSub_of_mem_cross c₁ hy₁) hy₁4' hcomm'
    exact Subtype.ext this
  exact nc4_excl_generic (crossIn K' a) ⟨z, hzA⟩
    (fun c => crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa c) hNC4 hJ₁ hJ₂ hy hy4 hy2 hz₂
    hz₂2 hz₂1 hne hcomm

end NC4Sec

end CFSG.ClassicalInvolution.Asc77.C25J
