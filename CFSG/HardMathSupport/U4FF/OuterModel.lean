module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolution
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis CFSG.LocalAnalysis.EvenBN.U4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

variable {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

theorem exists_displaced_involution {α : MulAut (gramSU h (miyamotoJ4 K))} (hα : orderOf α = 2)
    (hσ : miyamotoFieldFactor h α ≠ 1) :
    ∃ g : gramSU h (miyamotoJ4 K), α g ≠ g ∧ (α g * g⁻¹) * (α g * g⁻¹) = 1 := by
  have hchar : CharP K 2 := h.charP
  haveI := isElementaryAbelian_miyamotoA1 h
  obtain ⟨t, ht⟩ := exists_conj_eq_u_or_uz1 h hα hσ
  set β := MulAut.conj t * α * (MulAut.conj t)⁻¹ with hβdef
  have hαβ : α = (MulAut.conj t)⁻¹ * β * MulAut.conj t := by rw [hβdef]; group
  obtain ⟨ω, hω⟩ := exists_add_bar_eq_one h
  have hg₀A1 : miyamotoXGL h 0 0 ω 0 ∈ miyamotoA1 h :=
    (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩
  let g₀ : gramSU h (miyamotoJ4 K) :=
    ⟨miyamotoXGL h 0 0 ω 0, miyamotoUnipotent_le_SU h true false hg₀A1⟩
  have hβ : ∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoA1 h →
      ((β g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
        glAut (miyamotoBarEquiv h) (g : GL (Fin 4) K) := by
    intro g hg
    rcases ht with ht | ht
    · rw [ht]
      rfl
    · rw [ht, MulAut.mul_apply, MulAut.conj_apply]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have hu : ((miyamotoFieldAut h (miyamotoBarEquiv h) g : gramSU h (miyamotoJ4 K)) :
          GL (Fin 4) K) = glAut (miyamotoBarEquiv h) (g : GL (Fin 4) K) := rfl
      rw [hu, miyamotoA1_mul_comm h (miyamotoZ1S_mem_A1 h) (glAut_mem_A1 h _ hg)]
      group
  have hbg₀ : ((β g₀ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) = miyamotoXGL h 0 0 (h.bar ω) 0 := by
    rw [hβ g₀ hg₀A1]
    change glAut (miyamotoBarEquiv h) (miyamotoXGL h 0 0 ω 0) = _
    rw [glAut_miyamotoXGL]
    simp only [miyamotoBarEquiv_apply, map_zero]
  have hne : β g₀ ≠ g₀ := by
    intro he
    have h1 : ((β g₀ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) = (g₀ : GL (Fin 4) K) :=
      congrArg Subtype.val he
    rw [hbg₀] at h1
    have h2 := (miyamotoXGL_inj h).1 h1
    have h3 : h.bar ω = ω := h2.2.2.1
    rw [h3] at hω
    have : (ω + ω : K) = 0 := CharTwo.add_self_eq_zero ω
    rw [this] at hω
    exact zero_ne_one hω
  have hτA1 : ((β g₀ * g₀⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ miyamotoA1 h := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hbg₀]
    exact (miyamotoA1 h).mul_mem ((miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩)
      ((miyamotoA1 h).inv_mem hg₀A1)
  have hτsq : (β g₀ * g₀⁻¹) * (β g₀ * g₀⁻¹) = 1 := by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := miyamotoA1 h) (p := 2) _ hτA1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    simpa using this
  have h1 : α ((MulAut.conj t)⁻¹ g₀) = (MulAut.conj t)⁻¹ (β g₀) := by
    conv_lhs => rw [hαβ]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  refine ⟨(MulAut.conj t)⁻¹ g₀, ?_, ?_⟩
  · intro he
    apply hne
    rw [h1] at he
    have h2 := congrArg (fun z => MulAut.conj t z) he
    simp only [MulAut.apply_inv_self] at h2
    exact h2
  · generalize (MulAut.conj t)⁻¹ = φ at h1 ⊢
    rw [h1, ← map_inv φ g₀, ← map_mul φ, ← map_mul φ, hτsq, map_one]

end CFSG.HardMathSupport.U4FF
