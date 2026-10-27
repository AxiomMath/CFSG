module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23L63Frame
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutFinal

public section

namespace CFSG.EvenSporadicStandard.Solomon78.F23L63

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ CFSG.EvenSporadicStandard.TwoFi22.DS81

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

theorem mem_of_forall_comm {C : Type} [Group C] {E : Subgroup C} (hZ : center C ≤ E)
    (haut : ∀ σ : MulAut C, (∀ e ∈ E, σ e = e) → ∃ x ∈ E, σ = MulAut.conj x) {c : C}
    (hc : ∀ e ∈ E, c * e = e * c) : c ∈ E := by
  obtain ⟨x, hx, hσ⟩ := haut (MulAut.conj c) fun e he => by
    rw [MulAut.conj_apply]
    calc c * e * c⁻¹ = e * c * c⁻¹ := by rw [hc e he]
      _ = e := by group
  have hcen : x⁻¹ * c ∈ center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : c * g * c⁻¹ = x * g * x⁻¹ := by
      have := congrArg (fun f : MulAut C => f g) hσ
      simpa only [MulAut.conj_apply] using this
    calc g * (x⁻¹ * c) = x⁻¹ * (x * g * x⁻¹) * c := by group
      _ = x⁻¹ * (c * g * c⁻¹) * c := by rw [h1]
      _ = x⁻¹ * c * g := by group
  have hc' : c = x * (x⁻¹ * c) := by group
  rw [hc']
  exact mul_mem hx (hZ hcen)

section Cent


theorem centralizer_E0_le {c : Cd} (hc : ∀ e ∈ E0, c * e = e * c) : c ∈ E0 :=
  @mem_of_forall_comm ↥Cd (inferInstance) E0 E0_center_le Cd_aut_cent c hc

theorem centralizer_frameE_le {z : J} (hz : ∀ x ∈ (frameE : Subgroup J), z * x = x * z) :
    z ∈ (frameE : Subgroup J) := by
  have hzd : z ∈ Cd := mem_Cd.2 (hz d d_mem_frameE)
  have h := centralizer_E0_le (c := ⟨z, hzd⟩) fun e he =>
    Subtype.ext (hz e (Subgroup.mem_subgroupOf.1 he))
  exact Subgroup.mem_subgroupOf.1 h

end Cent

end CFSG.EvenSporadicStandard.Solomon78.F23L63
