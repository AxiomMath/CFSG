module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TGiCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TGiIdx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TGiWit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Pi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec8t84t_gi_claimA (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) {g : OGroup Q}
    (hgΩ : g ∈ omegaGroup hQ) (hgC : g ∈ fixSub (simAct Q ρ)) :
    g ∈ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ∨
      piOrth Q * g ∈ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ := by
  obtain ⟨hLie, hG1Ω, -⟩ := ff6m_K4_core hQ hdim hρ hρρ
  have hCcard := sec8t84t_gi_cent_card hQ hdim hρ hρρ
  have hG1card := ff_card_model_psl2 hLie
  have hπG1 := ff6m_K4_pi_not_mem hQ hdim hρ hρρ
  obtain ⟨c, hcC, hcΩ⟩ := sec8t84t_gi_witness hQ hdim hρ hρρ
  have hG1C : ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ≤ fixSub (simAct Q ρ) := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)
  have hπΩ : piOrth Q ∈ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim, hsgn]
    decide
  have hπC : piOrth Q ∈ fixSub (simAct Q ρ) := mem_fixSub_iff.mpr (simAct_piOrth ρ)
  let G' : Subgroup ↥(fixSub (simAct Q ρ)) :=
    (⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆).subgroupOf (fixSub (simAct Q ρ))
  let A' : Subgroup ↥(fixSub (simAct Q ρ)) := (omegaGroup hQ).subgroupOf (fixSub (simAct Q ρ))
  have hGA : G' ≤ A' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hG1Ω (Subgroup.mem_subgroupOf.mp hx))
  have hcardG' : Nat.card ↥G' = 360 := by
    rw [← hG1card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG1C).toEquiv
  have hcard : Nat.card ↥(fixSub (simAct Q ρ)) = 4 * Nat.card ↥G' := by
    rw [hCcard, hcardG']
  have hA : A' ≠ ⊤ := by
    intro h
    have hc : (⟨c, hcC⟩ : ↥(fixSub (simAct Q ρ))) ∈ A' := h ▸ Subgroup.mem_top _
    exact hcΩ (Subgroup.mem_subgroupOf.mp hc)
  let z : ↥(fixSub (simAct Q ρ)) := ⟨piOrth Q, hπC⟩
  have hzA : z ∈ A' := Subgroup.mem_subgroupOf.mpr hπΩ
  have hzG : z ∉ G' := fun h => hπG1 (Subgroup.mem_subgroupOf.mp h)
  have key := sec8t84t_gi_index_two G' A' hGA hcard hA hzA hzG ⟨g, hgC⟩
    (Subgroup.mem_subgroupOf.mpr hgΩ)
  rcases key with h | h
  · exact Or.inl (Subgroup.mem_subgroupOf.mp h)
  · right
    have h' : g * (piOrth Q)⁻¹ ∈ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ :=
      Subgroup.mem_subgroupOf.mp h
    have hπinv : (piOrth Q)⁻¹ = piOrth Q := inv_eq_of_mul_eq_one_right piOrth_mul_self
    have hcomm : piOrth Q * g = g * piOrth Q :=
      (Subgroup.mem_center_iff.mp piOrth_mem_center g).symm
    rw [hπinv, ← hcomm] at h'
    exact h'

end CFSG.OddStandard.SmallF3.Omega
