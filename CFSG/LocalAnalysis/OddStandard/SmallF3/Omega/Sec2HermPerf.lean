module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open scoped commutatorElement

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Matrix
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary

theorem commutator_su_herm : commutator (Su F9 3 1 4) = ⊤ :=
  isQuasisimple_su_herm.1.commutator_eq_top

theorem suToOrth_mem_omega (s : Su F9 3 1 4) :
    suToOrth s ∈ omegaGroup (hermForm_nondegenerate 4) := by
  rw [omegaGroup_eq_commutator _ (by rw [finrank_hermSpace]; norm_num), commutator_def]
  have hs : s ∈ commutator (Su F9 3 1 4) := by
    rw [commutator_su_herm]
    trivial
  rw [commutator_def] at hs
  have h1 := Subgroup.mem_map_of_mem suToOrth hs
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono le_top le_top h1

theorem commute_omega_conj {γ : OGroup (hermForm 4)}
    (hγ : γ * omegaOrth 4 * γ⁻¹ = omegaOrth 4 ∨
      γ * omegaOrth 4 * γ⁻¹ = piOrth (hermForm 4) * omegaOrth 4) (s : Su F9 3 1 4) :
    (γ * suToOrth s * γ⁻¹) * omegaOrth 4 = omegaOrth 4 * (γ * suToOrth s * γ⁻¹) := by
  have key : (γ * suToOrth s * γ⁻¹) * (γ * omegaOrth 4 * γ⁻¹) =
      (γ * omegaOrth 4 * γ⁻¹) * (γ * suToOrth s * γ⁻¹) := by
    calc (γ * suToOrth s * γ⁻¹) * (γ * omegaOrth 4 * γ⁻¹)
        = γ * (suToOrth s * omegaOrth 4) * γ⁻¹ := by group
      _ = γ * (omegaOrth 4 * suToOrth s) * γ⁻¹ := by rw [suToOrth_comm_omega]
      _ = (γ * omegaOrth 4 * γ⁻¹) * (γ * suToOrth s * γ⁻¹) := by group
  rcases hγ with h | h
  · rwa [h] at key
  · rw [h] at key
    set g := γ * suToOrth s * γ⁻¹
    have h1 : piOrth (hermForm 4) * (g * omegaOrth 4) = piOrth (hermForm 4) * (omegaOrth 4 * g) :=
      calc piOrth (hermForm 4) * (g * omegaOrth 4) = g * piOrth (hermForm 4) * omegaOrth 4 := by
            rw [← mul_assoc, ← mul_piOrth_comm g]
        _ = g * (piOrth (hermForm 4) * omegaOrth 4) := by group
        _ = piOrth (hermForm 4) * omegaOrth 4 * g := key
        _ = piOrth (hermForm 4) * (omegaOrth 4 * g) := by group
    exact mul_left_cancel h1

theorem commutatorElement_mem_SUid (A B : Uid σ9 4) :
    ((⁅A, B⁆ : Uid σ9 4) : GL (Fin 4) F9) ∈ SUid σ9 4 := by
  have h : ⁅A, B⁆ ∈ specialUnitary σ9 4 := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  rw [specialUnitary_eq_subgroupOf, Subgroup.mem_subgroupOf] at h
  exact h

theorem conj_suToOrth_mem_range {γ : OGroup (hermForm 4)}
    (hγ : γ * omegaOrth 4 * γ⁻¹ = omegaOrth 4 ∨
      γ * omegaOrth 4 * γ⁻¹ = piOrth (hermForm 4) * omegaOrth 4) (s : Su F9 3 1 4) :
    ∃ s' : Su F9 3 1 4, γ * suToOrth s * γ⁻¹ = suToOrth s' := by
  let c : Su F9 3 1 4 →* OGroup (hermForm 4) := (MulAut.conj γ).toMonoidHom.comp suToOrth
  have hc : ∀ a, c a = γ * suToOrth a * γ⁻¹ := fun a => rfl
  have hle : commutator (Su F9 3 1 4) ≤ Subgroup.comap c suToOrth.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨A, hA⟩ := exists_uid_of_comm (commute_omega_conj hγ a)
    obtain ⟨B, hB⟩ := exists_uid_of_comm (commute_omega_conj hγ b)
    refine ⟨⟨_, commutatorElement_mem_SUid A B⟩, ?_⟩
    rw [map_commutatorElement, hc, hc, ← hA, ← hB, ← map_commutatorElement]
    rfl
  have hs : s ∈ commutator (Su F9 3 1 4) := by
    rw [commutator_su_herm]
    trivial
  obtain ⟨s', hs'⟩ := hle hs
  exact ⟨s', hs'.symm⟩

end CFSG.OddStandard.SmallF3.Omega
