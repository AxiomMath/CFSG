module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.LieType.Steinberg
open scoped commutatorElement

section Perfect

theorem isPerfect_commutator_of_central {E H : Type} [Group E] [Group H] [Group.IsPerfect H]
    (π : E →* H) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    Group.IsPerfect ↥(commutator E) := by
  have hmap : (commutator E).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  have hdec : ∀ x : E, ∃ n ∈ commutator E, x * n⁻¹ ∈ Subgroup.center E := by
    intro x
    have hx : π x ∈ (commutator E).map π := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n, hn, hcen ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, mul_inv_cancel]
  have hle : commutator E ≤ ⁅commutator E, commutator E⁆ := by
    refine (commutator_def E).le.trans (Subgroup.commutator_le.mpr fun x _ y _ => ?_)
    obtain ⟨n, hn, hnx⟩ := hdec x
    obtain ⟨m, hm, hmy⟩ := hdec y
    have e : ⁅x, y⁆ = ⁅n, m⁆ := by
      have h := commutatorElement_mul_mul_of_mem_center hnx hmy n m
      rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
    rw [e]
    exact Subgroup.commutator_mem_commutator hn hm
  have hperf : ⁅commutator E, commutator E⁆ = commutator E :=
    le_antisymm (Subgroup.commutator_le_right _ _) hle
  rw [Group.isPerfect_def, eq_top_iff]
  intro y _
  have h1 : (y : E) ∈ ⁅commutator E, commutator E⁆ := by
    rw [hperf]
    exact y.2
  rw [← Subgroup.map_subtype_commutator] at h1
  obtain ⟨z, hz, hzy⟩ := h1
  have : z = y := Subtype.ext hzy
  rwa [← this]

end Perfect

end CFSG.ClassicalInvolution.Q3.Q3OF
