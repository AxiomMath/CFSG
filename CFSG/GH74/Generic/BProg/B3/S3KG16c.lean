module

public import CFSG.GH74.Generic.BProg.B3.S3KG16cCore
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem S3KG.isSolvable_outer_of_qShape3 {Kt : Type} [Group Kt] (h3 : QShape3 Kt) :
    Group.IsSolvable (Outer Kt) := by
  obtain ⟨p, f, -, -, -, hm⟩ := h3
  rcases hm with hm | hm
  · exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_classical_model_schreier
      le_rfl (CFSG.GH74.Generic.stated_of_lieModel_PSL hm)).2
  · exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
      (CFSG.GH74.Generic.stated_of_lieModel_PSU hm)).2

theorem s16cKG_proved : S3Sec29C.S16cKG := by
  intro Kt _ _ h3 _ u S hu _ hcomm
  obtain ⟨S₀, hS₀c, huS₀, hS₀q, -, -⟩ := S3L3KGroup.exists_invDataB4 h3 hu
  have hS₀S : S₀ ≤ S := by
    have h1 : ⁅S₀, S₀⁆ ≤ S :=
      Subgroup.commutator_le.mpr fun a ha b hb => hcomm a (hS₀c ha) b (hS₀c hb)
    exact (Subgroup.isPerfect_iff.mp hS₀q.1) ▸ h1
  refine S3KG.isSolvable_of_fixes (S := S) _ (fun γ hγ => hγ) (fun c hc s hs => ?_)
    (S3KG.isSolvable_centralizer (hS₀S huS₀) hcomm) (S3KG.isSolvable_outer_of_qShape3 h3)
  rw [MulAut.conj_apply, ← mem_centralizer_iff.mp hc s hs, mul_inv_cancel_right]

end CFSG.GH74.Generic.BProg.B3
