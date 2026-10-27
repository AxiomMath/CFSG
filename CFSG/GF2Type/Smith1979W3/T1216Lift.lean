module

public import CFSG.GF2Type.Smith1979W3.Cert690.Q0
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GriessLift

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.GF2Type.Smith1979W3.Cert690

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_mulEquiv_Q0 {L : S.Qt ≃ₗ[ZMod 2] V₀} (hL : ∀ v, qPlus (L v) = S.q v) :
    ∃ φ : S.Q ≃* Q0, ∀ x : S.Q, (φ x).v = L (S.toQt x) := by
  obtain ⟨φ, hφ⟩ := CFSG.EvenSporadicStandard.HNRecog.ML1.exists_mulEquiv_of_isometry
    S.extraspecial isExtraspecialPGroup_Q0 (L.trans q0Equiv.symm) fun v => by
      rw [← qPlus_q0Equiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      exact hL v
  refine ⟨φ, fun x => ?_⟩
  have h := congrArg q0Equiv (hφ x)
  rw [q0Equiv_of, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

end CFSG.GF2Type.Smith1979W3

end
