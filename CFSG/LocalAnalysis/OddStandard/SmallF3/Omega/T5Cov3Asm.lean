module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5c_ne_one_of_invType {w : OGroup Q} (h : invType w = (4, 1)) : w ≠ 1 := by
  rintro rfl
  have h4 : invDim (1 : OGroup Q) = 4 := by
    simpa only [invType] using congrArg Prod.fst h
  have h0 : Module.finrank (ZMod 3) (commSp (1 : OGroup Q)) = 0 := by
    rw [commSp_one]
    exact finrank_bot (ZMod 3) V
  exact absurd (h0.symm.trans h4) (by norm_num)

theorem t5c_cover_i4_of_model (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ)
    {s : G} (hs : orderOf s = 2) {x : simGroup Q} (hx : CoverAct L φ s x) {w : OGroup Q}
    (hw : w ∈ twoRes (omegaGroup hQ ⊓ fixSub (simAct Q x))) (hww : w * w = 1)
    (hwt : invType w = (4, 1)) {c : omegaGroup hQ}
    (hc : w = (c : OGroup Q) * simAct Q x (c : OGroup Q)⁻¹) :
    ∃ u ∈ XOut L s, orderOf u = 2 ∧ IsI4PlusIn L u ∧ s * u ∈ conjClassIn L s := by
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs]; exact pow_orderOf_eq_one s
  obtain ⟨u, hu, hmem, hord, hcomm, hφu⟩ :=
    t5c_lift_twoRes hL h hs2 hx hw hww (t5c_ne_one_of_invType hwt)
  have huu : u * u = 1 := by rw [← pow_two, ← hord]; exact pow_orderOf_eq_one u
  refine ⟨u, ?_, hord, ?_, ?_⟩
  · exact Subgroup.subset_closure ⟨hmem, 1, by rw [hord, pow_one]⟩
  · rw [t5_isI4PlusIn_iff hL h hu hord]
    have hww' : ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) *
        ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) = 1 := by rw [hφu]; exact hww
    have hne : φ ⟨u, hu⟩ ≠ 1 := by
      intro h1
      apply t5c_ne_one_of_invType hwt
      rw [← hφu, h1]
      rfl
    rw [t5_isI4PlusIn_omega_iff h.finrank_eq h.quadSign_eq hww' hne, hφu]
    exact hwt
  · have he2 : (u * s) * (u * s) = 1 := by
      calc (u * s) * (u * s) = u * (s * u) * s := by group
        _ = u * (u * s) * s := by rw [hcomm]
        _ = (u * u) * (s * s) := by group
        _ = 1 := by rw [huu, hs2, mul_one]
    have hconj := t5c_conj_exact hL h hs2 hx hu he2 (c := c) (by rw [hφu]; exact hc)
    rw [hcomm]
    exact hconj

end CFSG.OddStandard.SmallF3.Omega
