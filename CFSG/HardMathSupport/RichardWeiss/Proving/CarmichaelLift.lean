module

public import CFSG.Alternating.Multipliers.Carmichael

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.Alternating.Multipliers CFSG.LieType.Multipliers CFSG.LocalAnalysis.ComponentInitial

theorem exists_hom_altThreeCycle_eq {G : Type*} [Group G] (m : ℕ) (a : Fin m → G)
    (h3 : ∀ i, a i ^ 3 = 1) (h2 : ∀ i j, i ≠ j → (a i * a j) ^ 2 = 1) :
    ∃ ψ : alternatingGroup (Fin (m + 2)) →* G, ∀ i, ψ (altThreeCycle i) = a i := by
  have hP := isPresentation_carmichael m
  have hle : (FreeGroup.lift (altThreeCycle (n := m))).ker ≤ (FreeGroup.lift a).ker := by
    rw [hP.ker_lift]
    exact Subgroup.normalClosure_le_normal fun r hr =>
      MonoidHom.mem_ker.mpr (lift_carmichaelWords_eq_one h3 h2 r hr)
  let e := QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift (altThreeCycle (n := m)))
    hP.lift_surjective
  let q := QuotientGroup.lift (FreeGroup.lift (altThreeCycle (n := m))).ker (FreeGroup.lift a) hle
  have key : ∀ i, e (QuotientGroup.mk (FreeGroup.of i)) = altThreeCycle i := fun i =>
    (QuotientGroup.kerLift_mk _ _).trans (FreeGroup.lift_apply_of)
  refine ⟨q.comp e.symm.toMonoidHom, fun i => ?_⟩
  have hi : e.symm (altThreeCycle i) = QuotientGroup.mk (FreeGroup.of i) := by
    rw [MulEquiv.symm_apply_eq, key]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hi]
  rw [QuotientGroup.lift_mk, FreeGroup.lift_apply_of]

end CFSG.HardMathSupport.RichardWeiss.Proving

end
