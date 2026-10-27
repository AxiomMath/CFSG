module

public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

theorem nonempty_mulEquiv_sup_prod {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) (hdisj : P ⊓ Q = ⊥) :
    Nonempty (↥(P ⊔ Q) ≃* ↥P × ↥Q) := by
  let f : ↥P × ↥Q →* G :=
    MonoidHom.noncommCoprod P.subtype Q.subtype
      fun p q => (commute_iff_eq _ _).mpr (hcomm p p.2 q q.2)
  have hinj : Function.Injective f := by
    dsimp only [f]
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Subtype.coe_injective, Subtype.coe_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.mpr hdisj
  have hrange : f.range = P ⊔ Q := by
    dsimp only [f]
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent
