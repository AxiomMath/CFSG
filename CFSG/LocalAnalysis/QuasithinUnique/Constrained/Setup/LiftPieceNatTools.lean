module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatY
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

variable {G : Type} [Group G]

theorem natL_normal : (oddOrderSubgroup (⊤ : Subgroup G)).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  refine top_le_iff.mp fun g _ => normalizer_le_normalizer_oddOrderSubgroup (⊤ : Subgroup G)
    (?_ : g ∈ Subgroup.normalizer ((⊤ : Subgroup G) : Set G))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp

theorem NatResidual.le_LS {R P : Subgroup G} (hres : NatResidual R P) :
    P ≤ oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R :=
  calc P = oddOrderSubgroup P ⊔ baum R := hres.P_eq
    _ ≤ oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R :=
      sup_le_sup_right (oddOrderSubgroup_mono le_top) _

theorem natQ_normal [Finite G] {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) :
    (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)).Normal := by
  have hLS := normal_L_sup_baum hS
  apply Subgroup.normalizer_eq_top_iff.mp
  rw [eq_top_iff]
  intro g _
  refine C1.mem_normalizer_blockQ (L := oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ?_
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top g

end CFSG.QuasithinUnique.Setup.Lift
