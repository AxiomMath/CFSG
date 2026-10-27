module

public import CFSG.LieType.Ree.FixedMonomialQuotient

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable (t : ReeTag)

@[expose] def reeParabolicWeylGroup
    (J : Set (Fin t.fixedOrbitCount)) :
    Subgroup (WeylGroup t.tag) :=
  Subgroup.closure (t.fixedOrbitElement '' J)

variable (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

@[expose] def reeParabolic
    (J : Set (Fin t.fixedOrbitCount)) : Subgroup (ModGL t.tag K) :=
  t.reeFixedBorel K a ⊔ Subgroup.closure
    ((fun j => canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) '' J)

theorem reeParabolicWeylGroup_le
    (J : Set (Fin t.fixedOrbitCount)) :
    t.reeParabolicWeylGroup J ≤ t.relWeylRee :=
  (Subgroup.closure_le _).2 fun _ ⟨j, _, hj⟩ => hj ▸ fixedOrbitElement_mem j

theorem reeParabolic_le
    (J : Set (Fin t.fixedOrbitCount)) :
    t.reeParabolic K a J ≤ t.reeGamma K a :=
  sup_le inf_le_right ((Subgroup.closure_le _).2 fun _ ⟨j, _, hj⟩ =>
    hj ▸ (canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j)).2)

theorem reeFixedBorel_le_reeParabolic
    (J : Set (Fin t.fixedOrbitCount)) :
    t.reeFixedBorel K a ≤ t.reeParabolic K a J :=
  le_sup_left

theorem canonicalRep_mem_reeParabolic
    {J : Set (Fin t.fixedOrbitCount)}
    {j : Fin t.fixedOrbitCount} (hj : j ∈ J) :
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeParabolic K a J :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, rfl⟩)

omit [Finite K] [CharP K t.prime] in
theorem reeParabolicWeylGroup_empty
    : t.reeParabolicWeylGroup ∅ = ⊥ := by
  rw [reeParabolicWeylGroup, Set.image_empty, Subgroup.closure_empty]

theorem reeParabolic_empty
    : t.reeParabolic K a ∅ = t.reeFixedBorel K a := by
  rw [reeParabolic, Set.image_empty, Subgroup.closure_empty, sup_bot_eq]

end ReeTag

end CFSG.LieType.Ree
