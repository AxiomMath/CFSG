module

public import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag


theorem lieModel_reeGamma (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.Blueprint.LieModel ↥(F4.reeGamma K a) .twistedF4 0 2 (2 * a + 1) := by
  let H : Subgroup (ModGL F4.tag K) :=
    reeFixedGroup .F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))
  have hH : H = F4.reeGamma K a :=
    (reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)).symm
  obtain ⟨e⟩ :=
    CFSG.LieType.ChevTwo.Semi.nonempty_derivedCentralQuotient_equiv_reeGamma
      (K := K) ha hK hH
  refine Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ?_⟩))
  refine ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl, ?_⟩
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.symm⟩⟩

end CFSG.LieType.ChevTwo.Semi
