module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall

public section

namespace CFSG

theorem actsTrivially_of_cyclic_pGroup_of_nontrivial_fixedPointSubgroup
    {Q E : Type*} [Group Q] [Finite Q] [IsCyclic Q]
    [Group E] [Finite E] [MulDistribMulAction E Q]
    (q : ℕ) (hq : q.Prime) (hQ : IsPGroup q Q)
    (hcoprime : Nat.Coprime (Nat.card E) (Nat.card Q))
    (hfixed : fixedPointSubgroup E Q ≠ ⊥) :
    ActsTrivially E Q := by
  let : Fact q.Prime := ⟨hq⟩
  let : CommGroup Q := IsCyclic.commGroup
  let C : Subgroup Q := fixedPointSubgroup E Q
  let D : Subgroup Q := commutatorAction E Q
  have hcompl : IsCompl C D :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : Q => mul_comm x y)) hcoprime
      (inferInstance : IsMulCommutative Q)
  let multiply : C × D →* Q :=
    { toFun := fun x => (x.1 : Q) * (x.2 : Q)
      map_one' := by simp
      map_mul' := by
        intro x y
        change ((x.1 : Q) * (y.1 : Q)) * ((x.2 : Q) * (y.2 : Q)) =
          ((x.1 : Q) * (x.2 : Q)) * ((y.1 : Q) * (y.2 : Q))
        ac_rfl }
  have hmultiply : Function.Injective multiply :=
    Subgroup.mul_injective_of_disjoint hcompl.disjoint
  let : IsCyclic (C × D) := isCyclic_of_injective multiply hmultiply
  have hCDcoprime : Nat.Coprime (Nat.card C) (Nat.card D) :=
    coprime_card_of_isCyclic_prod C D
  have hD : D = ⊥ := by
    by_contra hDne
    have hCne : C ≠ ⊥ := hfixed
    let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hCne
    let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
    obtain ⟨c, hc, hCcard⟩ :=
      (hQ.to_subgroup C).nontrivial_iff_card.mp (inferInstance : Nontrivial C)
    obtain ⟨d, hd, hDcard⟩ :=
      (hQ.to_subgroup D).nontrivial_iff_card.mp (inferInstance : Nontrivial D)
    have hqC : q ∣ Nat.card C := by
      rw [hCcard]
      exact dvd_pow_self q (Nat.ne_of_gt hc)
    have hqD : q ∣ Nat.card D := by
      rw [hDcard]
      exact dvd_pow_self q (Nat.ne_of_gt hd)
    exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hCDcoprime hqC hqD)
  have hC : C = ⊤ := by
    simpa [hD] using hcompl.sup_eq_top
  intro e x
  have hx : x ∈ C := by rw [hC]; exact Subgroup.mem_top x
  exact hx e

end CFSG
