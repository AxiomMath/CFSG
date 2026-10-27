module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem isInvariant_of_smul_mem {A H : Type*} [Group A] [Group H] [MulDistribMulAction A H]
    {U : Subgroup H} (hU : ∀ a : A, ∀ x ∈ U, a • x ∈ U) : IsInvariant A H U :=
  ⟨fun a g => ⟨fun hg => hU a g hg, fun hag => by
    have h := hU a⁻¹ _ hag
    rwa [inv_smul_smul] at h⟩⟩

theorem solvable_coprime_invariant_hall_conjugacy {A H : Type*} [Group A] [Group H] [Finite A]
    [Finite H] [MulDistribMulAction A H] (hH : Group.IsSolvable H)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card H)) (π : Set Nat.Primes) {P Q : Subgroup H}
    (hP : IsHallSubgroup π P) (hQ : IsHallSubgroup π Q) (hPinv : ∀ a : A, ∀ x ∈ P, a • x ∈ P)
    (hQinv : ∀ a : A, ∀ x ∈ Q, a • x ∈ Q) :
    ∃ c ∈ fixedPointSubgroup A H, P.map (MulAut.conj c⁻¹).toMonoidHom = Q := by
  obtain ⟨g, hg, hgQ⟩ := CFSG.exists_fixedPoint_conj_of_isHallSubgroup_of_isInvariant hH hcop π
    hP hQ (isInvariant_of_smul_mem hPinv) (isInvariant_of_smul_mem hQinv)
  refine ⟨g⁻¹, inv_mem hg, ?_⟩
  rw [inv_inv, hgQ, MulEquiv.toMonoidHom_eq_coe]

end CFSG.GroupTheory.SteinbergBK
