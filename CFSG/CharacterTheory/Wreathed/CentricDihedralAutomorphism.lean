module

public import CFSG.CharacterTheory.Wreathed.SubgroupDihedralQuotient
public import CFSG.CharacterTheory.Wreathed.CentricVCopies
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalizerComplement
public import CFSG.GroupTheory.AutomorphismRestrictionKernel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem nonabelian_dihedral_center_quotient_automorphism_isPGroup
    (n : ℕ) (hn : 2 ≤ n) (P : Subgroup (Wreath (2 ^ n)))
    (hP : ∃ u v : P, u * v ≠ v * u)
    (hcenter : Subgroup.center (Wreath (2 ^ n)) ≤ P)
    (k : ℕ) (hk : 2 ≤ k)
    (equiv : P ⧸ Subgroup.center P ≃* DihedralGroup (2 ^ k)) :
    IsPGroup 2 (MulAut P) := by
  have hm : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have htwoP := (wreath_isPGroup n).to_subgroup P
  have htwoCenter := htwoP.to_subgroup (Subgroup.center P)
  let : IsCyclic (Subgroup.center P) :=
    nonabelian_subgroup_center_isCyclic _ hm P hP hcenter
  have hcenterAut := CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup
    (Subgroup.center P) htwoCenter
  have hquotientAut := (CFSG.GorensteinWalter.dihedral_mulAut_is_twoGroup hk).of_equiv
    (MulAut.congr equiv).symm
  exact CFSG.characteristic_automorphism_isPGroup 2 Nat.prime_two (Subgroup.center P)
    htwoCenter hcenterAut hquotientAut

theorem nonabelian_odd_automorphism_center_quotient_dihedral_two
    (n : ℕ) (hn : 2 ≤ n) (P : Subgroup (Wreath (2 ^ n)))
    (hP : ∃ u v : P, u * v ≠ v * u)
    (hcenter : Subgroup.center (Wreath (2 ^ n)) ≤ P)
    (hautomorphism : ¬ IsPGroup 2 (MulAut P)) :
    Nonempty (P ⧸ Subgroup.center P ≃* DihedralGroup 2) := by
  obtain ⟨k, hk, _, ⟨equiv⟩⟩ :=
    nonabelian_subgroup_center_quotient_dihedral (by omega : 1 ≤ n) P hP
  have hkone : k = 1 := by
    by_contra hne
    exact hautomorphism
      (nonabelian_dihedral_center_quotient_automorphism_isPGroup n hn P hP hcenter k
        (by omega) equiv)
  subst k
  exact ⟨equiv⟩

end CFSG.Wreathed
