module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitF5B4

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5g8_isPGroup_mulAut {X : Type} [Group X] {Tb : Subgroup X}
    (hD : Nonempty (↥Tb ≃* DihedralGroup 4)) : IsPGroup 2 (MulAut ↥Tb) := by
  obtain ⟨e⟩ := hD
  exact (CFSG.GorensteinWalter.dihedral_mulAut_is_twoGroup (m := 2) le_rfl).of_equiv
    (MulAut.congr e).symm

theorem sec5g8_hN {X : Type} [Group X] {Tb : Subgroup X}
    (hD : Nonempty (↥Tb ≃* DihedralGroup 4)) :
    ∀ n ∈ normalizer (Tb : Set X), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (Tb : Set X) :=
  fun _ hn =>
    CFSG.ComponentClassification.FooteLit.F5.pow_mem_centralizer_of_isPGroup_mulAut
      (sec5g8_isPGroup_mulAut hD) hn

end CFSG.OddStandard.SmallF3.Omega
