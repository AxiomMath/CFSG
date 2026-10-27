module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSylowNormalizer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.FooteLit.F5

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mem_centralizer_of_isPGroup_mulAut {T : Subgroup G} (hT : IsPGroup 2 (MulAut T))
    {n : G} (hn : n ∈ normalizer (T : Set G)) : ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (T : Set G) := by
  obtain ⟨k, hk⟩ := hT (T.normalizerMonoidHom ⟨n, hn⟩)
  refine ⟨k, ?_⟩
  have h1 : (⟨n, hn⟩ : normalizer (T : Set G)) ^ (2 ^ k) ∈ T.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_pow, hk]
  rw [normalizerMonoidHom_ker, mem_subgroupOf] at h1
  simpa using h1

omit [Finite G] in
theorem isPGroup_mulAut_of_dihedral {D : Subgroup G} (hD : AschbacherTheorem3.IsDihedralTwoGroup D)
    (h8 : 8 ≤ Nat.card D) : IsPGroup 2 (MulAut D) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hD
  have hcard : Nat.card D = 2 * 2 ^ (n - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hm : 2 ≤ n - 1 := by
    by_contra h
    have h1 : n - 1 ≤ 1 := by omega
    have h2 : 2 ^ (n - 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  exact (GorensteinWalter.dihedral_mulAut_is_twoGroup hm).of_equiv (MulAut.congr e).symm

omit [Finite G] in
theorem isPGroup_mulAut_of_semidihedral {S₀ : Subgroup G}
    (hS₀ : AschbacherTheorem3.IsSemidihedralTwoGroup S₀) : IsPGroup 2 (MulAut S₀) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hS₀
  exact (Semidihedral.FieldFactorOne.semidihedral_automorphism_isPGroup hn).of_equiv
    (MulAut.congr e).symm

end CFSG.ComponentClassification.FooteLit.F5
