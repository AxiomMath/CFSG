module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalizerClassDefect
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPBlockDefect

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem centralNormalizerCoefficientProjection_conjugacyClassSum
    (ring : Subring ℂ) (p : ℕ) [Fact p.Prime] (P : Subgroup G)
    (x : Subgroup.normalizer (P : Set G)) (hx : classDefectAt p P x.val) :
    centralNormalizerCoefficientProjection ring P (Subgroup.normalizer (P : Set G))
        (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
        (centralConjugacyClassSum ring (ConjClasses.mk x.val)) =
      centralConjugacyClassSum ring (ConjClasses.mk x) := by
  apply Subtype.ext
  ext n
  rw [centralNormalizerCoefficientProjection_coeff]
  change (if n.val ∈ Subgroup.centralizer (P : Set G) then
      (conjugacyClassSum (ring := ℂ) (ConjClasses.mk x.val)).coeff n.val else 0) =
    (conjugacyClassSum (ring := ℂ) (ConjClasses.mk x)).coeff n
  rw [conjugacyClassSum_coeff, conjugacyClassSum_coeff]
  have hiff := exact_defect_class_intersection p P x n hx
  by_cases hn : n.val ∈ Subgroup.centralizer (P : Set G)
  · rw [ite_eq_left hn]
    by_cases hc : ConjClasses.mk n.val = ConjClasses.mk x.val
    · rw [ite_eq_left hc, ite_eq_left (hiff.mp ⟨hc, hn⟩)]
    · rw [ite_eq_right hc, ite_eq_right fun h => hc (hiff.mpr h).1]
  · rw [ite_eq_right hn, ite_eq_right fun h => hn (hiff.mpr h).2]

theorem defect_normalizer_brauer_preimage_exact_defect
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (P : Subgroup G) (hP : IsPGroup p P) (label : basis.index)
    (hdefect : coefficientBlockDefect basis ideal p label P)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (P : Set G)))
    (localLabel : localBasis.index)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.normalizer (P : Set G))
      (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl localBasis localLabel =
        centralCharacterResidueHom basis ideal label) :
    coefficientBlockDefect localBasis ideal p localLabel
      (P.subgroupOf (Subgroup.normalizer (P : Set G))) := by
  obtain ⟨X, hX, hXres⟩ := hdefect.1
  obtain ⟨x, hxX, hx⟩ := (classDefect_iff_exists_at p X P).mp hX
  have hxC : x ∈ Subgroup.centralizer (P : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hx.1 hy)
  set xN : Subgroup.normalizer (P : Set G) :=
    ⟨x, Subgroup.centralizer_le_normalizer (P : Set G) hxC⟩ with hxN
  have hLdefect : classDefect p (ConjClasses.mk xN)
      (P.subgroupOf (Subgroup.normalizer (P : Set G))) :=
    classDefectAt_classDefect (classDefectAt_subgroup p _ P Subgroup.le_normalizer xN hx)
  have hLres : centralCharacterResidueHom localBasis ideal localLabel
      (centralConjugacyClassSum _ (ConjClasses.mk xN)) ≠ 0 := by
    have e := congrArg (fun f => f (centralConjugacyClassSum (localizedComplexIntegerRing ideal) X))
      hbrauer
    change centralCharacterResidueHom localBasis ideal localLabel
      (centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal) P
        (Subgroup.normalizer (P : Set G))
        (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
        (centralConjugacyClassSum _ X)) = _ at e
    rw [← hxX, centralNormalizerCoefficientProjection_conjugacyClassSum _ p P xN hx] at e
    rw [e, hxX]
    exact hXres
  obtain ⟨Q, hQ⟩ := coefficientBlockDefect_exists localBasis ideal p localLabel
  have hPN : IsPGroup p (P.subgroupOf (Subgroup.normalizer (P : Set G))) := hP.comap_subtype
  have hle : P.subgroupOf (Subgroup.normalizer (P : Set G)) ≤ Q :=
    normal_p_le_coefficientBlockDefect localBasis ideal p _ hPN hQ
  obtain ⟨g, hg⟩ := hQ.2 _ _ hLdefect hLres
  have hcard : Nat.card Q ≤ Nat.card (P.subgroupOf (Subgroup.normalizer (P : Set G))) := by
    rw [← conjugation_subgroup_card Q g]
    exact Subgroup.card_le_of_le hg
  rw [Subgroup.eq_of_le_of_card_ge hle hcard]
  exact hQ

end CFSG.Semidihedral.Principal
