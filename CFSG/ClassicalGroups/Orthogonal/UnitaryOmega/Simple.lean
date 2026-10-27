module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
open CFSG.ComponentClassification.RankTwoClassical.ORigid
  (isSimpleGroup_statedOmega_quadPlus_of_three_le isSimpleGroup_statedOmega_quadMinus_of_two_le)

variable {f : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]

theorem isSimpleGroup_normOmega [Finite F] (E : QuadExt F K (unitaryInvolution K 2 f)) {k : ℕ}
    (hk : 1 ≤ k) : IsSimpleGroup ↥(normOmega E k) := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  rcases Nat.even_or_odd k with hke | hko
  · obtain ⟨e⟩ := nonempty_normOmega_mulEquiv_plus E hke
    have := isSimpleGroup_statedOmega_quadPlus_of_three_le (K := F) (k := k + 1)
      (by obtain ⟨j, rfl⟩ := hke; omega)
    exact e.isSimpleGroup
  · obtain ⟨b, c, hirr⟩ := CFSG.GroupTheory.WeirSylow.exists_irreducible_quadratic F
    obtain ⟨e⟩ := nonempty_normOmega_mulEquiv_minus E hko hirr
    have := isSimpleGroup_statedOmega_quadMinus_of_two_le (m := k + 1) (by omega) hirr
    exact e.isSimpleGroup

theorem isPerfect_normOmega [Finite F] (E : QuadExt F K (unitaryInvolution K 2 f)) {k : ℕ}
    (hk : 1 ≤ k) : Group.IsPerfect (normOmega E k) := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  rcases Nat.even_or_odd k with hke | hko
  · obtain ⟨e⟩ := nonempty_normOmega_mulEquiv_plus E hke
    haveI : Group.IsPerfect
        ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (k + 1) F)) :=
      CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := F) (n := k + 1)
        (by obtain ⟨j, rfl⟩ := hke; omega)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · obtain ⟨b, c, hirr⟩ := CFSG.GroupTheory.WeirSylow.exists_irreducible_quadratic F
    obtain ⟨e⟩ := nonempty_normOmega_mulEquiv_minus E hko hirr
    haveI : Group.IsPerfect
        ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (k + 1) F b c)) :=
      ⟨CFSG.ComponentClassification.RankTwoClassical.ORigid.commutator_statedOmega_quadMinus_eq_top
        (m := k + 1) (by omega) hirr⟩
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isSimpleGroup_normBlock
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr : 3 ≤ r)
    (S : Finset (Fin r)) (hS : S.Nonempty) :
    IsSimpleGroup ↥(normBlock E r S) := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  obtain ⟨e⟩ := nonempty_normOmega_mulEquiv_normBlock E hr S
  haveI : IsSimpleGroup ↥(normOmega E S.card) :=
    isSimpleGroup_normOmega E (by
      have := Finset.card_pos.mpr hS
      omega)
  exact e.symm.isSimpleGroup

theorem isPerfect_normBlock
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr : 3 ≤ r)
    (S : Finset (Fin r)) (hS : S.Nonempty) :
    Group.IsPerfect ↥(normBlock E r S) := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  obtain ⟨e⟩ := nonempty_normOmega_mulEquiv_normBlock E hr S
  haveI : Group.IsPerfect ↥(normOmega E S.card) :=
    isPerfect_normOmega E (by
      have := Finset.card_pos.mpr hS
      omega)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
