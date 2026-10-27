module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneAutomorphisms
public import CFSG.Foundations.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem normal_conjugation_kernel_eq_centralizer
    (Q : Subgroup G) [Q.Normal] :
    (MulAut.conjNormal : G →* MulAut Q).ker = Subgroup.centralizer (Q : Set G) := by
  ext g
  change MulAut.conjNormal g = 1 ↔ g ∈ Subgroup.centralizer (Q : Set G)
  constructor
  · intro hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    have hfixed := congrArg (fun f : MulAut Q => ((f ⟨q, hq⟩ : Q) : G)) hg
    change g * q * g⁻¹ = q at hfixed
    exact (mul_inv_eq_iff_eq_mul.mp hfixed).symm
  · intro hg
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    change g * (q : G) * g⁻¹ = (q : G)
    rw [← (Subgroup.mem_centralizer_iff.mp hg q q.property), mul_inv_cancel_right]

omit [Finite G] in
theorem solvable_of_self_centralizing_normal_subgroup
    (Q : Subgroup G) [Q.Normal] [Group.IsSolvable (MulAut Q)]
    (hcentralizer : Subgroup.centralizer (Q : Set G) ≤ Q) :
    Group.IsSolvable G := by
  let conjugation : G →* MulAut Q := MulAut.conjNormal
  have hkernelQ : conjugation.ker ≤ Q := by
    rw [normal_conjugation_kernel_eq_centralizer]
    exact hcentralizer
  let kernel := conjugation.ker
  let : Group.IsSolvable kernel := Group.isSolvable_of_comm (by
    intro a b
    apply Subtype.ext
    have hb : (b : G) ∈ Subgroup.centralizer (Q : Set G) := by
      have := b.property
      change (b : G) ∈ (MulAut.conjNormal : G →* MulAut Q).ker at this
      rwa [normal_conjugation_kernel_eq_centralizer] at this
    exact Subgroup.mem_centralizer_iff.mp hb (a : G) (hkernelQ a.property))
  apply Group.isSolvable_of_ker_le_range kernel.subtype conjugation
  rw [kernel.subtype_range]

theorem full_core_eq_top_of_normal_two_subgroup_rank
    (S : Sylow 2 G) (Q : Subgroup G) [Q.Normal]
    (hQtwo : IsPGroup 2 Q) (hQrank : 2 ≤ Open.pRank 2 Q) :
    properTwoGenCoreGamma (S : Subgroup G) 2 = ⊤ := by
  have hQS := hQtwo.le_sylow_of_normal S
  have hnormalizer := (gamma_le_iff _ _ 2).mp le_rfl Q hQS hQrank
  rw [Subgroup.normalizer_eq_top] at hnormalizer
  exact top_le_iff.mp hnormalizer

theorem two_core_rank_le_one_of_proper_full_core
    (S : Sylow 2 G)
    (hproper : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    Open.pRank 2 (pCore 2 G) ≤ 1 := by
  by_contra hlarge
  exact hproper (full_core_eq_top_of_normal_two_subgroup_rank S (pCore 2 G)
    pCore_isPGroup (by omega))

theorem characteristic_two_solvable_of_two_core_rank_le_one
    (hchar : IsCharacteristicP 2 G)
    (hQrank : Open.pRank 2 (pCore 2 G) ≤ 1) : Group.IsSolvable G := by
  have hQrankInternal : twoRank (pCore 2 G) ≤ 1 := by
    change Open.pRank 2 (⊤ : Subgroup (pCore 2 G)) ≤ 1
    rwa [← pRank_subgroup_eq_internal_top 2 (by decide)]
  let : Group.IsSolvable (MulAut (pCore 2 G)) :=
    rank_one_two_group_automorphism_solvable (pCore 2 G) pCore_isPGroup hQrankInternal
  exact solvable_of_self_centralizing_normal_subgroup (pCore 2 G) hchar

theorem characteristic_two_rank_three_full_core
    (hchar : IsCharacteristicP 2 G) (hrank : 3 ≤ twoRank G) (S : Sylow 2 G) :
    properTwoGenCoreGamma (S : Subgroup G) 2 = ⊤ := by
  by_cases hlarge : 2 ≤ Open.pRank 2 (pCore 2 G)
  · exact full_core_eq_top_of_normal_two_subgroup_rank S (pCore 2 G)
      pCore_isPGroup hlarge
  · let : Group.IsSolvable G :=
      characteristic_two_solvable_of_two_core_rank_le_one hchar (by omega)
    exact solvable_rank_three_full_core hrank S

end CFSG.ProperTwoGeneratedCore
