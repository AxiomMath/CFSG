module

public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineNumericRank

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
  (twoRank_le_one_of_not_twoRankAtLeastTwo)

theorem strongly_embedded_solvable (K : Type) [Group K] [Finite K] (M : Subgroup K)
    (hM : fusionStronglyEmbedded M) (hrank : 2 ≤ twoRank K) : Group.IsSolvable M := by
  have hn : CFSG.BenderSuzuki.IsStronglyEmbedded M := hM.to_native
  rcases theorem_SE M hn with hlow | hB
  · exfalso
    apply hlow
    apply twoRankAtLeastTwo_involutionCore_iff.mpr
    by_contra h
    have := twoRank_le_one_of_not_twoRankAtLeastTwo h
    omega
  have hindex : Odd (involutionCore K).index := hn.involutionCore_index_odd_of_bender hB
  obtain ⟨-, -, hborel⟩ := hB
  let L : Subgroup K := involutionCore K
  let O : Subgroup L := twoPrimeCore L
  let q := QuotientGroup.mk' O
  have hOodd : Odd (Nat.card O) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := L))
  let ML : Subgroup L := M.subgroupOf L
  have hML : ((M ⊓ L).subgroupOf L) = ML := Subgroup.inf_subgroupOf_right M L
  have hsolvML : Group.IsSolvable ML := by
    let f : ML →* ML.map q := q.subgroupMap ML
    have hfsurj : Function.Surjective f := q.subgroupMap_surjective ML
    have : Group.IsSolvable (ML.map q) := by
      have h := hborel.1
      rwa [hML] at h
    have hkerodd : Odd (Nat.card f.ker) := by
      have hle : (f.ker.map ML.subtype).map L.subtype ≤ O.map L.subtype := by
        rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨(w : L), ?_, rfl⟩
        have h1 : q (w : L) = 1 := congrArg Subtype.val hw
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective L.subtype_injective,
        Subgroup.card_map_of_injective ML.subtype_injective,
        Subgroup.card_map_of_injective L.subtype_injective] at hdvd
      exact hOodd.of_dvd_nat hdvd
    have : Group.IsSolvable f.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hkerodd
    exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])
  let LM : Subgroup M := L.subgroupOf M
  have hsolvLM : Group.IsSolvable LM := by
    let ι : LM →* ML :=
      { toFun := fun x => ⟨⟨((x : M) : K), x.property⟩, (x : M).property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y hxy
      have h : ((x : M) : K) = ((y : M) : K) := congrArg (fun w : ML => ((w : L) : K)) hxy
      exact Subtype.ext (Subtype.ext h)
    exact Group.isSolvable_of_isSolvable_injective hι
  have hquot : Group.IsSolvable (M ⧸ LM) := by
    have hodd : Odd (Nat.card (M ⧸ LM)) := by
      rw [← Subgroup.index_eq_card]
      exact hindex.of_dvd_nat (Subgroup.relIndex_dvd_index_of_normal L M)
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact (Group.isSolvable_iff_subgroup_quotient LM).mpr ⟨hsolvLM, hquot⟩

end CFSG.ComponentClassification.AschbacherStrongEmbedding
