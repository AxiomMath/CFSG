module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_normalized_by_pGroup {q : ℕ} (hq : q.Prime) {Q Y : Subgroup G}
    (hQ : IsPGroup q Q) (hQY : Q ≤ normalizer (Y : Set G)) (hY : q.Coprime (Nat.card Y)) :
    ∃ A : Subgroup G, IsSylowOf 2 A Y ∧ Q ≤ normalizer (A : Set G) := by
  classical
  let φ := ambientSubgroupActionHom Q Y hQY
  let _ : MulDistribMulAction Q Y := MulDistribMulAction.compHom Y φ
  obtain ⟨S, hS⟩ := coprime_pGroup_has_invariant_sylow q hq hQ hY 2 Nat.prime_two
  have hSinv : ∀ g : Q, (S : Subgroup Y).map (φ g).toMonoidHom = S := by
    intro g
    have h := congrArg (fun T : Sylow 2 Y => (T : Subgroup Y)) (hS g)
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h
    exact h
  exact ⟨(S : Subgroup Y).map Y.subtype, ⟨S, rfl⟩,
    (ambient_subgroup_action_image_invariant_iff Q Y hQY S).1 hSinv⟩

theorem isSylowOf_of_maximalInvariantTwoIn {q : ℕ} (hq : q.Prime) {Q Y A : Subgroup G}
    (hQ : IsPGroup q Q) (hQY : Q ≤ normalizer (Y : Set G)) (hY : q.Coprime (Nat.card Y))
    (hA : invariantTwoMaximalWithin Q Y A) : IsSylowOf 2 A Y := by
  classical
  let action := ambientSubgroupActionHom Q Y hQY
  have hAY := hA.1
  have hInternalGroup : IsPGroup 2 (A.subgroupOf Y) :=
    hA.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hAY).symm
  have hInvariant : ∀ actingElement : Q,
      (A.subgroupOf Y).map (action actingElement).toMonoidHom = A.subgroupOf Y :=
    (ambient_subgroup_action_invariant_iff Q Y A hQY hAY).mpr hA.2.2.1
  have hMaximal : ∀ larger : Subgroup Y, IsPGroup 2 larger →
      (∀ actingElement : Q, larger.map (action actingElement).toMonoidHom = larger) →
      A.subgroupOf Y ≤ larger → larger = A.subgroupOf Y := by
    intro larger hgroup hfixed hinclusion
    have himageInvariant := (ambient_subgroup_action_image_invariant_iff Q Y hQY larger).mp hfixed
    have himageLe : A ≤ larger.map Y.subtype := by
      have himage := Subgroup.map_mono (f := Y.subtype) hinclusion
      rwa [Subgroup.map_subgroupOf_eq_of_le hAY] at himage
    have hequal := hA.2.2.2 (larger.map Y.subtype) (Subgroup.map_subtype_le _)
      (hgroup.map Y.subtype) himageInvariant himageLe
    apply Subgroup.map_injective Y.subtype_injective
    rwa [Subgroup.map_subgroupOf_eq_of_le hAY]
  obtain ⟨S, hS⟩ := coprime_maximal_invariant_prime_subgroup_is_sylow action q hq hQ hY 2
    Nat.prime_two (A.subgroupOf Y) hInternalGroup hInvariant hMaximal
  refine ⟨S, ?_⟩
  rw [hS, Subgroup.map_subgroupOf_eq_of_le hAY]

theorem exists_isSylowOf_normalized_containing {q : ℕ} (hq : q.Prime) {Q Y A : Subgroup G}
    (hQ : IsPGroup q Q) (hQY : Q ≤ normalizer (Y : Set G)) (hY : q.Coprime (Nat.card Y))
    (hAY : A ≤ Y) (hA : IsPGroup 2 A) (hQA : Q ≤ normalizer (A : Set G)) :
    ∃ B : Subgroup G, A ≤ B ∧ IsSylowOf 2 B Y ∧ Q ≤ normalizer (B : Set G) := by
  obtain ⟨B, hAB, hB⟩ := exists_invariantTwoMaximalWithin_containing Q Y A hAY hA hQA
  exact ⟨B, hAB, isSylowOf_of_maximalInvariantTwoIn hq hQ hQY hY hB, hB.2.2.1⟩

theorem exists_mem_centralizer_conj_eq_of_isSylowOf {q : ℕ} (hq : q.Prime) {Q Y A B : Subgroup G}
    (hQ : IsPGroup q Q) (hQY : Q ≤ normalizer (Y : Set G)) (hY : q.Coprime (Nat.card Y))
    (hA : IsSylowOf 2 A Y) (hB : IsSylowOf 2 B Y) (hQA : Q ≤ normalizer (A : Set G))
    (hQB : Q ≤ normalizer (B : Set G)) :
    ∃ c : G, c ∈ Y ∧ c ∈ centralizer (Q : Set G) ∧ A.map (MulAut.conj c).toMonoidHom = B := by
  classical
  let action := ambientSubgroupActionHom Q Y hQY
  have hAY := hA.le
  have hBY := hB.le
  have hAInternal : IsPGroup 2 (A.subgroupOf Y) :=
    hA.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hAY).symm
  have hBInternal : IsPGroup 2 (B.subgroupOf Y) :=
    hB.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hBY).symm
  have hAInvariant : ∀ actingElement : Q,
      (A.subgroupOf Y).map (action actingElement).toMonoidHom = A.subgroupOf Y :=
    (ambient_subgroup_action_invariant_iff Q Y A hQY hAY).mpr hQA
  have hBInvariant : ∀ actingElement : Q,
      (B.subgroupOf Y).map (action actingElement).toMonoidHom = B.subgroupOf Y :=
    (ambient_subgroup_action_invariant_iff Q Y B hQY hBY).mpr hQB
  have hMaximal (S : Subgroup G) (hS : IsSylowOf 2 S Y) (larger : Subgroup Y)
      (hgroup : IsPGroup 2 larger) (hinclusion : S.subgroupOf Y ≤ larger) :
      larger = S.subgroupOf Y := by
    have himageLe : S ≤ larger.map Y.subtype := by
      have himage := Subgroup.map_mono (f := Y.subtype) hinclusion
      rwa [Subgroup.map_subgroupOf_eq_of_le hS.le] at himage
    have hequal := hS.eq_of_le himageLe (Subgroup.map_subtype_le _) (hgroup.map Y.subtype)
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hS.le]
    exact hequal
  obtain ⟨conjugator, hconjugator, hfixed⟩ :=
    coprime_maximal_invariant_prime_subgroups_fixed_conjugator action q hq hQ hY 2
      Nat.prime_two (A.subgroupOf Y) (B.subgroupOf Y) hAInternal hAInvariant
      (fun larger hg _ hi => hMaximal A hA larger hg hi) hBInternal hBInvariant
      (fun larger hg _ hi => hMaximal B hB larger hg hi)
  refine ⟨conjugator, conjugator.property, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro actingElement helement
    have hambient := congrArg Subtype.val (hfixed ⟨actingElement, helement⟩)
    rw [ambientSubgroupActionHom_apply_coe] at hambient
    exact mul_inv_eq_iff_eq_mul.mp hambient
  · have hmapped := congrArg (fun subgroup : Subgroup Y => subgroup.map Y.subtype) hconjugator
    have hmaps : Y.subtype.comp (MulAut.conj conjugator).toMonoidHom =
        (MulAut.conj (conjugator : G)).toMonoidHom.comp Y.subtype := by
      ext element
      rfl
    rw [Subgroup.map_map, hmaps, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hAY, Subgroup.map_subgroupOf_eq_of_le hBY] at hmapped
    exact hmapped

end CFSG.LocalAnalysis.RankThreeTheoremC
