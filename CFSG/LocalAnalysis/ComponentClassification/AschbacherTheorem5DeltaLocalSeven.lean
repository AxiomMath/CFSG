module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSix

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

open SectionSix SectionSix.BarTools DeltaLocal DeltaLocal.RankOne

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace DeltaLocal.Seven

theorem pRank_le_bar {Y : Subgroup G} (hYH : Y ≤ Subgroup.normalizer (D : Set G)) :
    CFSG.Open.pRank 2 Y ≤ CFSG.Open.pRank 2 (bar D Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) Y
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hcard
  have hEH : E ≤ Subgroup.normalizer (D : Set G) := hEY.trans hYH
  refine CFSG.SectionRank.le_pRank (by norm_num) (bar_mono D hEY)
    (CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hE _) (toBar D)) ?_
  rw [card_bar_of_isPGroup hE2 hEH, hcard]

theorem isSemisimple_bar (hyp : Hyp61 G D r Abar) (i : Fin r) :
    aschbacherThm5IsSemisimple (bar D (aschbacherThm5Preimage D (Abar i))) := by
  obtain ⟨m, K, hm, hK, hcomm, hKgen⟩ := bar_factor_components hyp i
  exact ⟨m, K, hm, fun l => ⟨(hK l).2, (hK l).1.2.2⟩, hcomm, hKgen⟩

theorem two_le_pRank_inter (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {U : Subgroup G} (hU : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g)) (i : Fin r) :
    2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  have hAH : A ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have h66 : 2 ≤ CFSG.Open.pRank 2 A := lemma_6_6 h3 hin hC ⟨_, g, rfl, hg, U, hU⟩ i
  obtain ⟨hUH, hUel, hU4, hUC⟩ := id hU
  have hUb4 := isFourGroup_bar hUH hUel hU4
  have hUbL := bar_le_normalizer (lemma_6_5_one hC hg hU i) hAH
  have hcj : 2 ≤ CFSG.Open.pRank 2
      (AschbacherKnownGroup.centralizerJoin (bar D U) (bar D A)) := by
    by_contra hlt
    push Not at hlt
    have h1 := hin.lemma_3_8 (bar D A) (bar D U) (isSemisimple_bar hC.hyp i) hUbL hUb4
      (by omega)
    have h2 := (pRank_le_bar hAH).trans h1.le
    omega
  set X := ⨆ (v : G) (_ : v ∈ U) (_ : v ≠ 1), A ⊓ Subgroup.centralizer ({v} : Set G) with hXdef
  have hXH : X ≤ H := iSup₂_le fun v _ => iSup_le fun _ => inf_le_left.trans hAH
  have hXA : X ≤ A ⊓ rightConjugate H g :=
    iSup₂_le fun v hv => iSup_le fun hv1 => le_inf inf_le_left (inf_le_right.trans (hUC v hv hv1))
  have hle : AschbacherKnownGroup.centralizerJoin (bar D U) (bar D A) ≤ bar D X := by
    refine iSup₂_le fun u hu => iSup_le fun hu1 => ?_
    obtain ⟨v, hvU, rfl⟩ := (mem_bar_iff D U u).mp hu
    have hv1 : (v : G) ≠ 1 := by
      intro h
      apply hu1
      rw [show v = 1 from Subtype.ext h, map_one]
    have hvo : orderOf (v : G) = 2 := orderOf_eq_prime (hUel.2 _ hvU) hv1
    rw [← bar_inf_centralizer (core_le_preimage D _) v.2 hvo]
    exact bar_mono D (le_iSup₂_of_le (v : G) hvU (le_iSup_of_le hv1 le_rfl))
  calc 2 ≤ CFSG.Open.pRank 2 (AschbacherKnownGroup.centralizerJoin (bar D U) (bar D A)) := hcj
    _ ≤ CFSG.Open.pRank 2 (bar D X) := CFSG.SectionRank.pRank_mono (by norm_num) hle
    _ ≤ CFSG.Open.pRank 2 X := pRank_bar_le hXH le_rfl
    _ ≤ CFSG.Open.pRank 2 (A ⊓ rightConjugate H g) := CFSG.SectionRank.pRank_mono (by norm_num) hXA

theorem mem_fourGroupsInto_conj (hC : Counterexample G D r Abar) {g : G} (i : Fin r)
    {V : Subgroup G} (hVA : V ≤ aschbacherThm5Preimage D (Abar i) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hVel : IsElemAbelian 2 V) (hV4 : Nat.card V = 4) :
    V ∈ fourGroupsInto (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      (rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) g⁻¹) := by
  obtain ⟨j, hji⟩ := Strong.exists_ne_index (two_le hC) i
  refine ⟨?_, hVel, hV4, fun v hv hv1 => ?_⟩
  · rw [normalizer_rightConjugate]
    exact hVA.trans inf_le_right
  · rw [Six.conj_normalizer_inv]
    exact centralizer_le hC j ⟨1, by rw [pow_one]; exact hVel.2 v hv⟩ hv1
      (centralizes_of_mem_centralizing (factor_le_centralizing hC.hyp.hcomm hji (hVA hv).1))

end DeltaLocal.Seven

theorem lemma_6_7 (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (i : Fin r) :
    2 ≤ CFSG.Open.pRank 2 (rightConjugate (aschbacherThm5Preimage D (Abar i)) g ⊓
      Subgroup.normalizer (D : Set G)) ∧
    2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g) ∧
    ∃ U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g),
      U ≤ rightConjugate (aschbacherThm5Preimage D (Abar i)) g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hg, U, hU⟩ := hΔ
  have h2 := Seven.two_le_pRank_inter h3 hin hC hg hU i
  obtain ⟨V, hVA, hVel, hV4⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) h2
  have hV := Seven.mem_fourGroupsInto_conj hC i hVA hVel (by rw [hV4]; norm_num)
  have hC' := hC.conj g
  have hinv := Six.conj_normalizer_inv (D := D) g
  have hH' := normalizer_rightConjugate D g
  have hg' : rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      g⁻¹ ≠ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    rw [hinv, hH']
    exact Ne.symm hg
  have h2' := Seven.two_le_pRank_inter h3 hin hC' hg' hV i
  rw [preimage_conjFactors, hinv] at h2'
  refine ⟨h2', h2, ?_⟩
  obtain ⟨W, hWA, hWel, hW4⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) h2'
  obtain ⟨j, hji⟩ := Strong.exists_ne_index (two_le hC) i
  refine ⟨W, ⟨hWA.trans inf_le_right, hWel, by rw [hW4]; norm_num, fun w hw hw1 => ?_⟩,
    hWA.trans inf_le_left⟩
  have hwA' : w ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i) := by
    rw [preimage_conjFactors]
    exact (hWA hw).1
  have h1 := centralizer_le hC' j ⟨1, by rw [pow_one]; exact hWel.2 w hw⟩ hw1
    (centralizes_of_mem_centralizing (factor_le_centralizing hC'.hyp.hcomm hji hwA'))
  rwa [hH'] at h1

end CFSG.ComponentClassification.AschbacherTheorem5
