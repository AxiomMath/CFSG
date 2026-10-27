module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLevi2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2c
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeRankOne
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersParabolic

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section ReeBlocks

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem ree_structure
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedOrbitComplementUnipotent K a j ≤ reePosWeylGroup K a j ∧
    reePosWeylGroup K a j ≤
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) ∧
    F4.reeFixedOrbitComplementUnipotent K a j ⊔ F4.reeLocalBlock K a j = reePosWeylGroup K a j ∧
    F4.reeLocalBlock K a j ≤
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) := by
  have hV : F4.reeFixedOrbitComplementUnipotent K a j ≤ F4.reeFixedPosUnipotent K a :=
    reeFixedOrbitComplementUnipotent_le j
  have hUN : F4.reeFixedPosUnipotent K a ≤ reePosWeylGroup K a j :=
    reeFixedPosUnipotent_le_reePosWeylGroup j
  have hUnorm : F4.reeFixedPosUnipotent K a ≤
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) :=
    reeFixedPosUnipotent_le_normalizer j
  have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) :=
    mem_normalizer_of_map_eq (map_conj_reeFixedOrbitComplementUnipotent j)
  have hnM : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      F4.reeLocalBlock K a j := canonicalRep_fixedOrbitElement_mem_reeLocalBlock j
  have hMnorm : F4.reeLocalBlock K a j ≤
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) := by
    refine sup_le ((reeFixedOrbitUnipotent_le j).trans hUnorm) ?_
    intro y hy
    rw [← map_conj_reeFixedOrbitUnipotent j] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact mul_mem (mul_mem hn (hUnorm (reeFixedOrbitUnipotent_le j hx))) (inv_mem hn)
  refine ⟨hV.trans hUN, ?_, ?_, hMnorm⟩
  · exact sup_le hUnorm ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hn))
  · refine le_antisymm (sup_le (hV.trans hUN) (reeLocalBlock_le_reePosWeylGroup j)) ?_
    refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 ?_))
    · rw [← reeFixedOrbitComplementUnipotent_sup j] at hu
      exact sup_le_sup_left (reeFixedOrbitUnipotent_le_reeLocalBlock j) _ hu
    · exact Subgroup.mem_sup_right hnM

theorem ree_levi_hom
    (hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a))
    (j : Fin F4.fixedOrbitCount) {M : Subgroup (ModGL F4.tag K)}
    (hMeq : F4.reeLocalBlock K a j = M) [IsSimpleGroup ↥M] (hnab : ∃ x y : ↥M, x * y ≠ y * x) :
    ∃ g : ↥(perfectCore ((F4.reeParabolic K a {j}).subgroupOf (F4.reeGamma K a))) →* ↥M,
      Function.Surjective g ∧ IsPGroup 2 g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨hVN, hNV, hsup, hMnorm⟩ := ree_structure (K := K) (a := a) j
  rw [hMeq] at hsup hMnorm
  have hVU : F4.reeFixedOrbitComplementUnipotent K a j ≤ F4.reeFixedPosUnipotent K a :=
    reeFixedOrbitComplementUnipotent_le j
  have hV2 : IsPGroup 2 ↥(F4.reeFixedOrbitComplementUnipotent K a j) :=
    IsPGroup.of_injective hUp (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  have hMperf : ⁅M, M⁆ = M := perfect_of_isSimpleGroup_nonabelian hnab
  have hNP := reePosWeylGroup_le_reeParabolic (K := K) (a := a) j
  exact exists_levi_hom_final (C := F4.reeGamma K a) hNP (reeParabolic_le F4 K a _)
    (perfectCore_eq_of_commutator_le hNP (commutator_reeParabolic_le_reePosWeylGroup j))
    hVN hNV hsup hMnorm hV2 hMperf

end ReeBlocks

section Main

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem a312For_F4
    {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hq : CFSG.IsQuasisimple ↥(F4.reeGamma K a))
    (h2F4 : Is2F4 (2 * a + 1) ↥(F4.reeGamma K a)) : A312For ↥(F4.reeGamma K a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hchar : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent K a)
      (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := hUsyl.2.1
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  refine a312For_of_rank2_ree (f := 2 * a + 1) hq hU₀ (large_Ree_residualOvergroupsAt hK) ?_
    ⟨a, by omega⟩ (by omega) h2F4 ?_
  ·
    intro j c hc
    have hUC' : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := hUC
    have hc' : (c : ModGL F4.tag K) ∈
        Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
      have key : ∀ v : ↥(F4.reeGamma K a), (v : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a ↔
          ((c * v * c⁻¹ : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ∈
            F4.reeFixedPosUnipotent K a := fun v => Subgroup.mem_normalizer_iff.1 hc v
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        exact (key ⟨u, hUC' hu⟩).1 hu
      · intro hcu
        have huC : u ∈ F4.reeGamma K a := by
          have : u = (c : ModGL F4.tag K)⁻¹ *
              ((c : ModGL F4.tag K) * u * (c : ModGL F4.tag K)⁻¹) * (c : ModGL F4.tag K) := by
            group
          rw [this]
          exact mul_mem (mul_mem (inv_mem c.2) (hUC' hcu)) c.2
        exact (key ⟨u, huC⟩).2 hcu
    obtain ⟨-, -, -, -, -, hNU, -⟩ := ree_Borel_self_normalizers F4 a K w₀ hw₀
    have hB : (c : ModGL F4.tag K) ∈ F4.reeFixedBorel K a := by
      rw [← hNU]
      exact ⟨c.2, hc'⟩
    exact reeFixedBorel_le_reeParabolic F4 K a _ hB
  · intro j
    have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
      intro i
      rcases i with ⟨i, hi⟩
      have hi2 : i < 2 := hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcases (f4Index j) with hj | hj
    ·
      left
      have : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
      obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
        (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq)
        (isSimpleGroup_rankOneGroupOne ha hK).2
      let e : ↥(rankOneGroupOne K a) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
        (rankOneEquivSL K a hK).symm
      refine Or.inr ⟨K, inferInstance, inferInstance, hchar, 2 * a + 1, hK, by omega,
        e.toMonoidHom.comp g, e.surjective.comp hg, ?_⟩
      have hkerEq : (e.toMonoidHom.comp g).ker = g.ker := by
        ext x
        simp only [MonoidHom.mem_ker]
        exact MulEquiv.map_eq_one_iff e
      rw [hkerEq]
      exact hk
    ·
      right
      have : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK).1
      obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
        (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq)
        (isSimpleGroup_rankOneGroupTwo ha hK).2
      let e : ↥(rankOneGroupTwo K a) ≃* CFSG.Blueprint.suzukiGroup a K :=
        rankOneEquivSuzuki K a ha hK
      refine ⟨a, K, inferInstance, inferInstance, ha, rfl, hK, e.toMonoidHom.comp g,
        e.surjective.comp hg, ?_⟩
      have hkerEq : (e.toMonoidHom.comp g).ker = g.ker := by
        ext x
        simp only [MonoidHom.mem_ker]
        exact MulEquiv.map_eq_one_iff e
      rw [hkerEq]
      exact hk

end Main

theorem f4
    : FamF4 := by
  intro X _ _ f hq hodd hf3 hX
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  subst hfa
  exact A312For.of_mulEquiv e (a312For_F4 ha hK (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)
    (Is2F4.of_mulEquiv e hX))

end CFSG.QuasithinUnique.Vol2Native.A312L
