module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LieType.Ree.LargeReeInvolutionFusion

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

section Basic

theorem rad_le_parabolic
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedOrbitComplementUnipotent K a j ≤ F4.reeLocalParabolic K a j := by
  rw [← reeParabolic_singleton]
  exact (ree_structure (K := K) (a := a) j).1.trans (reePosWeylGroup_le_reeParabolic j)

theorem parabolic_le_normalizer_rad
    (j : Fin F4.fixedOrbitCount) :
    F4.reeLocalParabolic K a j ≤
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) := by
  rw [← reeParabolic_singleton, reeParabolic_singleton_eq_sup]
  exact sup_le (reeFixedTorus_le_normalizer_complement j) (ree_structure (K := K) (a := a) j).2.1

theorem isPGroup_rad
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (j : Fin F4.fixedOrbitCount) : IsPGroup 2 ↥(F4.reeFixedOrbitComplementUnipotent K a j) :=
  IsPGroup.of_injective (isPGroup_reeFixedPosUnipotent ha hK)
    (Subgroup.inclusion (reeFixedOrbitComplementUnipotent_le j))
    (Subgroup.inclusion_injective _)

theorem perfectCore_parabolic
    (j : Fin F4.fixedOrbitCount) :
    perfectCore (F4.reeLocalParabolic K a j) = perfectCore (reePosWeylGroup K a j) := by
  rw [← reeParabolic_singleton]
  exact perfectCore_eq_of_commutator_le (reePosWeylGroup_le_reeParabolic j)
    (commutator_reeParabolic_le_reePosWeylGroup j)

theorem levi_hom
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : Fin F4.fixedOrbitCount)
    {M : Subgroup (ModGL F4.tag K)} (hMeq : F4.reeLocalBlock K a j = M) [IsSimpleGroup ↥M]
    (hnab : ∃ x y : ↥M, x * y ≠ y * x) :
    (∃ g : ↥(perfectCore (F4.reeLocalParabolic K a j)) →* ↥M, Function.Surjective g ∧
      ∀ x, g x = 1 → (x : ModGL F4.tag K) ∈ F4.reeFixedOrbitComplementUnipotent K a j) ∧
    M ≤ perfectCore (F4.reeLocalParabolic K a j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨hVN, hNV, hsup, hMnorm⟩ := ree_structure (K := K) (a := a) j
  rw [hMeq] at hsup hMnorm
  have hV2 := isPGroup_rad ha hK j
  have hMperf : ⁅M, M⁆ = M := perfect_of_isSimpleGroup_nonabelian hnab
  have hVM : F4.reeFixedOrbitComplementUnipotent K a j ⊓ M = ⊥ :=
    inf_eq_bot_of_simple hMnorm hV2 hMperf
  obtain ⟨g, hg, hk⟩ := exists_levi_hom hVN hNV hVM hsup le_rfl hMperf (perfectCore_le M)
  have hpc := perfectCore_parabolic (K := K) (a := a) j
  refine ⟨⟨g.comp (MulEquiv.subgroupCongr hpc).toMonoidHom,
    hg.comp (MulEquiv.subgroupCongr hpc).surjective, ?_⟩, ?_⟩
  · intro x hx
    have h1 : g (MulEquiv.subgroupCongr hpc x) = 1 := hx
    have h2 := hk _ h1
    rwa [MulEquiv.subgroupCongr_apply] at h2
  · have hMN : M ≤ reePosWeylGroup K a j := by
      rw [← hsup]
      exact le_sup_right
    exact (le_perfectCore_of_perfect hMN hMperf).trans (perfectCore_parabolic j).symm.le

end Basic

section SelfCentralizing

theorem selfCentralizing_zero
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeLocalParabolic K a ⟨0, by decide⟩ ⊓
        Subgroup.centralizer
          (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) ≤
      F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  intro x hx
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxΓ : x ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hxP).1
  have hL : sylowL a K 1 ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :=
    (blocks_mem (m := a) hK 0 0 0 0 0 0 1).2.2.2.2.2.2.1
  have hxL : x ∈ Subgroup.centralizer ({sylowL a K 1} : Set (ModGL F4.tag K)) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hL) hxC
  have hxT : x ∈ centralizerT K a := by
    have := reeGamma_inf_centralizer_tOne_eq (K := K) (a := a) hK
    rw [← this]
    exact Subgroup.mem_inf.2 ⟨hxΓ, hxL⟩
  obtain ⟨-, -, hC, -, -⟩ := centralizerT_kernel ha hK
  have hle : tKernel K a ≤ centralizerT K a := le_sup_left
  have hxQ : (⟨x, hxT⟩ : centralizerT K a) ∈
      (tKernel K a).subgroupOf (centralizerT K a) := by
    apply hC
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hyV : (y : ModGL F4.tag K) ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :=
      (Subgroup.mem_inf.1 hy).1
    have := Subgroup.mem_centralizer_iff.1 hxC y hyV
    exact Subtype.ext (by simpa using this)
  exact (Subgroup.mem_inf.1 hxQ).1

theorem selfCentralizing_one
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeLocalParabolic K a ⟨1, by decide⟩ ⊓
        Subgroup.centralizer
          (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) ≤
      F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  intro x hx
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxΓ : x ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hxP).1
  have hz : centralZ K a 1 ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ :=
    centralZ_mem_complement ha hK 1
  have hxz : x ∈ Subgroup.centralizer ({centralZ K a 1} : Set (ModGL F4.tag K)) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hz) hxC
  have hxT : x ∈ centralizerZ K a := by
    have := reeGamma_inf_centralizer_eq (K := K) (a := a) ha hK
    rw [← this]
    exact Subgroup.mem_inf.2 ⟨hxΓ, hxz⟩
  obtain ⟨-, -, hC, -, -⟩ := centralizerZ_kernel ha hK
  have hxQ : (⟨x, hxT⟩ : centralizerZ K a) ∈
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf (centralizerZ K a) := by
    apply hC
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hyV : (y : ModGL F4.tag K) ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := hy
    have := Subgroup.mem_centralizer_iff.1 hxC y hyV
    exact Subtype.ext (by simpa using this)
  exact hxQ

end SelfCentralizing

section Nonabelian

theorem nonabelian_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩,
      ∃ y ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩, x * y ≠ y * x := by
  refine ⟨sylowV a K 0 1 0 0 0 0 0 0 0 0 0 0, sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _,
    sylowL a K 1, (blocks_mem (m := a) hK 0 0 0 0 0 0 1).2.2.2.2.2.2.1, fun h => ?_⟩
  have := (sylowV_commute_sylowL_one_iff (m := a) (K := K) 0 1 0 0 0 0 0 0 0 0 0 0).1 h
  exact one_ne_zero this.1

theorem nonabelian_one
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩,
      ∃ y ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩, x * y ≠ y * x := by
  refine ⟨sylowV a K 0 0 0 0 0 1 0 0 0 0 0 0, ?_, sylowA a K 1, sylowA_mem_complement_one hK 1,
    fun h => ?_⟩
  · exact Subgroup.mem_inf.2 ⟨sylowV_rest_mem_rootSpan_one _ _ _ _ _ _ _ _ _,
      (Subgroup.mem_inf.1 (sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _)).2⟩
  · have := (sylowV_commute_sylowA_one_iff (m := a) (K := K) 0 0 0 0 0 1 0 0 0 0 0 0).1 h
    exact one_ne_zero this.2.2.1

end Nonabelian

section Assemble

theorem parabolicFacts_zero_of
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hC : F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊓
        Subgroup.centralizer
          (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) ≤
      ⁅F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩,
        F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩⁆)
    (hG : F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ≤
      ⁅F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩,
        perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩)⁆) :
    ParabolicFacts (F4.reeLocalParabolic K a ⟨0, by decide⟩)
      (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩) := by
  have hsimple : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
  obtain ⟨⟨h0eq, -, -⟩, -⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  obtain ⟨g, hg, hk⟩ := (levi_hom ha hK ⟨0, by decide⟩ (M := rankOneGroupOne K a) h0eq
    (isSimpleGroup_rankOneGroupOne ha hK).2).1
  exact ⟨rad_le_parabolic _, parabolic_le_normalizer_rad _, isPGroup_rad ha hK _,
    selfCentralizing_zero ha hK, hC, nonabelian_zero hK,
    Or.inr ⟨hG, ↥(rankOneGroupOne K a), inferInstance, g, hsimple, hg, hk⟩⟩

theorem parabolicFacts_one_of
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hC : F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊓
        Subgroup.centralizer
          (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) ≤
      ⁅F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩,
        F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩⁆)
    (hG : F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ≤
      ⁅F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩,
        perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩)⁆) :
    ParabolicFacts (F4.reeLocalParabolic K a ⟨1, by decide⟩)
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) := by
  have hsimple : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK).1
  obtain ⟨-, ⟨h1eq, -, -⟩⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  obtain ⟨g, hg, hk⟩ := (levi_hom ha hK ⟨1, by decide⟩ (M := rankOneGroupTwo K a) h1eq
    (isSimpleGroup_rankOneGroupTwo ha hK).2).1
  exact ⟨rad_le_parabolic _, parabolic_le_normalizer_rad _, isPGroup_rad ha hK _,
    selfCentralizing_one ha hK, hC, nonabelian_one hK,
    Or.inr ⟨hG, ↥(rankOneGroupTwo K a), inferInstance, g, hsimple, hg, hk⟩⟩

end Assemble

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4
