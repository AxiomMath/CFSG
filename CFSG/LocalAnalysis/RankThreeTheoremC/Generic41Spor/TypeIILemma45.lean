module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PlaneInT
import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC KFactWeakClosureHeis
  GenericComponentClass u3_endgame)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

theorem typeII_two_le_pRank_of_heisenberg {p : ℕ} (hp : p.Prime) {T : Subgroup G}
    (hTc : Nat.card T = p ^ 3) (hTe : ∀ t ∈ T, t ^ p = 1) (hTn : ¬ IsMulCommutative T) :
    2 ≤ CFSG.Open.pRank p T := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hET, hE, hEcard, -⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.exists_isElemAbelian_card_sq_of_nonabelian hTc hTe hTn
  exact CFSG.HardMathSupport.Timmesfeld.Proving.le_pRank_of_elemAbelian_card hp.two_le hET hE hEcard

theorem j4_lemma45_G {P : Sylow 11 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX : ExtraFacts IsJ4Type 11 J4Shape) (hc : PointConfig IsJ4Type G 11 P M x J) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup (u3U0 P x J) S₁ ∧ ¬ S₁ ≤ M := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hUe, hUcard, hUS, hxU, hcomm, hZTcard, -⟩ := typeII_U0_facts hX hc
  obtain ⟨hTcard, hTexp, hTnab, -⟩ := typeII_T_structure hX hc
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hSC : u3S P x ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  have hZTT : u3ZT P x J ≤ u3T P x J := inf_le_left
  have hZTU : u3ZT P x J ≤ u3U0 P x J := le_sup_left
  have hZT : ∃ z ∈ u3U0 P x J ⊓ u3T P x J, z ≠ 1 := by
    have hne : u3ZT P x J ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hZTcard
      norm_num at hZTcard
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨(a : G), ⟨hZTU a.2, hZTT a.2⟩, fun h => ha1 (Subtype.ext h)⟩
  refine typeII_lemma45_lift hS hD1 hU0 hX.lemma45 hX.maximal
    (fun A B _ _ e h => ⟨h.1, h.2.map fun f => e.symm.trans f⟩) hc (typeII_two_le_pRank_of_heisenberg (by norm_num) hTcard hTexp hTnab) hUe hUcard hUS hxU
    hZT ?_
  intro X _ ρ K R U₀ hf
  refine ⟨?_, ?_⟩
  · obtain ⟨z, ⟨hzU, hzT⟩, hz1⟩ := hZT
    have hzC : z ∈ Subgroup.centralizer ({x} : Set G) := hSC (hTS hzT)
    intro h
    have hmem : ρ ⟨z, hzC⟩ ∈ U₀ ⊓ K := ⟨hf.U₀_mem ⟨z, hzC⟩ hzU, hf.K_mem ⟨z, hzC⟩ (hTJ hzT)⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hz1 (hf.inj ⟨z, hzC⟩ hzT hmem)
  · rintro u ⟨hu, -⟩ s hs
    obtain ⟨c, hcU, rfl⟩ := hf.U₀_ex u hu
    obtain ⟨d, hdT, rfl⟩ := hf.RK_le s hs
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm d (hTS hdT) c hcU)

theorem mcl_lemma45_G {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX : ExtraFacts IsMcLType 5 McLShape) (hc : PointConfig IsMcLType G 5 P M x J)
    {U : Subgroup G} (hU : IIPlane 5 P x J U)
    (hnc : ∃ a ∈ U ⊓ u3T P x J, ∃ t ∈ u3T P x J, t * a ≠ a * t) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hTcard, hTexp, hTnab, -⟩ := typeII_T_structure hX hc
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hTC : u3T P x J ≤ Subgroup.centralizer ({x} : Set G) := hTS.trans inf_le_right
  have ha : ∃ a ∈ U ⊓ u3T P x J, a ≠ 1 := by
    obtain ⟨a, ha, t, -, hne⟩ := hnc
    refine ⟨a, ha, fun h => hne ?_⟩
    rw [h]; simp
  refine typeII_lemma45_lift hS hD1 hU0 hX.lemma45 hX.maximal
    (fun A B _ _ e h => ⟨h.1, h.2.map fun f => e.symm.trans f⟩) hc (typeII_two_le_pRank_of_heisenberg (by norm_num) hTcard hTexp hTnab) hU.elem hU.card
    hU.le hU.mem ha ?_
  intro X _ ρ K R U₀ hf
  obtain ⟨a, ⟨haU, haT⟩, t, htT, hne⟩ := hnc
  refine ⟨ρ ⟨a, hTC haT⟩, ⟨hf.U₀_mem ⟨a, hTC haT⟩ haU, hf.K_mem ⟨a, hTC haT⟩ (hTJ haT)⟩,
    ρ ⟨t, hTC htT⟩, hf.T_le ⟨t, hTC htT⟩ htT, fun h => hne ?_⟩
  set ca : ↥(Subgroup.centralizer ({x} : Set G)) := ⟨a, hTC haT⟩ with hca
  set ct : ↥(Subgroup.centralizer ({x} : Set G)) := ⟨t, hTC htT⟩ with hct
  have hρe : ρ (ct * ca * ct⁻¹ * ca⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hmemT : ((ct * ca * ct⁻¹ * ca⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) ∈ u3T P x J := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (u3T P x J).mul_mem ((u3T P x J).mul_mem ((u3T P x J).mul_mem htT haT)
      ((u3T P x J).inv_mem htT)) ((u3T P x J).inv_mem haT)
  have h1 := hf.inj _ hmemT hρe
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)


end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
