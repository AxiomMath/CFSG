module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieDelta5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem not_isDelta5_perfectCore_f4
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hodd : Odd f) (hf : 3 ≤ f) (hL : Is2F4 f ↥L) (hP : IsMaxParabolic2 L P) :
    ¬ IsDelta5Group ↥(perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isDelta5_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hL
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨hF0, hF1⟩ := F4.largeReeParabolicFacts a K ha hK
  refine not_isDelta5_perfectCore_of_equiv e ?_
  refine not_isDelta5_perfectCore_parabolic hU₀ (large_Ree_residualOvergroupsAt hK) (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  have hPC : F4.reeParabolic K a {f4Index j} ≤ F4.reeGamma K a := reeParabolic_le F4 K a _
  refine not_isDelta5_perfectCore_subgroupOf_of hPC ?_
  rw [reeParabolic_singleton (t := F4) (K := K) (a := a)]
  rcases hcases (f4Index j) with h | h
  · rw [h]
    exact hF0.not_isDelta5
  · rw [h]
    exact hF1.not_isDelta5

end CFSG.QuasithinUnique.A5.G3
