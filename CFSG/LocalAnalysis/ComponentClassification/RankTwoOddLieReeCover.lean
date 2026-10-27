module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchur
public import CFSG.Walter.Ree.Model.JTHyp
public import CFSG.LieType.Ree.SmallReeModelSchreier

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem exists_sylow_two_isMulCommutative_of_reeTitsModel {G : Type} [Group G] {f : ℕ}
    (h : ReeTitsModel G .twistedG2 3 f) :
    ∃ T : Sylow 2 G, IsMulCommutative (T : Subgroup G) ∧ Nat.card (T : Subgroup G) = 8 := by
  obtain ⟨hfin, -, -, ⟨a, ha, rfl⟩, hiso⟩ := small_Ree_model_Schreier G 3 f h
  obtain ⟨-, a', ha', K, _, _, hK, hmod⟩ := h
  have haa : a' = a := by omega
  rw [haa] at hmod
  have := Fintype.ofFinite K
  have : CharP K G2.prime := charP_of_card_eq_prime_pow (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨e⟩ := hiso a K rfl hK hmod
  have : Finite (G2.reeGamma K a) := Finite.of_equiv G e.toEquiv
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
  obtain ⟨hE, hcard, S, hS⟩ := CFSG.Walter.Ree.Model.smallRee_E8_sylow hK hw₀
  have hScomm : IsMulCommutative (S : Subgroup (G2.reeGamma K a)) := hS ▸ hE.toIsMulCommutative
  have hScard : Nat.card (S : Subgroup (G2.reeGamma K a)) = 8 := hS ▸ hcard
  refine ⟨S.mapSurjective (f := (e.symm : G2.reeGamma K a →* G)) e.symm.surjective, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    infer_instance
  · rw [Sylow.coe_mapSurjective, Subgroup.card_map_of_injective e.symm.injective, hScard]

theorem smallReeTwoMultiplierTrivial : SmallReeTwoMultiplierTrivial := by
  intro P _ _ hP hZ ⟨f, hf⟩
  obtain ⟨T, hT, hcard⟩ := exists_sylow_two_isMulCommutative_of_reeTitsModel hf
  exact (CFSG.ComponentClassification.WalterSchur.walter_schur_two_part_holds P
    (Subgroup.center P) hP le_rfl hZ T hT).2 hcard.ge

end CFSG.ComponentClassification.RankTwoOddLie
