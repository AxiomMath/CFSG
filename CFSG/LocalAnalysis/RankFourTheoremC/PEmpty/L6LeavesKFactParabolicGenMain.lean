module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenClassical
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenSmall
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenU33
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenTwisted
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenRee
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenTits
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAType

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

theorem kFactParabolicGen_of_hasParGen
    (h : ∀ (S : Type) [Group S] [Finite S], IsChevSimple 2 S → ¬ fusionIsBenderGroup S →
      HasParGen S) : KFactParabolicGen := by
  intro A _ _ K W hK hB hW J hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hW.exists_sylow_eq_subgroupOf
  have hWK : W ≤ K := hW.le
  have hpg := (hasParGen_iff_forall.mp (h ↥K hK hB)) Q
  have hle : parabGen (Q : Subgroup ↥K) ≤ J.subgroupOf K := by
    refine parabGen_le_of_hyp Q fun Q' hQ'Q hQ'1 hN => ?_
    have hQ₂K : Q'.map K.subtype ≤ K := Subgroup.map_subtype_le Q'
    have hsub : (Q'.map K.subtype).subgroupOf K = Q' :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q'
    have hNQ₂ : ∀ a : ↥K, a ∈ normalizer (Q' : Set ↥K) ↔
        (a : A) ∈ normalizer ((Q'.map K.subtype : Subgroup A) : Set A) := by
      intro a
      have h1 := Subgroup.subgroupOf_normalizer_eq hQ₂K
      rw [hsub] at h1
      rw [← h1]
      exact Iff.rfl
    have hQ₂W : Q'.map K.subtype ≤ W := by
      have h1 : Q'.map K.subtype ≤ (Q : Subgroup ↥K).map K.subtype := Subgroup.map_mono hQ'Q
      rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWK] at h1
      exact h1
    have hQ₂1 : Q'.map K.subtype ≠ ⊥ := by
      intro hbot
      apply hQ'1
      rw [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at hbot
      exact eq_bot_iff.mpr hbot
    have hBor : normalizer (W : Set A) ⊓ K ≤
        normalizer ((Q'.map K.subtype : Subgroup A) : Set A) := by
      intro a ha
      have h1 : (⟨a, ha.2⟩ : ↥K) ∈ normalizer ((Q : Subgroup ↥K) : Set ↥K) := by
        rw [hQ, ← Subgroup.subgroupOf_normalizer_eq hWK]
        exact ha.1
      exact (hNQ₂ ⟨a, ha.2⟩).mp (hN h1)
    intro b hb
    have hbA := (hNQ₂ b).mp hb
    exact hJ _ hQ₂W hQ₂1 hBor ⟨hbA, b.2⟩
  intro k hk
  have : (⟨k, hk⟩ : ↥K) ∈ J.subgroupOf K := hle (hpg ▸ Subgroup.mem_top _)
  exact this

open CFSG.Assembly.LowTwoRank CFSG.Blueprint in
theorem hasParGen_of_isChevSimple_two
    {S : Type} [Group S] [Finite S] (h : IsChevSimple 2 S) (hnb : ¬ fusionIsBenderGroup S) :
    HasParGen S := by
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h with ⟨t, n, f, hm⟩ | ⟨e⟩ | h33
  · rcases hm with ⟨htc, hcl⟩ | ⟨-, htc, hce⟩ | ⟨-, htc, hrt⟩ | ⟨-, rfl, hsz⟩
    · refine hasParGen_of_statedClassicalModel hcl ?_ ?_
      · rintro ⟨rfl, rfl⟩
        exact hnb (CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isPSL hcl)
      · rintro ⟨rfl, rfl⟩
        have hf : 2 ≤ f := by
          obtain ⟨-, hf1, -, hne⟩ := hcl.1
          by_contra hlt
          have hf1' : f = 1 := by omega
          subst hf1'
          exact hne (by simp)
        exact hnb (CFSG.Quasithin.GoldMLA.fusionIsBenderGroup_of_isPSU3 hf hcl)
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hasParGen_of_chevalleyExceptionalModel_untwisted hce (by decide) (by decide)
      · exact hasParGen_of_chevalleyExceptionalModel_untwisted hce (by decide) (by decide)
      · exact hasParGen_of_chevalleyExceptionalModel_untwisted hce (by decide) (by decide)
      · exact hasParGen_of_chevalleyExceptionalModel_untwisted hce (by decide) (by decide)
      · exact hasParGen_of_chevalleyExceptionalModel_untwisted hce (by decide) (by decide)
      · exact hasParGen_of_chevalleyExceptionalModel_twisted hce (Or.inl rfl)
      · exact hasParGen_of_chevalleyExceptionalModel_twisted hce (Or.inr rfl)
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at htc
      rcases htc with rfl | rfl | rfl
      · obtain ⟨⟨-, -, -, hp3, -⟩, -⟩ := hrt
        omega
      · exact hasParGen_of_reeModel_twistedF4 hrt
      · exact hasParGen_of_titsModel hrt
    · exact absurd (CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isSz hsz) hnb
  · obtain ⟨e⟩ := e
    exact hasParGen_of_mulEquiv e.symm hasParGen_alt6
  · exact hasParGen_of_isPSU_three_three h33

end KPGen

theorem kFactParabolicGen_holds
    : KFactParabolicGen :=
  KPGen.kFactParabolicGen_of_hasParGen fun _ _ _ h hnb =>
    KPGen.hasParGen_of_isChevSimple_two h hnb

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
