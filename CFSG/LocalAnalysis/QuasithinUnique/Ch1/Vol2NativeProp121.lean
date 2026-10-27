module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeFive
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Sporadic.J1
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open
open CFSG.Quasithin hiding lemma_1_2_1_three lemma_1_2_1_five

section Glue

theorem is121List_of_a38Types
    {X : Type} [Group X] [Finite X] (hX : A38Types X)
    (hns : ¬ Group.IsSolvable X) : Id2519.Is121List X := by
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    exact hns (Group.isSolvable_of_comm hc)
  have heven : 2 ∣ Nat.card X := by
    by_contra h2
    exact hns (CFSG.FeitThompson.isSolvable_of_odd_natCard X (Nat.odd_iff.mpr (by omega)))
  rcases hX with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hpsl⟩
  · obtain ⟨-, hsimple⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n hn
    refine ⟨hsimple, hnab, heven, Or.inl ⟨n, ?_, hn⟩⟩
    obtain ⟨⟨-, hf, -, h22, -⟩, -⟩ := hn
    by_contra hlt
    have hn1 : n = 1 := by omega
    exact h22 (by simp [hn1])
  · obtain ⟨-, hsimple⟩ := CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n hn
    refine ⟨hsimple, hnab, heven, Or.inr (Or.inl ⟨n, ?_, ?_, hn⟩)⟩
    · obtain ⟨-, a, -, -, -, -, hna, -, -⟩ := hn
      exact ⟨a, hna⟩
    · obtain ⟨-, a, ha, -, -, -, hna, -, -⟩ := hn
      omega
  · obtain ⟨e⟩ := hJ
    have hsimple : IsSimpleGroup X :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J1.isSimpleGroup_J1 e
    exact ⟨hsimple, hnab, heven, Or.inr (Or.inr (Or.inr ⟨e⟩))⟩
  · obtain ⟨-, hsimple⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 hpsl
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    exact ⟨hsimple, hnab, heven, Or.inr (Or.inr (Or.inl ⟨p, hp, by omega, hpsl⟩))⟩

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_modO2_of_mem_cComp {H L : Subgroup G} (hL : L ∈ cComp H) :
    ¬ Group.IsSolvable (↥L ⧸ CFSG.pCore 2 ↥L) := by
  intro hs
  have h2 : Group.IsSolvable ↥(CFSG.pCore 2 ↥L) := isSolvable_pCore_two_group ↥L
  have : Group.IsSolvable ↥L :=
    Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥L).subtype (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact not_isSolvable_of_mem_cComp hL this

omit [Finite G] in
theorem nat_card_conjugates_eq_ncard (H L : Subgroup G) :
    Nat.card {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate L h} =
      Set.ncard (conjSubgroupsBy H L) := by
  have hset : {L' : Subgroup G | ∃ h ∈ H, L' = CFSG.conjugate L h} = conjSubgroupsBy H L := by
    ext K'
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h⁻¹, H.inv_mem hh, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t⁻¹, H.inv_mem ht, ?_⟩
      simp [CFSG.conjugate]
  rw [← hset]
  exact Nat.card_coe_set_eq _

theorem prop121Three_of_a3
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) : Id2519.Prop121Three := by
  intro G _ _ _ _ hqtke H hH L hL
  rcases lemma_1_2_1_three hqtke.1 h37 h38 hH hL with hn | ⟨hcard, htypes⟩
  · exact Or.inl ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hL)).mp hn)
  · exact Or.inr ⟨(nat_card_conjugates_eq_ncard H L).trans hcard,
      is121List_of_a38Types htypes (not_isSolvable_modO2_of_mem_cComp hL)⟩

theorem prop121Five_of_core (h36 : A36CoreForSQTKCat) (hl2 : L2MultiplierFact) :
    Id2519.Prop121Five := by
  intro G _ _ _ _ hqtke H hH L hL hcent hE
  obtain ⟨E, hEL, hE2, hEcard⟩ := hE
  have hZ : pCoreOf 2 L ≤ centerOf L :=
    le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L) hcent
  have hm : 1 < CFSG.Open.pRank 2 L :=
    lt_of_lt_of_le one_lt_two
      (CFSG.SectionRank.le_pRank one_lt_two hEL hE2 (by rw [hEcard]; norm_num))
  exact lemma_1_2_1_five_core hqtke.1 h36 hl2 hH hL hZ hm

end Glue

end CFSG.QuasithinUnique.Vol2Native
