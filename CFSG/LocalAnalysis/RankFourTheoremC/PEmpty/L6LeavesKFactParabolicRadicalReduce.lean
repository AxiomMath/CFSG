module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

namespace KPRad

theorem ne_bot_of_parabolic {A : Type} [Group A] {K K₀ U : Subgroup A} (hK₀K : K₀ ≤ K)
    (hUN : normalizer (U : Set A) ⊓ K ≤ K₀) (hne : K₀ ≠ K) : U ≠ ⊥ := by
  rintro rfl
  refine hne (le_antisymm hK₀K fun k hk => hUN ⟨?_, hk⟩)
  rw [Subgroup.normalizer_eq_top (H := (⊥ : Subgroup A))]
  exact Subgroup.mem_top k

theorem pCoreOf_ne_bot_of_overgroups {A : Type} [Group A] [Finite A] {K K₀ : Subgroup A}
    (hov : Overgroups ↥K) (hpar : IsParabolicTwo A K K₀) (hne : K₀ ≠ K) :
    pCoreOf 2 K₀ ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK₀K, U, hU, hUN⟩ := hpar
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  have hUK₀ : U ≤ K₀ := fun u hu => hUN ⟨Subgroup.le_normalizer hu, hU.le hu⟩
  have hU1 : U ≠ ⊥ := ne_bot_of_parabolic hK₀K hUN hne
  have hQJ : (Q : Subgroup ↥K) ≤ K₀.subgroupOf K := by
    rw [hQ]
    exact fun u hu => hUK₀ hu
  have hJ : K₀.subgroupOf K ≠ ⊤ := fun h =>
    hne (le_antisymm hK₀K (Subgroup.subgroupOf_eq_top.mp h))
  have hchar : CharTwo (K₀.subgroupOf K) :=
    hov _ _ (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Q) hQJ hJ
  intro hcore
  have hYcore : pCoreOf 2 (K₀.subgroupOf K) = ⊥ := by
    have h1 := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype 2 K (K₀.subgroupOf K)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK₀K, hcore,
      Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at h1
    exact le_bot_iff.mp h1
  have hYbot : K₀.subgroupOf K = ⊥ := by
    refine le_bot_iff.mp fun y hy => ?_
    have hcent : y ∈ Subgroup.centralizer (pCoreOf 2 (K₀.subgroupOf K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have : h = 1 := by
        rw [hYcore] at hh
        exact Subgroup.mem_bot.mp hh
      rw [this, one_mul, mul_one]
    have hmem : y ∈ pCoreOf 2 (K₀.subgroupOf K) := hchar ⟨hy, hcent⟩
    rwa [hYcore] at hmem
  apply hU1
  rw [hYbot] at hQJ
  have hUb : U.subgroupOf K = ⊥ := hQ.symm.trans (le_bot_iff.mp hQJ)
  have h2 := Subgroup.subgroupOf_map_subtype U K
  rw [hUb, Subgroup.map_bot, inf_eq_left.mpr hU.le] at h2
  exact h2.symm

end KPRad

theorem kFactParabolicRadical_of_overgroups
    (h : ∀ (S : Type) [Group S] [Finite S], IsChevSimple 2 S → Overgroups S) :
    KFactParabolicRadical :=
  fun _ _ _ _ _ hK _ hpar hne => KPRad.pCoreOf_ne_bot_of_overgroups (h _ hK) hpar hne

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
