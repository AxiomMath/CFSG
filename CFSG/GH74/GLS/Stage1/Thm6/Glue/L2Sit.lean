module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Data
public import CFSG.GH74.GLS.IVK.Statements.Sec1

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] (x : G) (Kb : Subgroup (CentralizerBar x)) [Kb.Normal]

structure SitFacts {F : Type} [Field F] [Finite F] (e : ↥Kb ≃* IVK.L2 F)
    (N : IVK.L2Notation e) (T : Subgroup G) : Prop where
  hF : IVK.L2Field F
  sylow : IsSylow2In T (Cx x)
  hTN : ∀ g ∈ T, phig x Kb g ∈ (N.T : Subgroup (MulAut ↥Kb))
  hPN : ∀ a : MulAut ↥Kb, a ∈ N.P ↔ ∃ g ∈ Pg x Kb T, phig x Kb g = a

theorem exists_sylow_bar {T : Subgroup G} (hT : IsSylow2In T (Cx x)) :
    ∃ Tb : Sylow 2 (CentralizerBar x), (Tb : Subgroup (CentralizerBar x)) =
      (T.subgroupOf (Cx x)).map (QuotientGroup.mk' (Ox x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(T.subgroupOf (Cx x)) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  let Ts : Sylow 2 ↥(Cx x) := hp.toSylow hT.2.2
  exact ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective (Ox x)) Ts, rfl⟩

theorem sitFacts_of_general (hgen : IVK.IVK_1_2_general) {F : Type} [Field F] [Finite F]
    (hF : IVK.L2Field F) (e0 : ↥Kb ≃* IVK.L2 F) {T : Subgroup G} (hT : IsSylow2In T (Cx x)) :
    ∃ (e : ↥Kb ≃* IVK.L2 F) (N : IVK.L2Notation e), SitFacts x Kb e N T := by
  obtain ⟨Tb, hTb⟩ := exists_sylow_bar x hT
  obtain ⟨e, N, h1, h2⟩ := hgen F hF (CentralizerBar x) Kb ⟨e0⟩ Tb
  refine ⟨e, N, ⟨hF, hT, ?_, ?_⟩⟩
  · intro g hg
    have hgC := hT.1 hg
    apply h1
    refine ⟨QuotientGroup.mk ⟨g, hgC⟩, ?_, ?_⟩
    · rw [hTb]
      exact ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    · simp [phig, pr_of_mem x hgC]
  · intro a
    constructor
    · intro ha
      rw [← h2] at ha
      obtain ⟨h, ⟨hTb', hK⟩, rfl⟩ := ha
      rw [hTb] at hTb'
      obtain ⟨t, ht, rfl⟩ := hTb'
      refine ⟨t.1, ⟨Subgroup.mem_subgroupOf.1 ht, ?_⟩, ?_⟩
      · exact (mem_Kg x Kb).2 ⟨t.2, by rw [pr_of_mem x t.2]; exact hK⟩
      · simp [phig, pr_of_mem x t.2]
    · rintro ⟨g, ⟨hgT, hgK⟩, rfl⟩
      rw [← h2]
      have hgC := ((mem_Kg x Kb).1 hgK).1
      refine ⟨QuotientGroup.mk ⟨g, hgC⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [hTb]; exact ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.2 hgT, rfl⟩
      · have := ((mem_Kg x Kb).1 hgK).2
        rwa [pr_of_mem x hgC] at this
      · simp [phig, pr_of_mem x hgC]

end CFSG.GH74.GLS.Stage1.Thm6.Glue
