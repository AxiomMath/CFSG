module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Chief
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup
open scoped commutatorElement

variable {M : Type*} [Group M]

theorem setup_of_critical {p : ℕ} {T : Subgroup M} (hTn : T.Normal) (hTp : IsPGroup p ↥T)
    (hmax : ∀ N : Subgroup M, N.Normal → IsPGroup p ↥N → N ≤ T)
    (hcent : centralizer (T : Set M) ≤ T) {C : Subgroup ↥T}
    (hC : CFSG.SectionRank.Ccomm.IsThompsonCritical C) :
    Setup p T (C.map T.subtype) := by
  obtain ⟨hchar, -, hcomm, hcen⟩ := hC
  refine ⟨hTn, hTp, hmax, hcent, ?_, map_subtype_le C, ?_, ?_⟩
  · refine ⟨?_⟩
    intro a ha m
    obtain ⟨c, hc, rfl⟩ := ha
    have h := CFSG.SectionRank.Ccomm.char_apply_mem hchar (MulAut.conjNormal (H := T) m) hc
    exact ⟨_, h, by simp [MulAut.conjNormal_apply]⟩
  · rw [Subgroup.commutator_le]
    intro t ht a ha
    obtain ⟨c, hc, rfl⟩ := ha
    have h1 : ⁅(⟨t, ht⟩ : ↥T), c⁆ ∈ C ⊓ centralizer (C : Set ↥T) :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hc)
    refine Subgroup.mem_inf.mpr ⟨⟨_, h1.1, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro a' ⟨c', hc', rfl⟩
    have h2 := (Subgroup.mem_centralizer_iff.mp h1.2) c' hc'
    exact congrArg Subtype.val h2
  · rintro t ⟨htT, htc⟩
    have h1 : (⟨t, htT⟩ : ↥T) ∈ centralizer (C : Set ↥T) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have := (Subgroup.mem_centralizer_iff.mp htc) (c : M) ⟨c, hc, rfl⟩
      exact Subtype.ext this
    rw [hcen] at h1
    exact ⟨_, (Subgroup.mem_inf.mp h1).1, rfl⟩

theorem subgroupOf_map_critical (T : Subgroup M) (C : Subgroup ↥T) :
    (C.map T.subtype).subgroupOf T = C :=
  Subgroup.comap_map_eq_self_of_injective Subtype.val_injective C

theorem exists_setup [Finite M] {p : ℕ} [Fact p.Prime] {T : Subgroup M} (hTn : T.Normal)
    (hTp : IsPGroup p ↥T) (hmax : ∀ N : Subgroup M, N.Normal → IsPGroup p ↥N → N ≤ T)
    (hcent : centralizer (T : Set M) ≤ T) :
    ∃ A : Subgroup M, A ≤ T ∧ CFSG.SectionRank.Ccomm.IsThompsonCritical (A.subgroupOf T) ∧
      Setup p T A := by
  obtain ⟨C, hC⟩ := (CFSG.SectionRank.Ccomm.thompson_critical_subgroup hTp).1
  refine ⟨C.map T.subtype, map_subtype_le C, ?_, setup_of_critical hTn hTp hmax hcent hC⟩
  rw [subgroupOf_map_critical]
  exact hC

end CFSG.GH74.GLS.Stage2.Signalizer.L53
