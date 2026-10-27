module

public import CFSG.LocalAnalysis.LargeEvenClassification.LocalCore
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCore

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem subgroup_le_normalizer_own_core {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (prime : ℕ) (SubgroupOfAmbient : Subgroup Ambient) :
    SubgroupOfAmbient ≤ Subgroup.normalizer (pCoreOf prime SubgroupOfAmbient : Set Ambient) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le prime SubgroupOfAmbient)).mp
    (pCoreOf_subgroupOf_normal prime SubgroupOfAmbient)

theorem nontrivial_core_local_container {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (SubgroupOfAmbient : Subgroup Ambient)
    (hcore : pCoreOf 2 SubgroupOfAmbient ≠ ⊥) :
    ∃ Local : Subgroup Ambient, IsTwoLocal Local ∧ SubgroupOfAmbient ≤ Local := by
  exact ⟨Subgroup.normalizer (pCoreOf 2 SubgroupOfAmbient : Set Ambient),
    ⟨pCoreOf 2 SubgroupOfAmbient, hcore, pCoreOf_isPGroup 2 SubgroupOfAmbient, rfl⟩,
    subgroup_le_normalizer_own_core 2 SubgroupOfAmbient⟩

theorem weak_core_one_sylow_local {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (Parent : Sylow prime Ambient)
    (hrank : 3 ≤ pRank prime (⊤ : Subgroup Ambient)) (Local : Subgroup Ambient)
    (hlocal : IsTwoLocal Local) (hcoreLe : weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) ≤ Local) :
    WeakCoreLocal prime Ambient := by
  let : Fact prime.Prime := ⟨hprime⟩
  refine ⟨hrank, ?_⟩
  intro OtherParent
  obtain ⟨conjugator, hconjugate⟩ := MulAction.exists_smul_eq Ambient Parent OtherParent
  let coordinates := MulAut.conj conjugator
  have hparent : (Parent : Subgroup Ambient).map coordinates.toMonoidHom =
      (OtherParent : Subgroup Ambient) := by
    rw [← hconjugate]
    have hcoe := Sylow.pointwise_smul_def (g := MulAut.conj conjugator) (P := Parent)
    rw [Subgroup.pointwise_smul_def] at hcoe
    rw [Sylow.smul_def]
    exact hcoe.symm
  refine ⟨Local.map coordinates.toMonoidHom, isTwoLocal_map_mulEquiv coordinates Local hlocal, ?_⟩
  have hle := Subgroup.map_mono (f := coordinates.toMonoidHom) hcoreLe
  rw [weak_core_map_mulEquiv hprime.one_lt coordinates, hparent] at hle
  exact hle

theorem nontrivial_weak_core_implies_local {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Parent : Sylow prime Ambient)
    (hrank : 3 ≤ pRank prime (⊤ : Subgroup Ambient))
    (hcore : pCoreOf 2 (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient)) ≠ ⊥) :
    WeakCoreLocal prime Ambient := by
  obtain ⟨Local, hlocal, hle⟩ := nontrivial_core_local_container
    (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient)) hcore
  exact weak_core_one_sylow_local hprime Parent hrank Local hlocal hle

theorem simple_subgroup_nontrivial_core_proper {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (SubgroupOfAmbient : Subgroup Ambient) (hcore : pCoreOf 2 SubgroupOfAmbient ≠ ⊥) :
    SubgroupOfAmbient ≠ ⊤ := by
  intro htop
  have hnormal : (pCoreOf 2 SubgroupOfAmbient).Normal := by
    have hle := subgroup_le_normalizer_own_core 2 SubgroupOfAmbient
    rw [htop] at hle
    have hnormalTop : (pCoreOf 2 (⊤ : Subgroup Ambient)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_unique hle)
    simpa only [htop] using hnormalTop
  let := hnormal
  rcases CFSG.eq_bot_or_eq_top_of_normal (pCoreOf 2 SubgroupOfAmbient) hnormal with hbottom | hwhole
  · exact hcore hbottom
  · have hpgroup : IsPGroup 2 Ambient := by
      have hsubgroup := pCoreOf_isPGroup 2 SubgroupOfAmbient
      rw [hwhole] at hsubgroup
      exact hsubgroup.of_equiv Subgroup.topEquiv
    exact not_isPGroup_of_nonabelian_simple Ambient Nat.prime_two hnonab hpgroup

end CFSG.LargeEvenClassification.Helpers
