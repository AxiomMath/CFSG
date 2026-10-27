module

public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocality
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeHyperplaneGeneration
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreTwoSubgroups
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocalIntersections

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem sylow_contains_conjugate_inside {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (Parent : Sylow prime Ambient) (Local Candidate : Subgroup Ambient)
    (hparentLe : (Parent : Subgroup Ambient) ≤ Local) (hcandidateLe : Candidate ≤ Local)
    (hpgroup : IsPGroup prime Candidate) :
    ∃ conjugator : Local, Candidate.map (MulAut.conj conjugator.val).toMonoidHom ≤
      (Parent : Subgroup Ambient) := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hinternalPGroup : IsPGroup prime (Candidate.subgroupOf Local) :=
    hpgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hcandidateLe).symm
  obtain ⟨OtherParent, hotherLe⟩ := hinternalPGroup.exists_le_sylow
  let InternalParent := Parent.subtype hparentLe
  obtain ⟨conjugator, hconjugate⟩ := MulAction.exists_smul_eq Local OtherParent InternalParent
  have hparent : (OtherParent : Subgroup Local).map (MulAut.conj conjugator).toMonoidHom =
      (InternalParent : Subgroup Local) := by
    rw [← hconjugate]
    have hcoe := Sylow.pointwise_smul_def (g := MulAut.conj conjugator) (P := OtherParent)
    rw [Subgroup.pointwise_smul_def] at hcoe
    rw [Sylow.smul_def]
    exact hcoe.symm
  have hle := Subgroup.map_mono (f := Local.subtype)
    (hparent ▸ Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) hotherLe)
  have hcomposition : Local.subtype.comp (MulAut.conj conjugator).toMonoidHom =
      (MulAut.conj conjugator.val).toMonoidHom.comp Local.subtype := by
    ext element
    rfl
  rw [Subgroup.map_map, hcomposition, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hcandidateLe, Sylow.coe_subtype,
    Subgroup.map_subgroupOf_eq_of_le hparentLe] at hle
  exact ⟨conjugator, hle⟩

theorem weak_core_absorbs_pSubgroup_normalizer {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Parent : Sylow prime Ambient)
    (hparentRank : 3 ≤ pRank prime (Parent : Subgroup Ambient)) (Candidate : Subgroup Ambient)
    (hcandidateLe : Candidate ≤ weakTwoGeneratedPCore prime (Parent : Subgroup Ambient))
    (hpgroup : IsPGroup prime Candidate) (hcandidateRank : 2 ≤ pRank prime Candidate)
    (hcentralizerRank : 3 ≤ pRank prime
      (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) ⊓ Subgroup.centralizer (Candidate : Set Ambient))) :
    Subgroup.normalizer (Candidate : Set Ambient) ≤ weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) := by
  let WeakCore := weakTwoGeneratedPCore prime (Parent : Subgroup Ambient)
  have hparentLe : (Parent : Subgroup Ambient) ≤ WeakCore :=
    parent_le_weak_core hprime.one_lt (Parent : Subgroup Ambient) hparentRank
  obtain ⟨Elementary, helementaryLe, helementary, hcard⟩ := pRank_witness hprime.one_lt
    (WeakCore ⊓ Subgroup.centralizer (Candidate : Set Ambient))
  have hpElementary : IsPGroup prime Elementary := IsPGroup.of_card hcard
  have helementaryNormalizes : Elementary ≤ Subgroup.normalizer (Candidate : Set Ambient) :=
    (helementaryLe.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hsupPGroup : IsPGroup prime (Candidate ⊔ Elementary : Subgroup Ambient) :=
    hpgroup.to_sup_of_normal_left' hpElementary helementaryNormalizes
  have hsupLe : Candidate ⊔ Elementary ≤ WeakCore :=
    sup_le hcandidateLe (helementaryLe.trans inf_le_left)
  obtain ⟨conjugator, hconjugateLe⟩ := sylow_contains_conjugate_inside hprime Parent WeakCore
    (Candidate ⊔ Elementary) hparentLe hsupLe hsupPGroup
  let coordinates := MulAut.conj conjugator.val
  have hcandidateParent : Candidate.map coordinates.toMonoidHom ≤ (Parent : Subgroup Ambient) :=
    (Subgroup.map_mono (f := coordinates.toMonoidHom) (show Candidate ≤ Candidate ⊔ Elementary from le_sup_left)).trans
      hconjugateLe
  have helementaryParent : Elementary.map coordinates.toMonoidHom ≤ (Parent : Subgroup Ambient) :=
    (Subgroup.map_mono (f := coordinates.toMonoidHom) (show Elementary ≤ Candidate ⊔ Elementary from le_sup_right)).trans
      hconjugateLe
  have helementaryCentralizer : Elementary.map coordinates.toMonoidHom ≤
      Subgroup.centralizer (Candidate.map coordinates.toMonoidHom : Set Ambient) := by
    rw [← centralizer_map_mulEquiv coordinates Candidate]
    exact Subgroup.map_mono (helementaryLe.trans inf_le_right)
  have helementaryRank : 3 ≤ pRank prime (Elementary.map coordinates.toMonoidHom) := by
    rw [pRank_map_mulEquiv hprime.one_lt]
    have hrank := elementary_pRank_card hprime.one_lt Elementary helementary hcard
    exact hrank ▸ hcentralizerRank
  have hconjugateEligible : weakPCoreEligible prime (Parent : Subgroup Ambient)
      (Candidate.map coordinates.toMonoidHom) := by
    refine ⟨hcandidateParent, ?_, ?_⟩
    · rw [pRank_map_mulEquiv hprime.one_lt]
      exact hcandidateRank
    · exact helementaryRank.trans (pRank_mono hprime.one_lt
        ((le_inf helementaryParent helementaryCentralizer).trans le_sup_right))
  have hnormalizerLe := eligible_normalizer_le_weak_core (Parent : Subgroup Ambient)
    (Candidate.map coordinates.toMonoidHom) hconjugateEligible
  have hweakInvariant : WeakCore.map coordinates.toMonoidHom = WeakCore :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer conjugator.property)
  have hnormalizerMap : (Subgroup.normalizer (Candidate : Set Ambient)).map coordinates.toMonoidHom ≤
      WeakCore.map coordinates.toMonoidHom := by
    rw [hweakInvariant, Subgroup.map_equiv_normalizer_eq]
    exact hnormalizerLe
  exact (Subgroup.map_le_map_iff_of_injective coordinates.injective).mp hnormalizerMap

theorem rank_three_normalized_coprime_le_weak_core {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime rank : ℕ} (hprime : prime.Prime) (Parent : Sylow prime Ambient)
    (hparentRank : 3 ≤ pRank prime (Parent : Subgroup Ambient)) (Elementary CoprimeSubgroup : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank)
    (hrank : 3 ≤ rank) (helementaryLe : Elementary ≤ weakTwoGeneratedPCore prime (Parent : Subgroup Ambient))
    (hcoprime : ¬prime ∣ Nat.card CoprimeSubgroup)
    (hnormalizes : Elementary ≤ Subgroup.normalizer (CoprimeSubgroup : Set Ambient)) :
    CoprimeSubgroup ≤ weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) := by
  let : CommGroup Elementary := { (inferInstance : Group Elementary) with
    mul_comm := @mul_comm' Elementary _ helementary.1 }
  have hstable : ∀ conjugator : Elementary, ∀ element : Ambient, element ∈ CoprimeSubgroup →
      conjugator.val * element * conjugator.val⁻¹ ∈ CoprimeSubgroup := by
    intro conjugator element helement
    exact (Subgroup.mem_normalizer_iff.mp (hnormalizes conjugator.property) element).mp helement
  let action := invariantSubgroupConjugation Elementary.subtype CoprimeSubgroup hstable
  have hexponent : ∀ element : Elementary, element ^ prime = 1 := by
    intro element
    apply Subtype.ext
    exact helementary.2 element element.property
  have hgenerates := coprime_hyperplane_fixed_generation hprime (IsPGroup.of_card hcard)
    hexponent action hcoprime
  have helementaryRank : 3 ≤ pRank prime Elementary :=
    (elementary_pRank_card hprime.one_lt Elementary helementary hcard) ▸ hrank
  have hspanLe : hyperplaneFixedSpan prime action ≤
      (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient)).comap CoprimeSubgroup.subtype := by
    apply iSup_le
    intro Fixers
    let MappedFixers := Fixers.val.map Elementary.subtype
    have hmappedLe : MappedFixers ≤ Elementary := by
      intro element helement
      obtain ⟨source, _, rfl⟩ := helement
      exact source.property
    have hmappedRank : 2 ≤ pRank prime MappedFixers := by
      have hbound := elementary_hyperplane_rank_lower hprime Elementary helementary hcard
        Fixers.val Fixers.property
      change rank ≤ pRank prime MappedFixers + 1 at hbound
      omega
    have helementaryCentralizer : Elementary ≤ Subgroup.centralizer (MappedFixers : Set Ambient) := by
      intro element helement
      apply Subgroup.mem_centralizer_iff.mpr
      intro other hother
      exact congrArg (fun entry : Elementary => entry.val)
        (@mul_comm' Elementary _ helementary.1 ⟨other, hmappedLe hother⟩ ⟨element, helement⟩)
    have hcentralizerRank : 3 ≤ pRank prime (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) ⊓
        Subgroup.centralizer (MappedFixers : Set Ambient)) :=
      helementaryRank.trans (pRank_mono hprime.one_lt (le_inf helementaryLe helementaryCentralizer))
    have hnormalizerLe := weak_core_absorbs_pSubgroup_normalizer hprime Parent hparentRank MappedFixers
      (hmappedLe.trans helementaryLe) (((IsPGroup.of_card hcard).to_subgroup Fixers.val).map Elementary.subtype)
      hmappedRank hcentralizerRank
    intro element helement
    apply hnormalizerLe
    apply Subgroup.centralizer_le_normalizer (MappedFixers : Set Ambient)
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    obtain ⟨fixer, hfixer, rfl⟩ := hother
    have hfixed := congrArg (fun entry : CoprimeSubgroup => entry.val) (helement ⟨fixer, hfixer⟩)
    change fixer.val * element.val * fixer.val⁻¹ = element.val at hfixed
    exact (mul_inv_eq_iff_eq_mul).mp hfixed
  intro element helement
  exact hspanLe (hgenerates.symm ▸ (show (⟨element, helement⟩ : CoprimeSubgroup) ∈
    (⊤ : Subgroup CoprimeSubgroup) from Subgroup.mem_top _))

theorem rank_three_two_local_intersection_characteristic {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime rank : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType Ambient) (Parent : Sylow prime Ambient)
    (hparentRank : 3 ≤ pRank prime (Parent : Subgroup Ambient)) (Elementary Local : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank)
    (hrank : 3 ≤ rank) (helementaryWeak : Elementary ≤ weakTwoGeneratedPCore prime (Parent : Subgroup Ambient))
    (helementaryLocal : Elementary ≤ Local) (hlocal : IsTwoLocal Local) :
    pCoreOf 2 Local ≤ pCoreOf 2 (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) ⊓ Local) ∧
      pCoreOf 2 (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) ⊓ Local) ≠ ⊥ ∧
      IsCharacteristicTwoLocal (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) ⊓ Local) := by
  have hcoprime : ¬prime ∣ Nat.card (pCoreOf 2 Local) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨exponent, hcoreCard⟩ := (pCoreOf_isPGroup 2 Local).exists_card_eq
    rw [hcoreCard]
    intro hdivides
    have htwoDivides := hprime.dvd_of_dvd_pow hdivides
    exact hodd ((Nat.dvd_prime Nat.prime_two).mp htwoDivides |>.resolve_left hprime.ne_one)
  have hcoreWeak := rank_three_normalized_coprime_le_weak_core hprime Parent hparentRank Elementary
    (pCoreOf 2 Local) helementary hcard hrank helementaryWeak hcoprime
    (helementaryLocal.trans (subgroup_le_normalizer_own_core 2 Local))
  let Intersection := weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) ⊓ Local
  have hcoreIntersection : pCoreOf 2 Local ≤ Intersection := le_inf hcoreWeak (pCoreOf_le 2 Local)
  have hcoreNormal : ((pCoreOf 2 Local).subgroupOf Intersection).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreIntersection).mpr
      (inf_le_right.trans (subgroup_le_normalizer_own_core 2 Local))
  have hcoreLe := normal_pSubgroup_le_pCoreOf (pCoreOf 2 Local) Intersection hcoreIntersection
    hcoreNormal (pCoreOf_isPGroup 2 Local)
  have hnontrivial : pCoreOf 2 Intersection ≠ ⊥ := by
    intro hzero
    exact twoLocal_core_ne_bot Local hlocal (le_antisymm (hzero ▸ hcoreLe) bot_le)
  refine ⟨hcoreLe, hnontrivial, ?_⟩
  intro element helement
  apply hcoreLe
  apply hchar Local hlocal
  refine ⟨helement.1.2, ?_⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro source hsource
  exact Subgroup.mem_centralizer_iff.mp helement.2 source (hcoreLe hsource)

end CFSG.LargeEvenClassification.Helpers
