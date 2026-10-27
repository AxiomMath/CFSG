module

public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreTwoSubgroups

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem elementary_comap_injective {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (homomorphism : Ambient →* Target)
    (hinjective : Function.Injective homomorphism) (Elementary : Subgroup Target)
    (helementary : IsElemAbelian prime Elementary) :
    IsElemAbelian prime (Elementary.comap homomorphism) := by
  constructor
  · apply isMulCommutative_iff.mpr
    intro first second
    apply Subtype.ext
    apply hinjective
    change homomorphism (first.val * second.val) = homomorphism (second.val * first.val)
    rw [map_mul, map_mul]
    exact congrArg (fun entry : Elementary => entry.val)
      (@mul_comm' Elementary _ helementary.1 ⟨homomorphism first, first.property⟩
        ⟨homomorphism second, second.property⟩)
  · intro element helement
    apply hinjective
    rw [map_pow, map_one]
    exact helementary.2 (homomorphism element) helement

theorem pRank_map_injective {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] {prime : ℕ}
    (hprime : 1 < prime) (homomorphism : Ambient →* Target) (hinjective : Function.Injective homomorphism)
    (Source : Subgroup Ambient) : pRank prime (Source.map homomorphism) = pRank prime Source := by
  have hlower : pRank prime Source ≤ pRank prime (Source.map homomorphism) := by
    obtain ⟨Elementary, helementaryLe, helementary, hcard⟩ := pRank_witness hprime Source
    apply le_csSup
    · refine ⟨Nat.card Target, ?_⟩
      rintro rank ⟨Other, _, _, hotherCard⟩
      exact rank_exponent_le_card hprime Other hotherCard
    · exact ⟨Elementary.map homomorphism, Subgroup.map_mono helementaryLe,
        elementary_map Elementary helementary homomorphism,
        (Nat.card_congr (Elementary.equivMapOfInjective homomorphism hinjective).toEquiv).symm.trans hcard⟩
  obtain ⟨Elementary, helementaryLe, helementary, hcard⟩ := pRank_witness hprime (Source.map homomorphism)
  have helementaryRange : Elementary ≤ homomorphism.range :=
    helementaryLe.trans (Subgroup.map_le_range homomorphism Source)
  have hmapComap : (Elementary.comap homomorphism).map homomorphism = Elementary :=
    Subgroup.map_comap_eq_self helementaryRange
  have hcomapLe : Elementary.comap homomorphism ≤ Source := by
    have hle := Subgroup.comap_mono (f := homomorphism) helementaryLe
    rw [Subgroup.comap_map_eq_self_of_injective hinjective] at hle
    exact hle
  have hcomapCard : Nat.card (Elementary.comap homomorphism) =
      prime ^ pRank prime (Source.map homomorphism) := by
    have hcardMap := Nat.card_congr ((Elementary.comap homomorphism).equivMapOfInjective
      homomorphism hinjective).toEquiv
    rw [hmapComap] at hcardMap
    exact hcardMap.trans hcard
  have hupper : pRank prime (Source.map homomorphism) ≤ pRank prime Source := by
    apply le_csSup
    · refine ⟨Nat.card Ambient, ?_⟩
      rintro rank ⟨Other, _, _, hotherCard⟩
      exact rank_exponent_le_card hprime Other hotherCard
    · exact ⟨Elementary.comap homomorphism, hcomapLe,
        elementary_comap_injective homomorphism hinjective Elementary helementary, hcomapCard⟩
  exact le_antisymm hupper hlower

theorem pRank_subgroupOf {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Source Local : Subgroup Ambient) (hle : Source ≤ Local) :
    pRank prime (Source.subgroupOf Local) = pRank prime Source := by
  have hmap := pRank_map_injective hprime Local.subtype Local.subtype_injective (Source.subgroupOf Local)
  rw [Subgroup.map_subgroupOf_eq_of_le hle] at hmap
  exact hmap.symm

theorem normalizer_subgroupOf_map {Ambient : Type groupUniverse} [Group Ambient]
    (Candidate Local : Subgroup Ambient) (hcandidateLe : Candidate ≤ Local)
    (hnormalizerLe : Subgroup.normalizer (Candidate : Set Ambient) ≤ Local) :
    (Subgroup.normalizer (Candidate.subgroupOf Local : Set Local)).map Local.subtype =
      Subgroup.normalizer (Candidate : Set Ambient) := by
  apply le_antisymm
  · intro element helement
    obtain ⟨source, hsource, rfl⟩ := helement
    apply Subgroup.mem_normalizer_iff.mpr
    intro other
    constructor
    · intro hother
      exact (Subgroup.mem_normalizer_iff.mp hsource ⟨other, hcandidateLe hother⟩).mp hother
    · intro hconjugate
      have hconjugateLocal : source.val * other * source.val⁻¹ ∈ Local := hcandidateLe hconjugate
      have hotherLocal : other ∈ Local := by
        have hback := Local.mul_mem (Local.mul_mem (Local.inv_mem source.property) hconjugateLocal)
          source.property
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hback
      exact (Subgroup.mem_normalizer_iff.mp hsource ⟨other, hotherLocal⟩).mpr hconjugate
  · intro element helement
    refine ⟨⟨element, hnormalizerLe helement⟩, ?_, rfl⟩
    apply Subgroup.mem_normalizer_iff.mpr
    intro other
    exact Subgroup.mem_normalizer_iff.mp helement other.val

theorem weakPCoreEligible_internal {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Parent Candidate Local : Subgroup Ambient)
    (hparentLe : Parent ≤ Local) (hcandidateLe : Candidate ≤ Parent) :
    weakPCoreEligible prime (Parent.subgroupOf Local) (Candidate.subgroupOf Local) ↔
      weakPCoreEligible prime Parent Candidate := by
  have hcandidateLocal : Candidate ≤ Local := hcandidateLe.trans hparentLe
  have hjoinLe : Candidate ⊔ (Parent ⊓ Subgroup.centralizer (Candidate : Set Ambient)) ≤ Local :=
    sup_le hcandidateLocal (inf_le_left.trans hparentLe)
  have hcentralizer : Parent.subgroupOf Local ⊓
      Subgroup.centralizer (Candidate.subgroupOf Local : Set Local) =
        (Parent ⊓ Subgroup.centralizer (Candidate : Set Ambient)).subgroupOf Local := by
    ext element
    constructor
    · intro helement
      refine ⟨helement.1, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro other hother
      exact congrArg (fun entry : Local => entry.val)
        (Subgroup.mem_centralizer_iff.mp helement.2 ⟨other, hcandidateLocal hother⟩ hother)
    · intro helement
      refine ⟨helement.1, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro other hother
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp helement.2 other.val hother
  have hjoin : Candidate.subgroupOf Local ⊔ (Parent.subgroupOf Local ⊓
      Subgroup.centralizer (Candidate.subgroupOf Local : Set Local)) =
        (Candidate ⊔ (Parent ⊓ Subgroup.centralizer (Candidate : Set Ambient))).subgroupOf Local := by
    rw [hcentralizer]
    exact Subgroup.comap_sup_eq_of_le_range Local.subtype
      (by simpa only [Subgroup.subtype_range] using hcandidateLocal)
      (by simpa only [Subgroup.subtype_range] using (inf_le_left.trans hparentLe))
  unfold weakPCoreEligible
  rw [hjoin, pRank_subgroupOf hprime _ Local hjoinLe,
    pRank_subgroupOf hprime Candidate Local hcandidateLocal]
  constructor
  · intro heligible
    exact ⟨hcandidateLe, heligible.2⟩
  · intro heligible
    exact ⟨Subgroup.comap_mono hcandidateLe, heligible.2⟩

theorem weak_core_internal_map_eq {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Parent : Subgroup Ambient)
    (hparentLe : Parent ≤ weakTwoGeneratedPCore prime Parent) :
    let WeakCore := weakTwoGeneratedPCore prime Parent
    (weakTwoGeneratedPCore prime (Parent.subgroupOf WeakCore)).map WeakCore.subtype = WeakCore := by
  let WeakCore := weakTwoGeneratedPCore prime Parent
  apply le_antisymm
  · change (⨆ Candidate : {Candidate : Subgroup WeakCore //
        weakPCoreEligible prime (Parent.subgroupOf WeakCore) Candidate},
      Subgroup.normalizer (Candidate.val : Set WeakCore)).map WeakCore.subtype ≤ WeakCore
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro Candidate
    let MappedCandidate := Candidate.val.map WeakCore.subtype
    have hmappedLe : MappedCandidate ≤ Parent := by
      have hle := Subgroup.map_mono (f := WeakCore.subtype) Candidate.property.1
      rw [Subgroup.map_subgroupOf_eq_of_le hparentLe] at hle
      exact hle
    have hcomap : MappedCandidate.subgroupOf WeakCore = Candidate.val :=
      Subgroup.comap_map_eq_self_of_injective WeakCore.subtype_injective Candidate.val
    have hmappedEligible : weakPCoreEligible prime Parent MappedCandidate := by
      apply (weakPCoreEligible_internal hprime Parent MappedCandidate WeakCore hparentLe hmappedLe).mp
      rw [hcomap]
      exact Candidate.property
    have hnormalizerLe : Subgroup.normalizer (MappedCandidate : Set Ambient) ≤ WeakCore :=
      eligible_normalizer_le_weak_core Parent MappedCandidate hmappedEligible
    rw [← hcomap, normalizer_subgroupOf_map MappedCandidate WeakCore
      (hmappedLe.trans hparentLe) hnormalizerLe]
    exact hnormalizerLe
  · change (⨆ Candidate : {Candidate : Subgroup Ambient // weakPCoreEligible prime Parent Candidate},
      Subgroup.normalizer (Candidate.val : Set Ambient)) ≤
        (weakTwoGeneratedPCore prime (Parent.subgroupOf WeakCore)).map WeakCore.subtype
    apply iSup_le
    intro Candidate
    have hcandLe := Candidate.property.1
    have hnormalizerLe : Subgroup.normalizer (Candidate.val : Set Ambient) ≤ WeakCore :=
      eligible_normalizer_le_weak_core Parent Candidate.val Candidate.property
    have heligible : weakPCoreEligible prime (Parent.subgroupOf WeakCore)
        (Candidate.val.subgroupOf WeakCore) :=
      (weakPCoreEligible_internal hprime Parent Candidate.val WeakCore hparentLe hcandLe).mpr
        Candidate.property
    have hle := Subgroup.map_mono (f := WeakCore.subtype)
      (eligible_normalizer_le_weak_core (Parent.subgroupOf WeakCore)
        (Candidate.val.subgroupOf WeakCore) heligible)
    rw [normalizer_subgroupOf_map Candidate.val WeakCore (hcandLe.trans hparentLe) hnormalizerLe] at hle
    exact hle

theorem weak_core_internal_eq_top {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Parent : Subgroup Ambient)
    (hparentLe : Parent ≤ weakTwoGeneratedPCore prime Parent) :
    weakTwoGeneratedPCore prime (Parent.subgroupOf (weakTwoGeneratedPCore prime Parent)) = ⊤ := by
  apply Subgroup.map_injective (weakTwoGeneratedPCore prime Parent).subtype_injective
  rw [weak_core_internal_map_eq hprime Parent hparentLe]
  apply le_antisymm
  · intro element helement
    exact ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩
  · intro element helement
    obtain ⟨source, _, rfl⟩ := helement
    exact source.property

theorem pRank_sylow_eq_ambient {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (Parent : Sylow prime Ambient) :
    pRank prime (Parent : Subgroup Ambient) = pRank prime (⊤ : Subgroup Ambient) := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨Elementary, _, helementary, hcard⟩ := pRank_witness hprime.one_lt (⊤ : Subgroup Ambient)
  obtain ⟨OtherParent, helementaryParent⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  obtain ⟨conjugator, hconjugate⟩ := MulAction.exists_smul_eq Ambient OtherParent Parent
  let coordinates := MulAut.conj conjugator
  have hparent : (OtherParent : Subgroup Ambient).map coordinates.toMonoidHom =
      (Parent : Subgroup Ambient) := by
    rw [← hconjugate]
    have hcoe := Sylow.pointwise_smul_def (g := MulAut.conj conjugator) (P := OtherParent)
    rw [Subgroup.pointwise_smul_def] at hcoe
    rw [Sylow.smul_def]
    exact hcoe.symm
  have hle : Elementary.map coordinates.toMonoidHom ≤ (Parent : Subgroup Ambient) :=
    hparent ▸ Subgroup.map_mono helementaryParent
  have hcardMapped : Nat.card (Elementary.map coordinates.toMonoidHom) =
      prime ^ pRank prime (⊤ : Subgroup Ambient) :=
    (Nat.card_congr (Elementary.equivMapOfInjective coordinates.toMonoidHom
      coordinates.injective).toEquiv).symm.trans hcard
  have hrank := elementary_pRank_card hprime.one_lt (Elementary.map coordinates.toMonoidHom)
    (elementary_map Elementary helementary coordinates.toMonoidHom) hcardMapped
  exact le_antisymm (pRank_mono hprime.one_lt le_top)
    (hrank ▸ pRank_mono hprime.one_lt hle)

theorem weak_core_rank_eq_ambient {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (Parent : Sylow prime Ambient)
    (hrank : 3 ≤ pRank prime (Parent : Subgroup Ambient)) :
    pRank prime (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient)) =
      pRank prime (⊤ : Subgroup Ambient) := by
  have hparentLe := parent_le_weak_core hprime.one_lt (Parent : Subgroup Ambient) hrank
  exact le_antisymm (pRank_mono hprime.one_lt le_top)
    ((pRank_sylow_eq_ambient hprime Parent).symm ▸ pRank_mono hprime.one_lt hparentLe)

theorem weak_core_internal_locality_iff {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (Parent : Sylow prime Ambient)
    (hrank : 3 ≤ pRank prime (Parent : Subgroup Ambient)) :
    WeakCoreLocal prime (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient)) ↔
      pCoreOf 2 (weakTwoGeneratedPCore prime (Parent : Subgroup Ambient)) ≠ ⊥ := by
  let WeakCore := weakTwoGeneratedPCore prime (Parent : Subgroup Ambient)
  have hparentLe : (Parent : Subgroup Ambient) ≤ WeakCore :=
    parent_le_weak_core hprime.one_lt (Parent : Subgroup Ambient) hrank
  let InternalParent := Parent.subtype hparentLe
  have hinternalTop : weakTwoGeneratedPCore prime (InternalParent : Subgroup WeakCore) = ⊤ := by
    rw [Sylow.coe_subtype]
    exact weak_core_internal_eq_top hprime.one_lt (Parent : Subgroup Ambient) hparentLe
  have hinternalRank : 3 ≤ pRank prime (⊤ : Subgroup WeakCore) := by
    have hparentRank := pRank_subgroupOf hprime.one_lt (Parent : Subgroup Ambient) WeakCore hparentLe
    exact (hparentRank ▸ hrank).trans (pRank_mono hprime.one_lt le_top)
  constructor
  · intro hlocality
    obtain ⟨Local, hlocal, hcoreLe⟩ := hlocality.2 InternalParent
    have hlocalTop : Local = ⊤ := top_unique (hinternalTop ▸ hcoreLe)
    obtain ⟨TwoSubgroup, hnontrivial, hpgroup, hnormalizer⟩ := hlocal
    have hnormal : TwoSubgroup.Normal := Subgroup.normalizer_eq_top_iff.mp
      (hnormalizer.symm.trans hlocalTop)
    have htwoLe := normal_pSubgroup_le_pCore TwoSubgroup hnormal hpgroup
    have hcoreNe : CFSG.Open.pCore 2 WeakCore ≠ ⊥ := by
      intro hzero
      exact hnontrivial (le_antisymm (hzero ▸ htwoLe) bot_le)
    exact fun hzero => hcoreNe ((Subgroup.map_eq_bot_iff_of_injective
      (CFSG.Open.pCore 2 WeakCore) WeakCore.subtype_injective).mp hzero)
  · intro hcoreNe
    have hinternalCoreNe : CFSG.Open.pCore 2 WeakCore ≠ ⊥ := by
      intro hzero
      apply hcoreNe
      change (CFSG.Open.pCore 2 WeakCore).map WeakCore.subtype = ⊥
      rw [hzero]
      exact Subgroup.map_bot _
    let : (CFSG.Open.pCore 2 WeakCore).Normal := pCore_normal WeakCore 2
    have htopLocal : IsTwoLocal (⊤ : Subgroup WeakCore) :=
      ⟨CFSG.Open.pCore 2 WeakCore, hinternalCoreNe, pCore_isPGroup WeakCore 2,
        (Subgroup.normalizer_eq_top _).symm⟩
    exact ⟨hinternalRank, fun _ => ⟨⊤, htopLocal, le_top⟩⟩

end CFSG.LargeEvenClassification.Helpers
