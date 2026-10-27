module

public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreInternal

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem twoLocalPRank_subgroup_le {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Local : Subgroup Ambient) :
    twoLocalPRank prime Local ≤ twoLocalPRank prime Ambient := by
  apply csSup_le'
  rintro rank ⟨InternalLocal, hinternalLocal, hrank⟩
  obtain ⟨TwoSubgroup, hnontrivial, hpgroup, hnormalizer⟩ := hinternalLocal
  let MappedTwo := TwoSubgroup.map Local.subtype
  have hmappedNe : MappedTwo ≠ ⊥ := fun hzero => hnontrivial
    ((Subgroup.map_eq_bot_iff_of_injective TwoSubgroup Local.subtype_injective).mp hzero)
  have hmappedPGroup : IsPGroup 2 MappedTwo := hpgroup.map Local.subtype
  have hlocal : IsTwoLocal (Subgroup.normalizer (MappedTwo : Set Ambient)) :=
    ⟨MappedTwo, hmappedNe, hmappedPGroup, rfl⟩
  have hle : InternalLocal.map Local.subtype ≤ Subgroup.normalizer (MappedTwo : Set Ambient) := by
    rw [hnormalizer]
    exact Subgroup.le_normalizer_map Local.subtype
  have hbound := (pRank_mono hprime hle).trans (pRank_le_twoLocalPRank hprime _ hlocal)
  rw [pRank_map_injective hprime Local.subtype Local.subtype_injective, hrank] at hbound
  exact hbound

end CFSG.LargeEvenClassification.Helpers
