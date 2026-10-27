module

public import CFSG.LocalAnalysis.LargeEvenClassification.NormalCoreIntersection

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem pCoreOf_map_injective {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target]
    (prime : ℕ) (Inside : Subgroup Ambient) (embedding : Ambient →* Target)
    (hinjective : Function.Injective embedding) :
    pCoreOf prime (Inside.map embedding) =
      (CFSG.Open.pCore prime Inside).map (embedding.comp Inside.subtype) := by
  let coordinates := Inside.equivMapOfInjective embedding hinjective
  have hcore := pCore_map_mulEquiv prime coordinates
  change (CFSG.Open.pCore prime (Inside.map embedding)).map
    (Inside.map embedding).subtype = _
  rw [← hcore, Subgroup.map_map]
  rfl

end CFSG.LargeEvenClassification.Helpers
