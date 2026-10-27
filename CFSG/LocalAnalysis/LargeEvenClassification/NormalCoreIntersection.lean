module

public import CFSG.LocalAnalysis.LargeEvenClassification.LocalCore
public import CFSG.LocalAnalysis.LargeEvenClassification.SubgroupTransport

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem pCore_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] (prime : ℕ)
    (coordinates : Ambient ≃* Target) :
    (CFSG.Open.pCore prime Ambient).map coordinates.toMonoidHom =
      CFSG.Open.pCore prime Target := by
  have hforward : (CFSG.Open.pCore prime Ambient).map coordinates.toMonoidHom ≤
      CFSG.Open.pCore prime Target :=
    normal_pSubgroup_le_pCore _ ((pCore_normal Ambient prime).map coordinates.toMonoidHom coordinates.surjective)
      ((pCore_isPGroup Ambient prime).map coordinates.toMonoidHom)
  have hbackward : (CFSG.Open.pCore prime Target).map coordinates.symm.toMonoidHom ≤
      CFSG.Open.pCore prime Ambient :=
    normal_pSubgroup_le_pCore _ ((pCore_normal Target prime).map coordinates.symm.toMonoidHom coordinates.symm.surjective)
      ((pCore_isPGroup Target prime).map coordinates.symm.toMonoidHom)
  have hback := Subgroup.map_mono (f := coordinates.toMonoidHom) hbackward
  rw [subgroup_map_forward_inverse_mulEquiv coordinates] at hback
  exact le_antisymm hforward hback

end CFSG.LargeEvenClassification.Helpers
