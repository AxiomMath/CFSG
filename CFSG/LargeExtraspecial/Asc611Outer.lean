module

public import CFSG.LargeExtraspecial.Asc611OutG
public import CFSG.LargeExtraspecial.Asc611Model

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary

namespace S14

theorem unitaryOuterCentStmt : UnitaryOuterCentStmt := by
  intro m hm β hββ hβ1 U hU hfix hnorm hDG
  have hm4 : 4 ≤ m := by omega
  obtain ⟨A, φ, hreal⟩ := AS35K.exists_realize hm4 β
  have hφ := Asc611.eq_frob_of_fieldFactor_ne_one hm4 hβ1 hreal
  have hS := Asc611.semiInv_of_realize hm4 hββ hreal hφ
  have hnorm' : ∀ v : Fin m → CFSG.Blueprint.Fischer.K,
      AS35K.semi (A : GL (Fin m) CFSG.Blueprint.Fischer.K) φ v = v → v ≠ 0 →
      herm frob v v = 0 → ∀ u ∈ U, tq v * u * (tq v)⁻¹ ∈ U := fun v hvS _ hv u hu =>
    hnorm (tq v) (by rw [Asc611.realize_tq hreal hv, hvS]) u hu
  refine eq_bot_iff.mpr fun u hu => ?_
  obtain ⟨g, rfl, hgS⟩ := Asc611.exists_lift_comm hm4 hreal hφ (hfix u hu)
  rw [mem_bot]
  exact Asc611.eq_one_of_lift hS hU hnorm' hDG (by omega) hu hgS

end S14

end CFSG.LargeExtraspecial
