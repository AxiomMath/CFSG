module

public import CFSG.GF2Type.Smith1979.IdxFourHBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G]

theorem exists_centralizer_lift (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hx1 : x ≠ 1)
    (hxz : x ≠ S.z) {s : S.O} (hs : s ∈ stab S (S.cl x)) :
    ∃ m : S.M, (m : G) * x = x * (m : G) ∧ S.ρ m = s := by
  obtain ⟨m0, hm0⟩ := hs.1
  have hfix : S.cl ((m0 : G) * x * (m0 : G)⁻¹) = S.cl x := by
    rw [← S.ρ_cl m0 hxQ, hm0]
    exact hs.2
  rcases (S.cl_eq_cl_iff hxQ (S.conj_mem_QG m0.2 hxQ)).mp hfix.symm with h | h
  · refine ⟨m0, ?_, hm0⟩
    calc (m0 : G) * x = (m0 : G) * x * (m0 : G)⁻¹ * (m0 : G) := by group
      _ = x * (m0 : G) := by rw [h]
  · obtain ⟨u, huQ, hu⟩ := S.exists_conj_eq_mul_z hxQ hx1 hxz
    have huM : u⁻¹ ∈ S.M := S.QG_le_M (S.QG.inv_mem huQ)
    refine ⟨⟨u⁻¹, huM⟩ * m0, ?_, ?_⟩
    · have hz : ∀ y : G, y ∈ S.M → y * S.z = S.z * y := fun y hy => S.z_comm hy
      have hzz : S.z * S.z = 1 := S.z_mul_z
      have h1 : u⁻¹ * (x * S.z) * u = x := by
        calc u⁻¹ * (x * S.z) * u = u⁻¹ * x * u * S.z := by
              rw [show u⁻¹ * (x * S.z) * u = u⁻¹ * x * (S.z * u) by group,
                ← hz u (S.QG_le_M huQ)]
              group
          _ = x := by
              have h2 : u⁻¹ * x * u = x * S.z := by
                calc u⁻¹ * x * u = u⁻¹ * (u * x * u⁻¹ * S.z) * u := by
                      rw [hu, mul_assoc x S.z S.z, hzz, mul_one]
                  _ = x * S.z := by
                      rw [show u⁻¹ * (u * x * u⁻¹ * S.z) * u = x * (u⁻¹ * S.z * u) by group,
                        show u⁻¹ * S.z * u = S.z by
                          rw [mul_assoc, ← hz u (S.QG_le_M huQ)]; group]
              rw [h2, mul_assoc, hzz, mul_one]
      show u⁻¹ * (m0 : G) * x = x * (u⁻¹ * (m0 : G))
      calc u⁻¹ * (m0 : G) * x = u⁻¹ * ((m0 : G) * x * (m0 : G)⁻¹) * u * (u⁻¹ * (m0 : G)) := by
            group
        _ = x * (u⁻¹ * (m0 : G)) := by rw [h, h1]
    · rw [map_mul, hm0, (S.ρ_eq_one_iff _).mpr (S.QG.inv_mem huQ), one_mul]

end CFSG.GF2Type.Smith1979.IdxFour
