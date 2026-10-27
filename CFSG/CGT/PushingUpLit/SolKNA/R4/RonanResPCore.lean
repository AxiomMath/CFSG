module

public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.ClassicalInvolution.Q3

theorem exists_normal_two_of_normal {G : Type} [Group G] (N : Subgroup G)
    (hN : ∀ g : G, CFSG.ClassicalInvolution.Generic.conjSub g N = N) {x : G} (hx : x ∈ N)
    (hin : TightInO2 (⟨x, hx⟩ : ↥N)) :
    ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 ↥Q ∧ x ∈ Q := by
  have hconj : ∀ g y : G, y ∈ N → g * y * g⁻¹ ∈ N := fun g y hy => by
    have h := CFSG.ClassicalInvolution.Generic.conj_mem_conjSub (n := g) hy
    rwa [hN g] at h
  refine ⟨(CFSG.pCore 2 ↥N).map N.subtype, ?_, ?_, ?_⟩
  · refine ⟨fun q hq g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    let c : ↥N ≃* ↥N :=
      { toFun := fun z => ⟨g * (z : G) * g⁻¹, hconj g (z : G) z.2⟩
        invFun := fun z => ⟨g⁻¹ * (z : G) * g, by
          have h := hconj g⁻¹ (z : G) z.2
          rwa [inv_inv] at h⟩
        left_inv := fun z => Subtype.ext (by simp [mul_assoc])
        right_inv := fun z => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hmap : (CFSG.pCore 2 ↥N).map c.toMonoidHom = CFSG.pCore 2 ↥N :=
      CFSG.pCore_map_iso 2 c
    have hc : c y ∈ CFSG.pCore 2 ↥N := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem c.toMonoidHom hy
    exact Subgroup.mem_map.mpr ⟨c y, hc, rfl⟩
  · exact IsPGroup.map CFSG.pCore_isPGroup N.subtype
  · obtain ⟨P, hPn, hPp, hxP⟩ := hin
    have hPmem : P ∈ {K : Subgroup ↥N | K.Normal ∧ IsPGroup 2 ↥K} := ⟨hPn, hPp⟩
    have hle : P ≤ CFSG.pCore 2 ↥N := le_sSup hPmem
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hle hxP, rfl⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
