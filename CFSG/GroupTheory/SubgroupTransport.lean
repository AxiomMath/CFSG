module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GroupTheory

theorem map_subgroupOf_equivMapOfInjective {G G' : Type*} [Group G] [Group G'] (e : G →* G')
    (he : Function.Injective e) (A K : Subgroup G) :
    (A.subgroupOf K).map (K.equivMapOfInjective e he).toMonoidHom =
      (A.map e).subgroupOf (K.map e) := by
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    Subtype.ext_iff, Subgroup.coe_equivMapOfInjective_apply]
  constructor
  · rintro ⟨k, hk, hkx⟩
    exact ⟨k, hk, hkx⟩
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨k, hkK, hk⟩ := hx
    have hhk : h = k := he (by simpa using hk.symm)
    subst hhk
    exact ⟨⟨h, hkK⟩, hh, rfl⟩

theorem map_map_mk'_congr {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    {N : Subgroup Q} {N' : Subgroup Q'} [N.Normal] [N'.Normal] (hN : N.map e.toMonoidHom = N')
    (B : Subgroup Q) :
    (B.map (QuotientGroup.mk' N)).map (QuotientGroup.congr N N' e hN).toMonoidHom =
      (B.map e.toMonoidHom).map (QuotientGroup.mk' N') := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_comap_mk'_congr {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    {N : Subgroup Q} {N' : Subgroup Q'} [N.Normal] [N'.Normal] (hN : N.map e.toMonoidHom = N')
    {R : Subgroup (Q ⧸ N)} {R' : Subgroup (Q' ⧸ N')}
    (hR : R.map (QuotientGroup.congr N N' e hN).toMonoidHom = R') :
    (R.comap (QuotientGroup.mk' N)).map e.toMonoidHom = R'.comap (QuotientGroup.mk' N') := by
  ext x'
  rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_comap, ← hR,
    Subgroup.mem_map_equiv]
  rfl

theorem isSylowOf_map_mulEquiv {p : ℕ} [Fact p.Prime] {Q Q' : Type*} [Group Q] [Group Q']
    [Finite Q] [Finite Q'] (e : Q ≃* Q') {P K : Subgroup Q} :
    CFSG.ABGLocalTools.IsSylowOf p (P.map e.toMonoidHom) (K.map e.toMonoidHom) ↔
      CFSG.ABGLocalTools.IsSylowOf p P K := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff, CFSG.ABGLocalTools.isSylowOf_iff,
    Subgroup.map_le_map_iff_of_injective e.injective,
    Subgroup.relIndex_map_map_of_injective _ _ e.injective]
  exact and_congr Iff.rfl (and_congr
    ⟨fun h => h.of_equiv (e.subgroupMap P).symm, fun h => h.of_equiv (e.subgroupMap P)⟩
    Iff.rfl)

end CFSG.GroupTheory
