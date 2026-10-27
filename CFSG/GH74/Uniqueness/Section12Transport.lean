module

public import CFSG.GH74.Uniqueness.Section12Stmts

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

section Transport

variable {G : Type*} [Group G]

theorem conjugate_subgroupOf_mk (A L : Subgroup G) {t : G} (ht : t ∈ L) :
    conjugate (A.subgroupOf L) ⟨t, ht⟩ = (conjugate A t).subgroupOf L := by
  ext y
  simp only [Bender.mem_conjugate_iff_mul_inv, mem_subgroupOf, coe_mul, coe_inv]

theorem inf_conjugate_subgroupOf (A L : Subgroup G) {t : G} (ht : t ∈ L) :
    (A ⊓ conjugate A t).subgroupOf L =
      A.subgroupOf L ⊓ conjugate (A.subgroupOf L) ⟨t, ht⟩ := by
  rw [conjugate_subgroupOf_mk A L ht]
  ext y
  simp only [mem_subgroupOf, mem_inf]

theorem cartan_eq_subgroupOf {A L : Subgroup G} {P : Subgroup L}
    (hB : (A ⊓ L).subgroupOf L = normalizer (P : Set L)) {t : G} (ht : t ∈ L) :
    Bender.cartan P ⟨t, ht⟩ = (A ⊓ conjugate A t).subgroupOf L := by
  rw [inf_subgroupOf_right] at hB
  rw [inf_conjugate_subgroupOf A L ht, hB]
  rfl

theorem map_subtype_cartan {A L : Subgroup G} {P : Subgroup L}
    (hB : (A ⊓ L).subgroupOf L = normalizer (P : Set L)) {t : G} (ht : t ∈ L) :
    (Bender.cartan P ⟨t, ht⟩).map L.subtype = A ⊓ conjugate A t ⊓ L := by
  rw [cartan_eq_subgroupOf hB ht, subgroupOf_map_subtype]

theorem map_subtype_borel {A L : Subgroup G} {P : Subgroup L}
    (hB : (A ⊓ L).subgroupOf L = normalizer (P : Set L)) :
    (Bender.borel P).map L.subtype = A ⊓ L := by
  change (normalizer (P : Set L)).map L.subtype = A ⊓ L
  rw [← hB, subgroupOf_map_subtype, inf_assoc, inf_idem]

theorem map_subtype_commutator_cartan {A L : Subgroup G} {P : Subgroup L}
    (hB : (A ⊓ L).subgroupOf L = normalizer (P : Set L)) {t : G} (ht : t ∈ L) :
    (⁅Bender.cartan P ⟨t, ht⟩, zpowers (⟨t, ht⟩ : L)⁆).map L.subtype =
      ⁅A ⊓ conjugate A t ⊓ L, zpowers t⁆ := by
  rw [map_commutator, map_subtype_cartan hB ht, MonoidHom.map_zpowers]
  rfl

theorem map_subtype_centralizer (L : Subgroup G) (H : Subgroup L) :
    (centralizer (H : Set L)).map L.subtype =
      centralizer ((H.map L.subtype : Subgroup G) : Set G) ⊓ L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨mem_centralizer_iff.mpr ?_, y.2⟩
    rintro _ ⟨h, hh, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hy h hh)
  · rintro ⟨hx, hxL⟩
    refine ⟨⟨x, hxL⟩, mem_centralizer_iff.mpr fun h hh => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.mp hx _ ⟨h, hh, rfl⟩

theorem map_subtype_rootCenter (L : Subgroup G) (P : Subgroup L) :
    (Bender.rootCenter P).map L.subtype = Bender.rootCenter (P.map L.subtype) := by
  change (P ⊓ centralizer (P : Set L)).map L.subtype =
    P.map L.subtype ⊓ centralizer ((P.map L.subtype : Subgroup G) : Set G)
  rw [map_inf_eq _ _ _ L.subtype_injective, map_subtype_centralizer, inf_comm (centralizer _) L,
    ← inf_assoc, inf_eq_left.mpr (map_subtype_le P)]

theorem map_subtype_normalizer (L : Subgroup G) (P : Subgroup L) :
    (normalizer (P : Set L)).map L.subtype =
      normalizer ((P.map L.subtype : Subgroup G) : Set G) ⊓ L := by
  have h1 : (P.map L.subtype).subgroupOf L = P := by
    rw [subgroupOf, comap_map_eq_self_of_injective L.subtype_injective]
  rw [← subgroupOf_map_subtype, subgroupOf_normalizer_eq (map_subtype_le P), h1]

theorem isSylowOf_map_subtype_sylow [Finite G] {p : ℕ} [Fact p.Prime] {L : Subgroup G}
    (Q : Sylow p L) {H : Subgroup G} (hQH : (Q : Subgroup L).map L.subtype ≤ H) (hHL : H ≤ L) :
    ABGLocalTools.IsSylowOf p ((Q : Subgroup L).map L.subtype) H :=
  ABGLocalTools.IsSylowOf.of_le ⟨Q, rfl⟩ hQH hHL

theorem isSylowOf_eq_of_normal [Finite G] {p : ℕ} [Fact p.Prime] {P T K : Subgroup G}
    (hT : ABGLocalTools.IsSylowOf p T K) (hTn : ∀ g ∈ K, ∀ x ∈ T, g * x * g⁻¹ ∈ T)
    (hP : ABGLocalTools.IsSylowOf p P K) : P = T := by
  obtain ⟨k, hk, hkx⟩ := hT.exists_mem_conj hP
  ext x
  rw [hkx]
  constructor
  · intro h
    have := hTn k hk _ h
    simpa [mul_assoc] using this
  · intro h
    have := hTn k⁻¹ (inv_mem hk) x h
    simpa using this

noncomputable def centerBotEquiv {E : Type*} [Group E] (hc : center E = ⊥) :
    E ≃* E ⧸ center E :=
  ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm

theorem centerBotEquiv_apply {E : Type*} [Group E] (hc : center E = ⊥) (x : E) :
    centerBotEquiv hc x = (x : E ⧸ center E) := by
  rw [centerBotEquiv, MulEquiv.symm_apply_eq]
  rfl

theorem centerBotEquiv_toMonoidHom {E : Type*} [Group E] (hc : center E = ⊥) :
    (centerBotEquiv hc).toMonoidHom = QuotientGroup.mk' (center E) :=
  MonoidHom.ext fun x => centerBotEquiv_apply hc x

theorem exists_sylow_normalizer_eq_of_center_eq_bot {E : Type*} [Group E] [Finite E] {p : ℕ}
    [Fact p.Prime] (hc : center E = ⊥) {H : Subgroup E} {T : Sylow p (E ⧸ center E)}
    (hT : H.map (QuotientGroup.mk' (center E)) =
      normalizer ((T : Subgroup (E ⧸ center E)) : Set (E ⧸ center E))) :
    ∃ Q : Sylow p E, H = normalizer ((Q : Subgroup E) : Set E) := by
  have hsurj : Function.Surjective (centerBotEquiv hc).symm.toMonoidHom := by
    rw [MulEquiv.coe_toMonoidHom]
    exact (centerBotEquiv hc).symm.surjective
  refine ⟨Sylow.mapSurjective hsurj T, ?_⟩
  rw [Sylow.coe_mapSurjective, ← map_equiv_normalizer_eq, ← hT, ← centerBotEquiv_toMonoidHom hc,
    map_map]
  have hid : (centerBotEquiv hc).symm.toMonoidHom.comp (centerBotEquiv hc).toMonoidHom =
      MonoidHom.id E :=
    MonoidHom.ext fun x => (centerBotEquiv hc).symm_apply_apply x
  rw [hid, map_id]

end Transport

section LDataAPI

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Ctx12

variable (c : Ctx12 Z M)

theorem t_mem_L : c.t ∈ c.L := mem_sup_left (mem_sup_right (mem_zpowers c.t))

theorem z_mem_L : c.z ∈ c.L := mem_sup_left (mem_sup_left (mem_zpowers c.z))

theorem kGrp_le_L : kGrp M c.t ≤ c.L := le_sup_right

abbrev tL : ↥c.L := ⟨c.t, c.t_mem_L⟩

abbrev zL : ↥c.L := ⟨c.z, c.z_mem_L⟩

theorem tL_mul_self (hZ : IsInvariantInvolutionSet Z) : c.tL * c.tL = 1 :=
  Subtype.ext (hZ.mul_self_eq_one c.ht)

theorem zL_ne_one (hZ : IsInvariantInvolutionSet Z) : c.zL ≠ 1 := by
  intro h1
  have h2 : c.z = 1 := congrArg Subtype.val h1
  have h3 := hZ.1 c.z c.hz
  rw [h2, orderOf_one] at h3
  exact absurd h3 (by norm_num)

variable {c}

theorem tL_not_mem_borel {Q : Subgroup c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer (Q : Set c.L)) : c.tL ∉ Bender.borel Q := by
  intro h
  have h' : c.tL ∈ (M ⊓ c.L).subgroupOf c.L := by
    rw [hQ]
    exact h
  exact c.htM (mem_inf.mp (mem_subgroupOf.mp h')).1

theorem map_subtype_cartan {Q : Subgroup c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer (Q : Set c.L)) :
    (Bender.cartan Q c.tL).map c.L.subtype = c.D ⊓ c.L :=
  CFSG.GH74.Uniqueness.map_subtype_cartan hQ c.t_mem_L

theorem map_sylow_le {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    (Q : Subgroup c.L).map c.L.subtype ≤ c.L ⊓ M := by
  have hle : (Q : Subgroup c.L) ≤ (M ⊓ c.L).subgroupOf c.L := by
    rw [hQ]
    exact le_normalizer
  have h2 := map_mono (f := c.L.subtype) hle
  rw [subgroupOf_map_subtype] at h2
  exact fun x hx => ⟨(h2 hx).2, (h2 hx).1.1⟩

theorem isSylowOf_map_sylow {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ABGLocalTools.IsSylowOf 2 ((Q : Subgroup c.L).map c.L.subtype) (c.L ⊓ M) :=
  isSylowOf_map_subtype_sylow Q (map_sylow_le hQ) inf_le_left

end Ctx12

namespace LData

variable {c : Ctx12 Z M} {n i : ℕ}

theorem benderCore
    (hZ : IsInvariantInvolutionSet Z) (h : LData c n i) {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    Bender.BenderCore (2 ^ n) i 1 (Q : Subgroup c.L) c.tL :=
  h.bender.benderCore Q (c.tL_mul_self hZ) (Ctx12.tL_not_mem_borel hQ)

theorem map_subtype_rootCenter
    (hZ : IsInvariantInvolutionSet Z) (h : LData c n i)
    {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    (Bender.rootCenter (Q : Subgroup c.L)).map c.L.subtype = zHull Z M := by
  have hc := h.benderCore hZ hQ
  have hle : zHull Z M ≤ (Bender.rootCenter (Q : Subgroup c.L)).map c.L.subtype := by
    refine (closure_le _).mpr fun x hx => ?_
    have hxL : x ∈ c.L := h.m_le (subset_closure hx)
    have hxB : (⟨x, hxL⟩ : c.L) ∈ Bender.borel (Q : Subgroup c.L) := by
      change _ ∈ normalizer _
      rw [← hQ]
      exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hx.2, hxL⟩)
    have hxo : orderOf (⟨x, hxL⟩ : c.L) = 2 := by
      rw [orderOf_mk]
      exact hZ.1 x hx.1
    exact ⟨⟨x, hxL⟩, hc.center_of_involution _ hxB hxo, rfl⟩
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective c.L.subtype_injective, hc.card_center, h.m_card]

theorem zL_mem_rootCenter
    (hZ : IsInvariantInvolutionSet Z) (h : LData c n i)
    {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    c.zL ∈ Bender.rootCenter (Q : Subgroup c.L) := by
  have hz : c.z ∈ zHull Z M := subset_closure ⟨c.hz, c.hzM⟩
  rw [← h.map_subtype_rootCenter hZ hQ] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hy' : y = c.zL := Subtype.ext hyz
  rwa [← hy']

theorem map_subtype_commutator_cartan
    (hZ : IsInvariantInvolutionSet Z) (h : LData c n i)
    {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    (⁅Bender.cartan (Q : Subgroup c.L) c.tL, zpowers c.tL⁆).map c.L.subtype = kGrp M c.t := by
  rw [← (h.benderCore hZ hQ).cartan_eq_commutator rfl, Ctx12.map_subtype_cartan hQ, h.k_eq']

theorem fixCartan_eq_bot
    (hZ : IsInvariantInvolutionSet Z) (h : LData c n i) {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    Bender.fixCartan (Q : Subgroup c.L) c.tL = ⊥ :=
  (h.benderCore hZ hQ).fixCartan_eq_bot

theorem nM_eq_sylow (h : LData c n i) {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ((M ⊓ normalizer (c.L : Set X) : Subgroup X) : Set X) =
      (((Q : Subgroup c.L).map c.L.subtype : Subgroup X) : Set X) * (c.D : Set X) := by
  obtain ⟨T, -, -, hT, hTn, hTD⟩ := h.nM_eq
  rw [hTD, isSylowOf_eq_of_normal hT hTn (Ctx12.isSylowOf_map_sylow hQ)]

theorem center_eq_bot (h : LData c n i) : center ↥c.L = ⊥ := by
  have hs : IsSimpleGroup ↥c.L := h.bender.isSimple
  rcases Subgroup.Normal.eq_bot_or_eq_top (center ↥c.L) with hc | hc
  · exact hc
  · exfalso
    apply h.bender.isSimpleBenderGroup.not_commutative
    intro x y
    have hy : y ∈ center ↥c.L := hc ▸ mem_top y
    exact mem_center_iff.mp hy x

end LData

end LDataAPI

end CFSG.GH74.Uniqueness
