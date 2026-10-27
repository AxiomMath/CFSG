module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ReifartTransport
public import CFSG.CGT.PushingUpLit.CGT6.EmbCentral

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.CGT.PushingUpLit.CGT6

section Abstract

variable {L L' : Type} [Group L] [Group L'] {Θ : L →* L'}

theorem pCore_two_eq_comap (hs : Function.Surjective Θ) (hk : IsPGroup 2 ↥Θ.ker) :
    CFSG.pCore 2 L = (CFSG.pCore 2 L').comap Θ :=
  TwoQuot.pCore_eq (Θ := Θ) ⟨hs, hk⟩

theorem O23Abs_eq_comap (hs : Function.Surjective Θ) (hk : IsPGroup 2 ↥Θ.ker) :
    DS81.Reifart.O23Abs L = (DS81.Reifart.O23Abs L').comap Θ := by
  have h : TwoQuot Θ := ⟨hs, hk⟩
  have hP3 := CFSG.pCore_map_iso 3 h.quotPCore
  ext l
  rw [Subgroup.mem_comap]
  have hf : h.quotPCore (QuotientGroup.mk' (CFSG.pCore 2 L) l) =
      QuotientGroup.mk' (CFSG.pCore 2 L') (Θ l) := h.quotPCore_mk l
  unfold DS81.Reifart.O23Abs
  rw [Subgroup.mem_comap, Subgroup.mem_comap, ← hP3, Subgroup.mem_map_equiv, ← hf,
    MulEquiv.symm_apply_apply]

end Abstract

variable {G : Type} [Group G] {E : Subgroup G} {t : G}

@[expose] def actPreS (T : Subgroup (MulAut ↥E)) : ↥(preS T) →* ↥T :=
  ((S44.actN E).comp (Subgroup.inclusion (preS_le_normalizer T))).codRestrict T
    fun s => (mem_preS_iff_of_mem (preS_le_normalizer T s.2)).1 s.2

theorem actPreS_apply (T : Subgroup (MulAut ↥E)) (s : ↥(preS T)) :
    ((actPreS T s : ↥T) : MulAut ↥E) = S44.actN E ⟨s, preS_le_normalizer T s.2⟩ := rfl

theorem actPreS_surjective {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) :
    Function.Surjective (actPreS T) := by
  intro g
  obtain ⟨y, hy, hyg⟩ := exists_mem_preS_actN hT g.2
  exact ⟨⟨y, hy⟩, Subtype.ext hyg⟩

theorem ker_actPreS (hCE : centralizer (E : Set G) = E) (T : Subgroup (MulAut ↥E)) :
    (actPreS T).ker = E.subgroupOf (preS T) := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_E_iff_actN_eq_one hCE (preS_le_normalizer T s.2)]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem isPGroup_ker_actPreS (hm : M24Out G E t) (T : Subgroup (MulAut ↥E)) :
    IsPGroup 2 ↥(actPreS T).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ker_actPreS hm.centralizer_eq]
  refine IsPGroup.of_card (n := 11) ?_
  rw [← hm.card_E]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E_le_preS hm.centralizer_eq T)).toEquiv

theorem map_comap_actPreS (T : Subgroup (MulAut ↥E)) (K : Subgroup ↥T) :
    (K.comap (actPreS T)).map (preS T).subtype = preS (K.map T.subtype) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact mem_preS.2 ⟨preS_le_normalizer T s.2, ⟨actPreS T s, hs, rfl⟩⟩
  · intro hx
    obtain ⟨hxN, k, hk, hkx⟩ := mem_preS.1 hx
    have hxS : x ∈ preS T := mem_preS.2 ⟨hxN, by rw [← hkx]; exact k.2⟩
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    have h1 : actPreS T ⟨x, hxS⟩ = k := Subtype.ext hkx.symm
    rw [Subgroup.mem_comap, h1]
    exact hk

theorem O2In_preS (hm : M24Out G E t) {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) :
    TwoFi22.O2In (preS T) = preS (TwoFi22.O2In T) := by
  have h := pCore_two_eq_comap (actPreS_surjective hT) (isPGroup_ker_actPreS hm T)
  show (CFSG.pCore 2 ↥(preS T)).map (preS T).subtype =
    preS ((CFSG.pCore 2 ↥T).map T.subtype)
  rw [h, map_comap_actPreS]

theorem O23In_preS (hm : M24Out G E t) {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) :
    TwoFi22.O23In (preS T) = preS (TwoFi22.O23In T) := by
  have h := O23Abs_eq_comap (actPreS_surjective hT) (isPGroup_ker_actPreS hm T)
  show (DS81.Reifart.O23Abs ↥(preS T)).map (preS T).subtype =
    preS ((DS81.Reifart.O23Abs ↥T).map T.subtype)
  rw [h, map_comap_actPreS]

theorem O2In_le {H : Type} [Group H] (T : Subgroup H) : TwoFi22.O2In T ≤ T := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem O23In_le {H : Type} [Group H] (T : Subgroup H) : TwoFi22.O23In T ≤ T :=
  Subgroup.map_subtype_le _

theorem O2In_conj_mem {H : Type} [Group H] {T : Subgroup H} {g x : H} (hg : g ∈ T)
    (hx : x ∈ TwoFi22.O2In T) : g * x * g⁻¹ ∈ TwoFi22.O2In T := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥T)).conj_mem y hy ⟨g, hg⟩, rfl⟩

theorem Pg_eq_preS (hm : M24Out G E t) {z : G} (hz : z ∈ E) :
    Pg E z = preS (TwoFi22.O2In (S44.XE E ⊓ @Quasithin.centSub ↥E (commGroupOfM24Out hm)
      (zpowers (⟨z, hz⟩ : ↥E)))) := by
  rw [Pg, CNz_eq_preS hm hz, O2In_preS hm inf_le_left]

theorem O23In_CNz_eq_preS (hm : M24Out G E t) {z : G} (hz : z ∈ E) :
    TwoFi22.O23In (CNz E z) = preS (TwoFi22.O23In (S44.XE E ⊓
      @Quasithin.centSub ↥E (commGroupOfM24Out hm) (zpowers (⟨z, hz⟩ : ↥E)))) := by
  rw [CNz_eq_preS hm hz, O23In_preS hm inf_le_left]

theorem O2In_Nrm_inf_Jg_eq_preS (hm : M24Out G E t) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    TwoFi22.O2In (Nrm E ⊓ Jg x y) = preS (TwoFi22.O2In (S44.XE E ⊓
      @Quasithin.stabSub ↥E (commGroupOfM24Out hm) (closure {(⟨x, hx⟩ : ↥E), ⟨y, hy⟩}))) := by
  rw [Nrm_inf_Jg_eq_preS hm hx hy, O2In_preS hm inf_le_left]

theorem card_Pg (hm : M24Out G E t) {z : G} (hz : z ∈ E) :
    Nat.card ↥(Pg E z) = 2 ^ 11 * Nat.card ↥(TwoFi22.O2In (S44.XE E ⊓
      @Quasithin.centSub ↥E (commGroupOfM24Out hm) (zpowers (⟨z, hz⟩ : ↥E)))) := by
  rw [Pg_eq_preS hm hz]
  exact card_preS hm ((O2In_le _).trans inf_le_left)

theorem card_O23In_CNz (hm : M24Out G E t) {z : G} (hz : z ∈ E) :
    Nat.card ↥(TwoFi22.O23In (CNz E z)) = 2 ^ 11 * Nat.card ↥(TwoFi22.O23In (S44.XE E ⊓
      @Quasithin.centSub ↥E (commGroupOfM24Out hm) (zpowers (⟨z, hz⟩ : ↥E)))) := by
  rw [O23In_CNz_eq_preS hm hz]
  exact card_preS hm ((O23In_le _).trans inf_le_left)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
