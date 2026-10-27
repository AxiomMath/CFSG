module

public import CFSG.GH74.Uniqueness.Section13Gen
public import CFSG.GH74.Uniqueness.Section126Basic
public import CFSG.GH74.Uniqueness.Section128Bender
public import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section Generic

omit [Finite X] in
theorem A6.subgroupOf_map_subtype_eq (K : Subgroup X) (Q : Subgroup ↥K) :
    (Q.map K.subtype).subgroupOf K = Q :=
  Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q

theorem A6.card_map_of_ker {G K : Type*} [Group G] [Group K] (f : G →* K) (H : Subgroup G)
    (hinj : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card (H.map f) = Nat.card H := by
  have hinj' : Function.Injective (f.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have h1 : H.map f = (f.comp H.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm

omit [Finite X] in
theorem A6.card_subgroupOf {H K : Subgroup X} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

end Generic

structure A6.Dict (Z : Set X) (M F : Subgroup X) (n e : ℕ) (Tb : Sylow 2 (↥F ⧸ center ↥F))
    (T : Subgroup X) : Prop where
  bsub : BenderSub Z M F n 3 e
  borel : ((M ⊓ F).subgroupOf F).map (QuotientGroup.mk' (center ↥F)) =
    normalizer ((Tb : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F))
  le : T ≤ F
  isP : IsPGroup 2 T
  map : (T.subgroupOf F).map (QuotientGroup.mk' (center ↥F)) = Tb

theorem A6.exists_dict {F : Subgroup X} {n e : ℕ} (hB : BenderSub Z M F n 3 e) :
    ∃ Tb T, A6.Dict Z M F n e Tb T := by
  obtain ⟨Tb, hTb⟩ := hB.borel
  obtain ⟨Q, hQ⟩ := A6.exists_sylow_map_eq (center ↥F) Tb
  refine ⟨Tb, (Q : Subgroup ↥F).map F.subtype, hB, hTb, map_subtype_le _, Q.isPGroup'.map _, ?_⟩
  rw [A6.subgroupOf_map_subtype_eq]
  exact hQ

namespace A6.Dict

variable {F T : Subgroup X} {n e : ℕ} {Tb : Sylow 2 (↥F ⧸ center ↥F)}

theorem odd (h : A6.Dict Z M F n e Tb T) : Odd (Nat.card (center ↥F)) :=
  A2.odd_card_center_of_benderSub h.bsub

omit [Finite X] in
theorem mk_mem (h : A6.Dict Z M F n e Tb T) {x : X} (hxT : x ∈ T) :
    QuotientGroup.mk' (center ↥F) ⟨x, h.le hxT⟩ ∈ (Tb : Subgroup (↥F ⧸ center ↥F)) := by
  rw [← h.map]
  exact ⟨⟨x, h.le hxT⟩, hxT, rfl⟩

omit [Finite X] in
theorem two (h : A6.Dict Z M F n e Tb T) {x : X} (hxT : x ∈ T) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h.isP ⟨x, hxT⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite X] in
theorem pow_mk {x : X} (hxF : x ∈ F) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    (⟨x, hxF⟩ : ↥F) ^ 2 ^ k = 1 :=
  Subtype.ext (by simpa using hk)

theorem mem_of_two (h : A6.Dict Z M F n e Tb T) {x : X} (hxF : x ∈ F) {k : ℕ}
    (hk : x ^ 2 ^ k = 1)
    (hx : QuotientGroup.mk' (center ↥F) ⟨x, hxF⟩ ∈ (Tb : Subgroup (↥F ⧸ center ↥F))) : x ∈ T := by
  have hP : IsPGroup 2 (T.subgroupOf F) := h.isP.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
  have := A6.mem_of_two_of_mk_mem h.odd le_rfl hP (pow_mk hxF hk) (by rw [h.map]; exact hx)
  exact this

theorem eq_of_mk_eq (h : A6.Dict Z M F n e Tb T) {x y : X} (hx : x ∈ T) (hy : y ∈ T)
    (hxy : QuotientGroup.mk' (center ↥F) ⟨x, h.le hx⟩ = QuotientGroup.mk' (center ↥F) ⟨y, h.le hy⟩) :
    x = y := by
  obtain ⟨k, hk⟩ := h.two hx
  obtain ⟨l, hl⟩ := h.two hy
  have := A6.eq_of_inv_mul_mem_two h.odd le_rfl (pow_mk (h.le hx) hk) (pow_mk (h.le hy) hl)
    (QuotientGroup.eq.mp hxy)
  exact congrArg Subtype.val this

theorem le_M (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T) : T ≤ M := fun x hxT =>
  (A2.mk_mem_normalizer_iff S h.bsub h.borel ⟨x, h.le hxT⟩).mp
    (Bender.le_borel _ (h.mk_mem hxT))

theorem mem_of_mem_M (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T) {x : X} (hxM : x ∈ M)
    (hxF : x ∈ F) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ T := by
  apply h.mem_of_two hxF hk
  have hN : QuotientGroup.mk' (center ↥F) ⟨x, hxF⟩ ∈
      normalizer ((Tb : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) :=
    (A2.mk_mem_normalizer_iff S h.bsub h.borel _).mpr hxM
  have hk' : (QuotientGroup.mk' (center ↥F) ⟨x, hxF⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow, pow_mk hxF hk, map_one]
  exact A6.mem_of_mem_normalizer_sylow Tb hN hk'

theorem card_eq
    (h : A6.Dict Z M F n e Tb T) : Nat.card T = (2 ^ n) ^ 3 := by
  obtain ⟨t, hc⟩ := h.bsub.bender.exists_benderCore Tb
  have h1 := A6.card_map_of_ker (QuotientGroup.mk' (center ↥F)) (T.subgroupOf F) (by
    intro x hx hx1
    have hx' : (x : X) ∈ T := hx
    have h2 := h.eq_of_mk_eq hx' T.one_mem (by rw [hx1]; exact (map_one _).symm)
    exact Subtype.ext h2)
  rw [h.map, hc.card_eq, A6.card_subgroupOf h.le] at h1
  exact h1.symm

theorem zHull_le {c : Ctx12 Z M} {n' i : ℕ} (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T)
    (hL : LData c n' i) (hMF : zHull Z M ≤ F) : zHull Z M ≤ T := fun m hm =>
  h.mem_of_mem_M S (Cor713.zHull_le M hm) (hMF hm) (k := 1)
    (by rw [pow_one, sq]; exact hL.sec126_zHull_sq hm)

theorem map_zHull
    {c : Ctx12 Z M} {i : ℕ} (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T)
    (hL : LData c n i) (hMF : zHull Z M ≤ F) :
    ((zHull Z M).subgroupOf F).map (QuotientGroup.mk' (center ↥F)) =
      Bender.rootCenter (Tb : Subgroup (↥F ⧸ center ↥F)) := by
  obtain ⟨t, hc⟩ := h.bsub.bender.exists_benderCore Tb
  have hMT := h.zHull_le S hL hMF
  have hle : ((zHull Z M).subgroupOf F).map (QuotientGroup.mk' (center ↥F)) ≤
      Bender.rootCenter (Tb : Subgroup (↥F ⧸ center ↥F)) := by
    apply hc.elemAbelian_le_rootCenter
    · rintro _ ⟨m, hm, rfl⟩
      exact h.mk_mem (hMT hm)
    · rintro _ ⟨m, hm, rfl⟩
      rw [← map_mul]
      have : m * m = 1 := Subtype.ext (hL.sec126_zHull_sq hm)
      rw [this, map_one]
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hc.card_center, A6.card_map_of_ker _ _ (fun x hx hx1 => by
      have hx' : (x : X) ∈ T := hMT hx
      exact Subtype.ext (h.eq_of_mk_eq hx' T.one_mem (by rw [hx1]; exact (map_one _).symm))),
    A6.card_subgroupOf hMF, hL.m_card]

theorem mem_zHull_iff
    {c : Ctx12 Z M} {i : ℕ} (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T)
    (hL : LData c n i) (hMF : zHull Z M ≤ F) {x : X} (hxT : x ∈ T) :
    x ∈ zHull Z M ↔ QuotientGroup.mk' (center ↥F) ⟨x, h.le hxT⟩ ∈
      Bender.rootCenter (Tb : Subgroup (↥F ⧸ center ↥F)) := by
  rw [← h.map_zHull S hL hMF]
  constructor
  · intro hx
    exact ⟨⟨x, h.le hxT⟩, hx, rfl⟩
  · rintro ⟨m, hm, hmx⟩
    have hmT : (m : X) ∈ T := h.zHull_le S hL hMF hm
    have := h.eq_of_mk_eq hmT hxT hmx
    rw [← this]
    exact hm

theorem mem_zHull_of_mul_self
    {c : Ctx12 Z M} {i : ℕ} (S : ZDSetup X Z M)
    (h : A6.Dict Z M F n e Tb T) (hL : LData c n i) (hMF : zHull Z M ≤ F) {x : X} (hxT : x ∈ T)
    (hxx : x * x = 1) : x ∈ zHull Z M := by
  rw [h.mem_zHull_iff S hL hMF hxT]
  obtain ⟨t, hc⟩ := h.bsub.bender.exists_benderCore Tb
  refine hc.mem_rootCenter_of_mul_self (h.mk_mem hxT) ?_
  rw [← map_mul]
  have : (⟨x, h.le hxT⟩ : ↥F) * ⟨x, h.le hxT⟩ = 1 := Subtype.ext hxx
  rw [this, map_one]

theorem comm_of_mem_zHull {c : Ctx12 Z M} {i : ℕ} (S : ZDSetup X Z M)
    (h : A6.Dict Z M F n e Tb T) (hL : LData c n i) (hMF : zHull Z M ≤ F) {m s : X}
    (hm : m ∈ zHull Z M) (hs : s ∈ T) : m * s = s * m := by
  have hmT := h.zHull_le S hL hMF hm
  have hmR := (h.mem_zHull_iff S hL hMF hmT).mp hm
  have h1 := (Bender.mem_rootCenter_iff.mp hmR).2 _ (h.mk_mem hs)
  have hc : m * s * m⁻¹ ∈ T := T.mul_mem (T.mul_mem hmT hs) (T.inv_mem hmT)
  have h2 : QuotientGroup.mk' (center ↥F) ⟨m * s * m⁻¹, h.le hc⟩ =
      QuotientGroup.mk' (center ↥F) ⟨s, h.le hs⟩ := by
    have e1 : (⟨m * s * m⁻¹, h.le hc⟩ : ↥F) = ⟨m, h.le hmT⟩ * ⟨s, h.le hs⟩ * ⟨m, h.le hmT⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
  have h3 := h.eq_of_mk_eq hc hs h2
  calc m * s = (m * s * m⁻¹) * m := by group
    _ = s * m := by rw [h3]

theorem center_iff
    {c : Ctx12 Z M} {i : ℕ} (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T)
    (hL : LData c n i) (hMF : zHull Z M ≤ F) {x : X} (hxT : x ∈ T) :
    (∀ s ∈ T, x * s = s * x) ↔ x ∈ zHull Z M := by
  constructor
  · intro hx
    rw [h.mem_zHull_iff S hL hMF hxT, Bender.mem_rootCenter_iff]
    refine ⟨h.mk_mem hxT, fun p hp => ?_⟩
    rw [← h.map] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    have hs' : (s : X) ∈ T := hs
    have h1 : (s : ↥F) * ⟨x, h.le hxT⟩ = ⟨x, h.le hxT⟩ * s := Subtype.ext (hx s hs').symm
    rw [← map_mul, h1, map_mul]
  · intro hx s hs
    exact h.comm_of_mem_zHull S hL hMF hx hs

theorem tbar (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T) {t : X} (htF : t ∈ F) (htZ : t ∈ Z)
    (htM : t ∉ M) :
    QuotientGroup.mk' (center ↥F) ⟨t, htF⟩ * QuotientGroup.mk' (center ↥F) ⟨t, htF⟩ = 1 ∧
      QuotientGroup.mk' (center ↥F) ⟨t, htF⟩ ∉ Bender.borel (Tb : Subgroup (↥F ⧸ center ↥F)) := by
  refine ⟨?_, fun hb => htM ((A2.mk_mem_normalizer_iff S h.bsub h.borel _).mp hb)⟩
  rw [← map_mul]
  have : (⟨t, htF⟩ : ↥F) * ⟨t, htF⟩ = 1 := Subtype.ext (S.invariant.mul_self_eq_one htZ)
  rw [this, map_one]

theorem irred
    {c : Ctx12 Z M} {i : ℕ} (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T)
    (hL : LData c n i) (hMF : zHull Z M ≤ F) {t : X} (htF : t ∈ F) (htZ : t ∈ Z) (htM : t ∉ M)
    {H : Subgroup X}
    (hH : ∀ d ∈ Bender.cartan (Tb : Subgroup (↥F ⧸ center ↥F))
        (QuotientGroup.mk' (center ↥F) ⟨t, htF⟩),
      ∃ g : X, ∃ hgF : g ∈ F, g ∈ H ∧ QuotientGroup.mk' (center ↥F) ⟨g, hgF⟩ = d)
    {W : Subgroup X} (hMW : zHull Z M ≤ W) (hWT : W ≤ T)
    (hHW : ∀ g ∈ H, ∀ w ∈ W, g * w * g⁻¹ ∈ W) : W = zHull Z M ∨ W = T := by
  obtain ⟨htb, htbQ⟩ := h.tbar S htF htZ htM
  set Wb : Subgroup (↥F ⧸ center ↥F) := (W.subgroupOf F).map (QuotientGroup.mk' (center ↥F))
    with hWb
  have hZW : Bender.rootCenter (Tb : Subgroup (↥F ⧸ center ↥F)) ≤ Wb := by
    rw [← h.map_zHull S hL hMF]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono F hMW)
  have hWQ : Wb ≤ (Tb : Subgroup (↥F ⧸ center ↥F)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact h.mk_mem (hWT hw)
  have hinv : ∀ d ∈ Bender.cartan (Tb : Subgroup (↥F ⧸ center ↥F))
      (QuotientGroup.mk' (center ↥F) ⟨t, htF⟩), ∀ w ∈ Wb, d * w * d⁻¹ ∈ Wb := by
    rintro d hd _ ⟨w, hw, rfl⟩
    obtain ⟨g, hgF, hgH, rfl⟩ := hH d hd
    have hw' : (w : X) ∈ W := hw
    refine ⟨⟨g, hgF⟩ * w * ⟨g, hgF⟩⁻¹, hHW g hgH w hw', ?_⟩
    rw [map_mul, map_mul, map_inv]
  rcases h.bsub.bender.irreducible_unitary Tb htb htbQ Wb hZW hWQ hinv with h1 | h1
  · left
    refine le_antisymm (fun w hw => ?_) hMW
    rw [h.mem_zHull_iff S hL hMF (hWT hw), ← h1]
    exact ⟨⟨w, h.le (hWT hw)⟩, hw, rfl⟩
  · right
    refine le_antisymm hWT (fun s hs => ?_)
    have hs' := h.mk_mem hs
    rw [← h1] at hs'
    obtain ⟨w, hw, hws⟩ := hs'
    have hw' : (w : X) ∈ W := hw
    have := h.eq_of_mk_eq (hWT hw') hs hws
    rw [← this]
    exact hw'

theorem fpf
    {c : Ctx12 Z M} {i : ℕ} (S : ZDSetup X Z M) (h : A6.Dict Z M F n e Tb T)
    (hL : LData c n i) (hMF : zHull Z M ≤ F) {t : X} (htF : t ∈ F) (htZ : t ∈ Z) (htM : t ∉ M)
    {a : X} (haF : a ∈ F)
    (ha : QuotientGroup.mk' (center ↥F) ⟨a, haF⟩ ∈ Bender.cartan (Tb : Subgroup (↥F ⧸ center ↥F))
      (QuotientGroup.mk' (center ↥F) ⟨t, htF⟩))
    (ha1 : QuotientGroup.mk' (center ↥F) ⟨a, haF⟩ ≠ 1) {s : X} (hs : s ∈ T)
    (hcomm : a * s * a⁻¹ * s⁻¹ ∈ zHull Z M) : s ∈ zHull Z M := by
  obtain ⟨htb, htbQ⟩ := h.tbar S htF htZ htM
  rw [h.mem_zHull_iff S hL hMF hs]
  refine h.bsub.bender.fixedPointFree_unitary Tb htb htbQ ha ha1 (h.mk_mem hs) ?_
  have hmem : a * s * a⁻¹ * s⁻¹ ∈ F :=
    F.mul_mem (F.mul_mem (F.mul_mem haF (h.le hs)) (F.inv_mem haF)) (F.inv_mem (h.le hs))
  have e1 : QuotientGroup.mk' (center ↥F) ⟨a, haF⟩ * QuotientGroup.mk' (center ↥F) ⟨s, h.le hs⟩ *
      (QuotientGroup.mk' (center ↥F) ⟨a, haF⟩)⁻¹ * (QuotientGroup.mk' (center ↥F) ⟨s, h.le hs⟩)⁻¹ =
      QuotientGroup.mk' (center ↥F) ⟨a * s * a⁻¹ * s⁻¹, hmem⟩ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e1, ← h.map_zHull S hL hMF]
  exact ⟨⟨a * s * a⁻¹ * s⁻¹, hmem⟩, hcomm, rfl⟩

end A6.Dict

section Count

theorem A6.ncard_Z_inter
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) :
    (Z ∩ (F : Set X)).ncard = (2 ^ n - 1) * ((2 ^ n) ^ i + 1) := by
  have hcount := Cor713.ncard_involutions_eq (QuotientGroup.mk' (center ↥F))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (A2.odd_card_center_of_benderSub hB)
    (fun o ho g => (mem_center_iff.mp ho g).symm) (B := ⊤) (Y := ⊤) (fun g => by simp)
  have e1 : {k : ↥F ⧸ center ↥F | k ∈ (⊤ : Subgroup (↥F ⧸ center ↥F)) ∧ orderOf k = 2} =
      {k : ↥F ⧸ center ↥F | orderOf k = 2} := by
    ext k
    simp
  rw [e1, hB.bender.ncard_involutions] at hcount
  have himage : (Subtype.val : ↥F → X) '' {y : ↥F | y ∈ (⊤ : Subgroup ↥F) ∧ orderOf y = 2} =
      Z ∩ (F : Set X) := by
    ext x
    constructor
    · rintro ⟨y, ⟨-, hy2⟩, rfl⟩
      exact ⟨hB.invol y y.2 (by rw [Subgroup.orderOf_coe]; exact hy2), y.2⟩
    · rintro ⟨hxZ, hxF⟩
      refine ⟨⟨x, hxF⟩, ⟨mem_top _, ?_⟩, rfl⟩
      rw [Subgroup.orderOf_mk]
      exact S.invariant.1 x hxZ
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective, hcount]

omit [Finite X] in
theorem A6.eq_of_le_of_ncard_le [Finite X] {F₁ F₂ : Subgroup X} (hF₁ : zHull Z F₁ = F₁)
    (hF₂ : zHull Z F₂ = F₂) (hle : F₁ ≤ F₂)
    (hcard : (Z ∩ (F₂ : Set X)).ncard ≤ (Z ∩ (F₁ : Set X)).ncard) : F₁ = F₂ := by
  have hsub : Z ∩ (F₁ : Set X) ⊆ Z ∩ (F₂ : Set X) := Set.inter_subset_inter_right Z hle
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  rw [← hF₁, ← hF₂]
  unfold zHull
  rw [heq]

end Count

end CFSG.GH74.Uniqueness
