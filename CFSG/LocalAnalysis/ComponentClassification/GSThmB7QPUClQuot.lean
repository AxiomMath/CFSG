module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup

variable {M : Type*} [Group M]

@[expose] def quotAut (M : Type*) [Group M] : MulAut M →* MulAut (M ⧸ center M) where
  toFun α := QuotientGroup.congr (center M) (center M) α
    (Subgroup.characteristic_iff_map_eq.1 inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem quotAut_mk (α : MulAut M) (m : M) :
    quotAut M α (m : M ⧸ center M) = ((α m : M) : M ⧸ center M) := rfl

theorem quotAut_conj (t : M) :
    quotAut M (MulAut.conj t) = MulAut.conj (t : M ⧸ center M) := by
  ext x
  induction x using QuotientGroup.induction_on
  rfl

@[expose] def fixedBy (E : Subgroup (MulAut M)) : Subgroup M where
  carrier := {m | ∀ e ∈ E, e m = m}
  one_mem' := fun e _ => map_one e
  mul_mem' := fun ha hb e he => by rw [map_mul, ha e he, hb e he]
  inv_mem' := fun ha e he => by rw [map_inv, ha e he]

theorem mem_fixedBy {E : Subgroup (MulAut M)} {m : M} : m ∈ fixedBy E ↔ ∀ e ∈ E, e m = m :=
  Iff.rfl

theorem fixedBy_zpowers_conj (t : M) : fixedBy (zpowers (MulAut.conj t)) = centralizer {t} := by
  ext m
  rw [mem_fixedBy, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have e := h (MulAut.conj t) (mem_zpowers _)
    rw [MulAut.conj_apply] at e
    calc m * t = t * m * t⁻¹ * t := by rw [e]
      _ = t * m := by group
  · rintro hmt _ ⟨k, rfl⟩
    have hc : Commute t m := hmt.symm
    change (MulAut.conj t) ^ k • m = m
    rw [← map_zpow, MulAut.smul_def, MulAut.conj_apply]
    have hck : Commute (t ^ k) m := Commute.zpow_left hc k
    rw [hck.eq, mul_inv_cancel_right]

theorem map_fixedBy_le (E : Subgroup (MulAut M)) :
    (fixedBy E).map (QuotientGroup.mk' (center M)) ≤ fixedBy (E.map (quotAut M)) := by
  rintro _ ⟨m, hm, rfl⟩ _ ⟨e, he, rfl⟩
  change quotAut M e (m : M ⧸ center M) = m
  rw [quotAut_mk, hm e he]

theorem normal_map_fixedBy (E : Subgroup (MulAut M)) :
    (((fixedBy E).map (QuotientGroup.mk' (center M))).subgroupOf
      (fixedBy (E.map (quotAut M)))).Normal := by
  constructor
  intro a ha g
  rw [mem_subgroupOf] at ha ⊢
  obtain ⟨n, hn, hna⟩ := ha
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (g : M ⧸ center M)
  refine ⟨x * n * x⁻¹, fun e he => ?_, ?_⟩
  · have hg : quotAut M e (x : M ⧸ center M) = x := by
      rw [hx]
      exact g.2 _ ⟨e, he, rfl⟩
    rw [quotAut_mk, QuotientGroup.eq] at hg
    have hzc := mem_center_iff.1 hg
    have hex : e x = x * ((e x)⁻¹ * x)⁻¹ := by group
    rw [map_mul, map_mul, map_inv, hex, hn e he]
    calc x * ((e x)⁻¹ * x)⁻¹ * n * (x * ((e x)⁻¹ * x)⁻¹)⁻¹ =
        x * (((e x)⁻¹ * x)⁻¹ * (n * ((e x)⁻¹ * x))) * x⁻¹ := by group
      _ = x * (((e x)⁻¹ * x)⁻¹ * (((e x)⁻¹ * x) * n)) * x⁻¹ := by rw [hzc n]
      _ = x * n * x⁻¹ := by group
  · rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, QuotientGroup.mk'_apply,
      hx, hna]
    rfl

variable [Finite M]

theorem isPComponent_map_fixedBy (E : Subgroup (MulAut M)) {L : Subgroup M}
    (hLE : L ≤ fixedBy E) (hL : IsPComponent 2 (L.subgroupOf (fixedBy E))) :
    L.map (QuotientGroup.mk' (center M)) ≤ fixedBy (E.map (quotAut M)) ∧
      IsPComponent 2 ((L.map (QuotientGroup.mk' (center M))).subgroupOf
        (fixedBy (E.map (quotAut M)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center M) with hπ
  set H := fixedBy E with hH
  set Hb := fixedBy (E.map (quotAut M)) with hHb
  set N := H.map π with hN
  have hNHb : N ≤ Hb := map_fixedBy_le E
  have hLN : L.map π ≤ N := map_mono hLE
  set φ : H →* N := (π.comp H.subtype).codRestrict N (fun h => ⟨h, h.2, rfl⟩) with hφ
  have hφs : Function.Surjective φ := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  have hφc : φ.ker ≤ center H := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have h1 : π (h : M) = 1 := congrArg Subtype.val hh
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 h1 g)
  have h1 := CatalogueBCentralQuotient.pComponent_map 2 φ hφs hφc _ hL
  have hmap : (L.subgroupOf H).map φ = (L.map π).subgroupOf N := by
    ext ⟨y, hy⟩
    simp only [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨⟨h, hh⟩, hhL, hhy⟩
      exact ⟨h, hhL, congrArg Subtype.val hhy⟩
    · rintro ⟨h, hhL, rfl⟩
      exact ⟨⟨h, hLE hhL⟩, hhL, rfl⟩
  rw [hmap] at h1
  refine ⟨hLN.trans hNHb, ?_⟩
  have : (N.subgroupOf Hb).Normal := normal_map_fixedBy E
  have h2 := (LieType.AlgebraicGroups.isPComponent_subgroupOf_subgroupOf_iff hNHb 2
    Nat.prime_two).2 h1
  exact (CatalogueBFixedCentralQuotient.pComponent_normal_iff 2 (N.subgroupOf Hb) _
    (fun x hx => by
      rw [mem_subgroupOf] at hx ⊢
      exact hLN hx)).1 h2

theorem isPComponent_map_centralizer (t : M) {J : Subgroup M} (hJt : J ≤ centralizer {t})
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer {t}))) :
    J.map (QuotientGroup.mk' (center M)) ≤ centralizer {(t : M ⧸ center M)} ∧
      IsPComponent 2 ((J.map (QuotientGroup.mk' (center M))).subgroupOf
        (centralizer {(t : M ⧸ center M)})) := by
  have hE : fixedBy ((zpowers (MulAut.conj t)).map (quotAut M)) =
      centralizer {(t : M ⧸ center M)} := by
    rw [MonoidHom.map_zpowers, quotAut_conj, fixedBy_zpowers_conj]
  rw [← fixedBy_zpowers_conj] at hJt hJ
  have h := isPComponent_map_fixedBy (zpowers (MulAut.conj t)) hJt hJ
  rw [hE] at h
  exact h

end CFSG.ComponentClassification.GSThmB.QPUCl
