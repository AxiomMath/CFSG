module

public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem card_centralizerIn_eq_of_mem_conjClass {M : Type*} [Group M] (H : Subgroup M) [Finite H]
    {t u : M} (hu : u ∈ conjClass H t) :
    Nat.card (centralizerIn H u) = Nat.card (centralizerIn H t) := by
  have hcls : conjClass H u = conjClass H t := by
    obtain ⟨h, hh, rfl⟩ := hu
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g * h, H.mul_mem hg hh, by group⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g * h⁻¹, H.mul_mem hg (H.inv_mem hh), by group⟩
  have h1 := ncard_conjClass_mul_card H u
  have h2 := ncard_conjClass_mul_card H t
  rw [hcls] at h1
  have hpos : 0 < (conjClass H t).ncard := by
    rcases Nat.eq_zero_or_pos (conjClass H t).ncard with h0 | h0
    · exfalso
      rw [h0, zero_mul] at h2
      exact (Nat.card_pos (α := ↥H)).ne' h2.symm
    · exact h0
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

theorem card_centralizer_eq_centralizerIn {L M : Type*} [Group L] [Group M] (H : Subgroup M)
    (e : L ≃* ↥H) (y : L) :
    Nat.card ↥(centralizer ({y} : Set L)) = Nat.card (centralizerIn H ((e y : ↥H) : M)) := by
  rw [card_centralizer_eq_of_mulEquiv e y, card_centralizer_subtype H (e y)]
  rfl

@[expose] noncomputable def centralizerSubtypeEquiv {M : Type*} [Group M] (H : Subgroup M) (x : ↥H) :
    ↥(centralizer ({x} : Set ↥H)) ≃* ↥(centralizerIn H (x : M)) :=
  (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      ext y
      simp only [Subgroup.mem_map, mem_centralizerIn, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, congrArg Subtype.val hz⟩
      · rintro ⟨hy, hc⟩
        exact ⟨⟨y, hy⟩, Subtype.ext hc, rfl⟩))

theorem isPerfect_centralizer_of_equiv {L M : Type*} [Group L] [Group M] (H : Subgroup M)
    (e : L ≃* ↥H) (y : L)
    (hperf : ⁅centralizerIn H ((e y : ↥H) : M), centralizerIn H ((e y : ↥H) : M)⁆ =
      centralizerIn H ((e y : ↥H) : M)) :
    Group.IsPerfect ↥(centralizer ({y} : Set L)) := by
  have h1 : Group.IsPerfect ↥(centralizerIn H ((e y : ↥H) : M)) := Subgroup.isPerfect_iff.2 hperf
  exact Group.IsPerfect.ofSurjective
    (f := ((centralizerEquiv e y (e y) rfl).trans (centralizerSubtypeEquiv H (e y))).symm.toMonoidHom)
    ((centralizerEquiv e y (e y) rfl).trans (centralizerSubtypeEquiv H (e y))).symm.surjective

theorem map_conj_centralizerIn {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H) (τ : M) :
    (centralizerIn H τ).map (MulAut.conj g).toMonoidHom = centralizerIn H (g * τ * g⁻¹) := by
  ext x
  simp only [Subgroup.mem_map, mem_centralizerIn, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨c, ⟨hc, hcτ⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hg hc) (H.inv_mem hg), ?_⟩
    calc g * c * g⁻¹ * (g * τ * g⁻¹) = g * (c * τ) * g⁻¹ := by group
      _ = g * (τ * c) * g⁻¹ := by rw [hcτ]
      _ = g * τ * g⁻¹ * (g * c * g⁻¹) := by group
  · rintro ⟨hx, hxc⟩
    refine ⟨g⁻¹ * x * g, ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩, by group⟩
    have h2 : x * (g * τ * g⁻¹) = (g * τ * g⁻¹) * x := hxc
    calc g⁻¹ * x * g * τ = g⁻¹ * (x * (g * τ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * τ * g⁻¹) * x) * g := by rw [h2]
      _ = τ * (g⁻¹ * x * g) := by group

theorem commutator_centralizerIn_conj {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H)
    {τ : M} (h : ⁅centralizerIn H τ, centralizerIn H τ⁆ = centralizerIn H τ) :
    ⁅centralizerIn H (g * τ * g⁻¹), centralizerIn H (g * τ * g⁻¹)⁆ =
      centralizerIn H (g * τ * g⁻¹) := by
  rw [← map_conj_centralizerIn hg τ, ← Subgroup.map_commutator, h]

@[expose] noncomputable def centralizerEquivConj {L M : Type*} [Group L] [Group M] (H : Subgroup M)
    (e : L ≃* ↥H) (y : L) {t g : M} (hg : g ∈ H) (hgt : ((e y : ↥H) : M) = g * t * g⁻¹) :
    ↥(centralizer ({y} : Set L)) ≃* ↥(centralizerIn H t) :=
  ((centralizerEquiv e y (e y) rfl).trans (centralizerSubtypeEquiv H (e y))).trans
    ((MulEquiv.subgroupCongr (by rw [hgt, ← map_conj_centralizerIn hg t])).trans
      (Subgroup.equivMapOfInjective (centralizerIn H t) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm)

end CFSG.GH74.GLS.IVK.GHInv
