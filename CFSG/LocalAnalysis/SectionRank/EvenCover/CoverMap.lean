module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

namespace CFSG.SectionRank.EvenCover

open Subgroup
open scoped commutatorElement

theorem eq_top_of_forall_mul_center {L : Type*} [Group L] [Group.IsPerfect L] {M : Subgroup L}
    (h : ∀ x : L, ∃ a ∈ M, a⁻¹ * x ∈ center L) : M = ⊤ := by
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := L), _root_.commutator_def,
    commutator_le]
  intro x _ y _
  obtain ⟨a, ha, hax⟩ := h x
  obtain ⟨b, hb, hby⟩ := h y
  set z := a⁻¹ * x with hz
  set z' := b⁻¹ * y with hz'
  have hx : x = a * z := by rw [hz]; group
  have hy : y = b * z' := by rw [hz']; group
  have e : ⁅x, y⁆ = ⁅a, b⁆ := by
    rw [hx, hy, commutatorElement_def, commutatorElement_def]
    have h1 := mem_center_iff.1 hax
    have h2 := mem_center_iff.1 hby
    calc a * z * (b * z') * (a * z)⁻¹ * (b * z')⁻¹
        = a * (z * b) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by group
      _ = a * (b * z) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [h1 b]
      _ = a * b * (z * z' * z⁻¹) * a⁻¹ * z'⁻¹ * b⁻¹ := by group
      _ = a * b * (z' * z * z⁻¹) * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [(h2 z).symm]
      _ = a * b * (z' * a⁻¹) * z'⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * z') * z'⁻¹ * b⁻¹ := by rw [h2 a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [e, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

@[expose] def centralQuotientMap {H L : Type*} [Group H] [Group L] {D : Subgroup H} [D.Normal]
    (e : L ⧸ center L ≃* H ⧸ D) : L →* H ⧸ D :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center L))

theorem centralQuotientMap_surjective {H L : Type*} [Group H] [Group L] {D : Subgroup H}
    [D.Normal] (e : L ⧸ center L ≃* H ⧸ D) : Function.Surjective (centralQuotientMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_centralQuotientMap {H L : Type*} [Group H] [Group L] {D : Subgroup H} [D.Normal]
    (e : L ⧸ center L ≃* H ⧸ D) : (centralQuotientMap e).ker = center L := by
  ext x
  rw [MonoidHom.mem_ker, centralQuotientMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem perfect_cover_map_of_section {H L : Type*} [Group H] [Group L] [Group.IsPerfect L]
    {D : Subgroup H} [D.Normal] (e : L ⧸ center L ≃* H ⧸ D)
    (σ : H →* pullback (centralQuotientMap e) (QuotientGroup.mk' D))
    (hσ : ∀ g, pullbackFst _ _ (σ g) = g) :
    ∃ φ : H →* L, Function.Surjective φ ∧ φ.ker ≤ D ∧ D.map φ = center L := by
  set φ : H →* L := (MonoidHom.snd H L).comp
    ((pullback (centralQuotientMap e) (QuotientGroup.mk' D)).subtype.comp σ) with hφ
  have hfφ : (centralQuotientMap e).comp φ = QuotientGroup.mk' D := comp_snd_section σ hσ
  have hfφ' : ∀ h, centralQuotientMap e (φ h) = (h : H ⧸ D) := fun h => congrArg (· h) hfφ
  have hker := ker_centralQuotientMap e
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    refine eq_top_of_forall_mul_center fun x => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective D (centralQuotientMap e x)
    refine ⟨φ h, ⟨h, rfl⟩, ?_⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hfφ', ← hh, QuotientGroup.mk'_apply,
      inv_mul_cancel]
  refine ⟨φ, hsurj, fun h hh => ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hh
    have := hfφ' h
    rw [hh, map_one] at this
    exact (QuotientGroup.eq_one_iff h).1 this.symm
  · ext z
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [← hker, MonoidHom.mem_ker, hfφ', (QuotientGroup.eq_one_iff h).2 hh]
    · intro hz
      obtain ⟨h, rfl⟩ := hsurj z
      refine ⟨h, ?_, rfl⟩
      rw [← hker, MonoidHom.mem_ker, hfφ'] at hz
      exact (QuotientGroup.eq_one_iff h).1 hz

theorem pullbackFst_centralQuotientMap {H L : Type*} [Group H] [Group L] [Finite L]
    {D : Subgroup H} [D.Normal] (e : L ⧸ center L ≃* H ⧸ D) :
    Function.Surjective (pullbackFst (centralQuotientMap e) (QuotientGroup.mk' D)) ∧
      (pullbackFst (centralQuotientMap e) (QuotientGroup.mk' D)).ker ≤
        center (pullback (centralQuotientMap e) (QuotientGroup.mk' D)) ∧
      Nat.card (pullbackFst (centralQuotientMap e) (QuotientGroup.mk' D)).ker ∣
        Nat.card (center L) := by
  refine ⟨pullbackFst_surjective (centralQuotientMap_surjective e) _,
    pullbackFst_ker_le_center (ker_centralQuotientMap e).le _, ?_⟩
  have h := card_pullbackFst_ker_dvd (centralQuotientMap e) (QuotientGroup.mk' D)
  rwa [ker_centralQuotientMap e] at h

end CFSG.SectionRank.EvenCover
