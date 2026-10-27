module

public import CFSG.LargeExtraspecial.S3bTen
public import CFSG.CGT.Timmesfeld75.Main

public section

namespace CFSG.LargeExtraspecial.TI75

open CFSG.CGT.Timmesfeld75 Subgroup

universe u

section Transfer

variable {Y X : Type*} [Group Y] [Group X]

theorem comap_conjSubgroup (e : Y ≃* X) (g : Y) (A : Subgroup X) :
    (conjSubgroup (e g) A).comap (e : Y →* X) = conjSubgroup g (A.comap (e : Y →* X)) := by
  ext y
  simp only [mem_comap, mem_conjSubgroup, MonoidHom.coe_ofClass, map_mul, map_inv]

theorem eq_bot_of_pCore_eq_bot (e : Y ≃* X) (hO2 : CFSG.pCore 2 X = ⊥) (N : Subgroup Y)
    (hN : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have hle : N.map (e : Y →* X) ≤ CFSG.pCore 2 X :=
    le_sSup ⟨hN.map _ e.surjective, hN2.map _⟩
  rw [hO2, le_bot_iff] at hle
  exact (map_eq_bot_iff_of_injective N e.injective).mp hle

end Transfer

theorem weaklyClosedTITransitive_of_transitivityTI (h : TimmesfeldTransitivityTI) :
    WeaklyClosedTITransitive.{u} := by
  intro X _ _ A hcomm hsq hTI hwc hO2 x hx hx1 y hy hy1
  set e : Shrink.{0} X ≃* X := Shrink.mulEquiv with he
  set A' : Subgroup (Shrink.{0} X) := A.comap (e : Shrink.{0} X →* X) with hA'
  have hel : CFSG.Open.IsElemAbelian 2 A' :=
    ⟨⟨⟨fun a b => Subtype.ext (e.injective (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcomm _ a.2 _ b.2))⟩⟩,
     fun a ha => e.injective (by rw [map_pow, map_one]; exact hsq _ ha)⟩
  have hTI' : ∀ g : Shrink.{0} X,
      A' ⊓ conjSubgroup g⁻¹ A' = ⊥ ∨ A' ⊓ conjSubgroup g⁻¹ A' = A' := by
    intro g
    rw [← comap_conjSubgroup, hA', ← comap_inf]
    rcases hTI (e g⁻¹) with h1 | h1
    · right
      change (A ⊓ A.map (MulAut.conj (e g⁻¹)).toMonoidHom).comap _ = _
      rw [h1, inf_idem]
    · left
      change (A ⊓ A.map (MulAut.conj (e g⁻¹)).toMonoidHom).comap _ = _
      rw [h1, MonoidHom.comap_bot]
      exact (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have hnorm : normalizer (A' : Set (Shrink.{0} X)) =
      (normalizer (A : Set X)).comap (e : Shrink.{0} X →* X) :=
    (comap_normalizer_eq_of_surjective A e.surjective).symm
  have hWC' : ∀ g : Shrink.{0} X, conjSubgroup g⁻¹ A' ≤ normalizer (A' : Set _) →
      conjSubgroup g⁻¹ A' = A' := by
    intro g hg
    rw [← comap_conjSubgroup, hnorm, comap_le_comap_of_surjective e.surjective] at hg
    have h1 : conjSubgroup (e g⁻¹) A = A := hwc (e g⁻¹) hg
    rw [← comap_conjSubgroup, h1]
  have hmem : ∀ z : X, z ∈ A → e.symm z ∈ A' := fun z hz => by
    rw [hA', mem_comap, MonoidHom.coe_ofClass, MulEquiv.apply_symm_apply]
    exact hz
  have hne : ∀ z : X, z ≠ 1 → e.symm z ≠ 1 := fun z hz h1 =>
    hz (by rw [← e.apply_symm_apply z, h1, map_one])
  obtain ⟨n, hn, hnxy⟩ := h (Shrink.{0} X) A' hel hTI' hWC' (eq_bot_of_pCore_eq_bot e hO2)
    (e.symm x) (hmem x hx) (hne x hx1) (e.symm y) (hmem y hy) (hne y hy1)
  refine ⟨e n, ?_, ?_⟩
  · rw [hnorm, mem_comap] at hn
    exact hn
  · have h1 := congrArg e hnxy
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

theorem weaklyClosedTITransitive_of_inputs (hS : SimpleCaseStmt) (h215 : Lemma215Stmt) :
    WeaklyClosedTITransitive.{u} :=
  weaklyClosedTITransitive_of_transitivityTI (timmesfeldTransitivityTI_of_inputs hS h215)

end CFSG.LargeExtraspecial.TI75
