module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Defs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module

section Transport
variable {U H : Type*} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup H] [Module (ZMod 2) H]

theorem commutatorSpace_congr (e : U ≃ₗ[ZMod 2] H) (g : LinearMap.GeneralLinearGroup (ZMod 2) U) :
    commutatorSpace (LinearMap.GeneralLinearGroup.congrLinearEquiv e g) =
      (commutatorSpace g).map (e : U →ₗ[ZMod 2] H) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨e.symm w + (g : U →ₗ[ZMod 2] U) (e.symm w), ⟨e.symm w, rfl⟩, ?_⟩
    simp [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
  · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
    refine ⟨e w, ?_⟩
    simp [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]

theorem isF2Transvection_congr (e : U ≃ₗ[ZMod 2] H) (g : LinearMap.GeneralLinearGroup (ZMod 2) U) :
    IsF2Transvection (LinearMap.GeneralLinearGroup.congrLinearEquiv e g) ↔ IsF2Transvection g := by
  unfold IsF2Transvection
  rw [commutatorSpace_congr, LinearEquiv.finrank_map_eq]
  have : LinearMap.GeneralLinearGroup.congrLinearEquiv e g ≠ 1 ↔ g ≠ 1 := by
    rw [Ne, Ne, ← map_one (LinearMap.GeneralLinearGroup.congrLinearEquiv e),
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e).injective.eq_iff]
  rw [this]
end Transport
section Transport2
variable {U H : Type*} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup H] [Module (ZMod 2) H]

theorem isElemAbelian_map_equiv {G G' : Type*} [Group G] [Group G'] (Φ : G ≃* G') {p : ℕ}
    {A : Subgroup G} (h : IsElemAbelian p A) : IsElemAbelian p (A.map Φ.toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map h _

theorem hasCentralizedConj_of_map (Φ : LinearMap.GeneralLinearGroup (ZMod 2) U ≃*
    LinearMap.GeneralLinearGroup (ZMod 2) H) {p : ℕ}
    {G A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)}
    {t : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (h : HasCentralizedConj p (G.map Φ.toMonoidHom) (A.map Φ.toMonoidHom) (Φ t)) :
    HasCentralizedConj p G A t := by
  obtain ⟨y', ⟨y, hyG, rfl⟩, E', hE'A, hcard, hcomm⟩ := h
  refine ⟨y, hyG, E'.comap Φ.toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, haA, hax⟩ := hE'A hx
    have : a = x := Φ.injective hax
    exact this ▸ haA
  · have h1 : Nat.card (E'.comap Φ.toMonoidHom) = Nat.card E' := by
      rw [show E'.comap Φ.toMonoidHom = E'.map Φ.symm.toMonoidHom from
        Subgroup.comap_equiv_eq_map_symm Φ E', Subgroup.card_map_of_injective Φ.symm.injective]
    rw [h1]
    rwa [Subgroup.card_map_of_injective Φ.injective] at hcard
  · intro e he
    apply Φ.injective
    have := hcomm (Φ e) he
    simpa [map_mul, map_inv] using this

theorem isMaxElemAbelianIn_map (Φ : LinearMap.GeneralLinearGroup (ZMod 2) U ≃*
    LinearMap.GeneralLinearGroup (ZMod 2) H) {p : ℕ}
    {G A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)}
    (h : IsMaxElemAbelianIn p G A) :
    IsMaxElemAbelianIn p (G.map Φ.toMonoidHom) (A.map Φ.toMonoidHom) := by
  obtain ⟨hAG, hel, hmax⟩ := h
  refine ⟨Subgroup.map_mono hAG, isElemAbelian_map_equiv Φ hel, ?_⟩
  intro A'' hA''G hA''el
  have h1 := hmax (A''.map Φ.symm.toMonoidHom) ?_ (isElemAbelian_map_equiv Φ.symm hA''el)
  · rw [Subgroup.card_map_of_injective Φ.symm.injective] at h1
    rwa [Subgroup.card_map_of_injective Φ.injective]
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg, hga⟩ := hA''G ha
    have : Φ.symm a = g := by rw [← hga]; simp
    simpa [this] using hg
end Transport2

end CFSG.HardMathSupport.Solomon.Coordinator
