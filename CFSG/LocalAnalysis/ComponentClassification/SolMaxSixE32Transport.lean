module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitInputs
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

private theorem map_conj_centralizer_singleton (y t : X) :
    (centralizer ({t} : Set X)).map (MulAut.conj y).toMonoidHom =
      centralizer ({y * t * y⁻¹} : Set X) := by
  ext z
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (MulAut.conj y) h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
    simpa [MulAut.conj_apply] using h'
  · intro h
    apply (MulAut.conj y).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    simpa [MulAut.conj_apply] using h

theorem not_isConj_of_isEmpty {t z : X} {J : Subgroup X}
    (hJ : SolAltLit.IsAltTwoComponent t J 9)
    (h : ∀ K : Subgroup X, K ≤ centralizer ({z} : Set X) →
      IsPComponent 2 (K.subgroupOf (centralizer ({z} : Set X))) →
        IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) :
    ∀ y : X, y * t * y⁻¹ ≠ z := by
  intro y hy
  subst hy
  obtain ⟨-, hJle, hJcomp, ⟨e⟩⟩ := hJ
  have hinj : Function.Injective (MulAut.conj y).toMonoidHom := (MulAut.conj y).injective
  have hcent := map_conj_centralizer_singleton y t
  have hKle : J.map (MulAut.conj y).toMonoidHom ≤ centralizer ({y * t * y⁻¹} : Set X) := by
    rw [← hcent]
    exact Subgroup.map_mono hJle
  have hKcomp : IsPComponent 2
      ((J.map (MulAut.conj y).toMonoidHom).subgroupOf (centralizer ({y * t * y⁻¹} : Set X))) := by
    let φ : ↥(centralizer ({t} : Set X)) ≃*
        ↥((centralizer ({t} : Set X)).map (MulAut.conj y).toMonoidHom) :=
      (centralizer ({t} : Set X)).equivMapOfInjective _ hinj
    have key : (J.subgroupOf (centralizer ({t} : Set X))).map φ.toMonoidHom =
        (J.map (MulAut.conj y).toMonoidHom).subgroupOf
          ((centralizer ({t} : Set X)).map (MulAut.conj y).toMonoidHom) := by
      ext ⟨x, hx⟩
      rw [mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨⟨c, hc⟩, hcA, hceq⟩
        exact ⟨c, hcA, congrArg Subtype.val hceq⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hJle hm⟩, hm, rfl⟩
    have := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 φ hJcomp
    rw [key, hcent] at this
    exact this
  let ψ : ↥J ≃* ↥(J.map (MulAut.conj y).toMonoidHom) := J.equivMapOfInjective _ hinj
  exact (h _ hKle hKcomp).false
    ((QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)).symm.trans e)

end CFSG.ComponentClassification.SolMax.Sig36.E32
