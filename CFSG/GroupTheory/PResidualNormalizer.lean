module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

theorem pResidual_characteristic (p : ℕ) (X : Type*) [Group X] :
    (pResidual p X).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  refine le_iInf fun N => le_iInf fun hN => le_iInf fun hprop => ?_
  have hN' : ((N.comap φ.toMonoidHom : Subgroup X)).Normal := inferInstance
  have hprop' : ∀ x : X, ∃ k : ℕ, x ^ p ^ k ∈ N.comap φ.toMonoidHom := by
    intro x
    obtain ⟨k, hk⟩ := hprop (φ x)
    exact ⟨k, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩
  calc (pResidual p X).map φ.toMonoidHom
      ≤ (N.comap φ.toMonoidHom).map φ.toMonoidHom :=
        Subgroup.map_mono (pResidual_le (N := N.comap φ.toMonoidHom) hprop')
    _ ≤ N := Subgroup.map_comap_le φ.toMonoidHom N

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_pResidualOf (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (pResidualOf p X : Set G) := by
  intro g hg
  have hXmap : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  let φ : ↥X ≃* ↥X :=
    (MulEquiv.subgroupMap (MulAut.conj g) X).trans (MulEquiv.subgroupCongr hXmap)
  have hφ : (pResidual p ↥X).map φ.toMonoidHom = pResidual p ↥X :=
    Subgroup.characteristic_iff_map_eq.mp (pResidual_characteristic p ↥X) φ
  have hcomp : (MulAut.conj g).toMonoidHom.comp X.subtype = X.subtype.comp φ.toMonoidHom := by
    ext x
    rfl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (pResidualOf p X).map (MulAut.conj g).toMonoidHom = pResidualOf p X
  rw [pResidualOf, Subgroup.map_map, hcomp, ← Subgroup.map_map, hφ]

end CFSG.Quasithin

end
