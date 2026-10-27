module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix

open CFSG.ClassicalInvolution.Upgrade (map_closure_preserving statedQuadMinus_comp)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)

theorem map_glCongr_orthogonalMinus {F F' : Type} [Field F] [Field F'] (φ : F ≃+* F') (m : ℕ)
    {b c : F} {b' c' : F'} (hb : φ b = b') (hc : φ c = c') :
    Subgroup.map (glCongr (ι := Fin m ⊕ Fin m ⊕ Fin 2) φ).toMonoidHom
      (CFSG.PGLModel.orthogonalMinus m F b c) = CFSG.PGLModel.orthogonalMinus m F' b' c' := by
  simpa [CFSG.PGLModel.orthogonalMinus, CFSG.PGLModel.orthogonalGroup,
    CFSG.MatrixModel.isometryCore] using
    map_closure_preserving (ι := Fin m ⊕ Fin m ⊕ Fin 2)
      (QK := CFSG.PGLModel.minusQuadForm m b c)
      (QL := CFSG.PGLModel.minusQuadForm m b' c') φ (by
        subst hb hc
        intro v
        change CFSG.Open.StatedQuadMinus (m + 1) F' (φ b) (φ c) (φ ∘ v) =
          φ (CFSG.Open.StatedQuadMinus (m + 1) F b c v)
        exact statedQuadMinus_comp (K := F) (L := F') φ (n := m + 1) (b := b) (c := c)
          rfl rfl v)

@[expose] noncomputable def orthogonalMinusCongr {F F' : Type} [Field F] [Field F']
    (φ : F ≃+* F') (m : ℕ) {b c : F} {b' c' : F'} (hb : φ b = b') (hc : φ c = c') :
    ↥(CFSG.PGLModel.orthogonalMinus m F b c) ≃*
      ↥(CFSG.PGLModel.orthogonalMinus m F' b' c') :=
  ((CFSG.PGLModel.orthogonalMinus m F b c).equivMapOfInjective
    (glCongr φ).toMonoidHom (glCongr φ).injective).trans
    (MulEquiv.subgroupCongr (map_glCongr_orthogonalMinus φ m hb hc))

end CFSG.ClassicalGroups.Orthogonal
