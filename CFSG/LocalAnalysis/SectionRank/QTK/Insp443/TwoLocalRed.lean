module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin

variable {A : Type} [Group A] [Finite A]

theorem KConfig.le_and_normalizer_of_inner {L V MK Y : Subgroup A} (h : KConfig A L V MK)
    (hinner : ∀ σ : A ≃* A, ∃ x : A, σ = MulAut.conj x)
    (hN : Subgroup.normalizer (V : Set A) ≤ Y) (hQ : pCoreOf 2 Y ≠ ⊥) :
    L ≤ Y ∧ Y ≤ Subgroup.normalizer (L : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYM : Y ≤ MK := by
    refine (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y).trans
      (h.normalizer_le _ hQ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) fun σ hσV _ _ => ?_)
    obtain ⟨x, rfl⟩ := hinner σ
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
        (hN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hσV)))
  exact ⟨h.le_normalizer.trans hN, hYM.trans h.MK_le_normalizer⟩

theorem le_and_normalizer_of_map_conj {L X : Subgroup A} (x : A)
    (hLY : L ≤ X.map (MulAut.conj x).toMonoidHom)
    (hYL : X.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (L : Set A)) :
    L.map (MulAut.conj x⁻¹).toMonoidHom ≤ X ∧
      X ≤ Subgroup.normalizer ((L.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup A) : Set A) := by
  have hback : (X.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = X := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id X
    ext z
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  refine ⟨?_, ?_⟩
  · rw [← hback]
    exact Subgroup.map_mono hLY
  · rw [← hback, ← Subgroup.map_normalizer_eq_of_bijective L (MulAut.conj x⁻¹).bijective]
    exact Subgroup.map_mono hYL

theorem pCoreOf_map_conj_ne_bot {X : Subgroup A} (x : A) (hX : pCoreOf 2 X ≠ ⊥) :
    pCoreOf 2 (X.map (MulAut.conj x).toMonoidHom) ≠ ⊥ := by
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj x) X]
  intro hb
  exact hX ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj x).injective).mp hb)

end CFSG.SectionRank.QTK.Insp443
