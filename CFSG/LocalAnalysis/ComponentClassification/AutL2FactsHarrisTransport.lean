module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisBase
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsShape
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem harris_context {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfe : Even f) (h16 : 16 ∣ p ^ f - 1) (hY : Blueprint.LieModel Y .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Φ : MulAut Y ≃* PGammaL2 F),
      HarrisHyp F ∧ (HarrisLit.innAut Y).map Φ.toMonoidHom = pGammaL2PSLRange F ∧
      (∀ φ, HarrisLit.IsFieldAutPSL2 φ ↔ IsFieldInvModel (Φ φ)) ∧
      (∀ φ, HarrisLit.IsFieldAutPSL2Any φ ↔ IsFieldAutModel (Φ φ)) := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hH : HarrisHyp F := harrisHyp_of hp hp2 hF hfe h16
  have hY4 : ∃ y : Y, y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
    obtain ⟨y, hy4, hy2⟩ := exists_psl2_pow_four (F := F) (by have := hH.four_le; omega)
    refine ⟨e.symm y, by rw [← map_pow, hy4, map_one], fun h => hy2 ?_⟩
    rw [← map_pow] at h
    exact e.symm.injective (h.trans (map_one _).symm)
  exact ⟨F, inferInstance, inferInstance, autEquiv e, hH, map_autEquiv_innAut e,
    isFieldAutPSL2_iff hH.odd e hY4, isFieldAutPSL2Any_iff hH.odd e hY4⟩

theorem SylowShape.pullback {Y : Type} [Group Y] {F : Type} [Field F]
    (Φ : MulAut Y ≃* PGammaL2 F) (hI : (HarrisLit.innAut Y).map Φ.toMonoidHom = pGammaL2PSLRange F)
    (hFA : ∀ φ, HarrisLit.IsFieldAutPSL2 φ ↔ IsFieldInvModel (Φ φ))
    (hFAany : ∀ φ, HarrisLit.IsFieldAutPSL2Any φ ↔ IsFieldAutModel (Φ φ))
    {T : Subgroup (PGammaL2 F)} {v : PGammaL2 F}
    (h : SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel T v) :
    HarrisLit.SylowAutData (T.map Φ.symm.toMonoidHom) (Φ.symm v) := by
  rw [sylowAutData_iff_shape]
  refine h.map Φ.symm ?_ (fun x => ?_) (fun x => ?_)
  · rw [← hI, map_symm_map_mulEquiv]
  · rw [hFA, MulEquiv.apply_symm_apply]
  · rw [hFAany, MulEquiv.apply_symm_apply]

theorem SylowShape.pushforward {Y : Type} [Group Y] {F : Type} [Field F]
    (Φ : MulAut Y ≃* PGammaL2 F) (hI : (HarrisLit.innAut Y).map Φ.toMonoidHom = pGammaL2PSLRange F)
    (hFA : ∀ φ, HarrisLit.IsFieldAutPSL2 φ ↔ IsFieldInvModel (Φ φ))
    (hFAany : ∀ φ, HarrisLit.IsFieldAutPSL2Any φ ↔ IsFieldAutModel (Φ φ))
    {T : Subgroup (MulAut Y)} {v : MulAut Y} (h : HarrisLit.SylowAutData T v) :
    SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel (T.map Φ.toMonoidHom)
      (Φ v) :=
  ((sylowAutData_iff_shape T v).mp h).map Φ hI hFA hFAany

end CFSG.ComponentClassification.AutL2Facts
