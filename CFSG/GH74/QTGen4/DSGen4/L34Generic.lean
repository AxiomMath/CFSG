module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpBorel
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem natCard_gf4 : Nat.card (GaloisField 2 2) = 4 :=
  (GaloisField.card 2 2 (by norm_num)).trans (by norm_num)

theorem isYAmalgamPair_of_borelData {M : Type} [Group M] {U R₁ R₂ : Subgroup M}
    (h : CFSG.QuasithinUnique.Borel252.BorelData M U R₁ R₂)
    (hO2 : ∀ P : Subgroup M, P.Normal → IsPGroup 2 P → P = ⊥) :
    IsYAmalgamPair U (Subgroup.normalizer (R₁ : Set M)) (Subgroup.normalizer (R₂ : Set M)) := by
  refine ⟨h.sylow, h.ne_norm, fun X => ⟨fun hX => ?_, fun hX => ?_⟩⟩
  · obtain ⟨hMax, hUX⟩ := hX
    obtain ⟨⟨P, hPne, hPp, hXP⟩, hmax⟩ := hMax
    by_cases hXtop : X = ⊤
    ·
      exfalso
      exact hPne (hO2 P (Subgroup.normalizer_eq_top_iff.mp (hXP.symm.trans hXtop)) hPp)
    by_cases hXU : X = Subgroup.normalizer (U : Set M)
    ·
      exfalso
      have hXle : X ≤ Subgroup.normalizer (R₁ : Set M) := by
        rw [hXU]
        exact h.lt₁.le
      have hR₁ : CFSG.Open.IsTwoLocal (Subgroup.normalizer (R₁ : Set M)) :=
        ⟨R₁, h.ne_bot₁, h.isPGroup₁, rfl⟩
      exact h.lt₁.ne (hXU.symm.trans (hmax _ hR₁ hXle).symm)
    ·
      exact h.only X (lt_of_le_of_ne hUX (Ne.symm hXU)) (lt_top_iff_ne_top.mpr hXtop)
  · rcases hX with rfl | rfl
    · exact ⟨h.isMaximalTwoLocal₁ hO2, h.lt₁.le⟩
    · exact ⟨h.isMaximalTwoLocal₂ hO2, h.lt₂.le⟩

theorem isLieOverTwo_psl3_four :
    IsLieOverTwo .PSL 3 2 (projectiveSL 3 (GaloisField 2 2)) := by
  refine (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).2 ?_
  exact ⟨CFSG.ComponentClassification.PSL3Four.admissible, GaloisField 2 2, inferInstance,
    inferInstance, natCard_gf4.trans (by norm_num),
    ⟨CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 (GaloisField 2 2)⟩⟩

end CFSG.GH74.QTGen4.DSGen4.L34
