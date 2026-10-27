module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888D3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma s888D4_qsub_eq_sSup (K₁ K₂ : Subgroup G) (h : G) :
    Qsub K₁ K₂ h = twoCoreIn (sSup (Gamma5 K₁ K₂ h)) := by
  rw [Qsub, Gamma5]
  congr 1
  simp only [sSup_insert, sSup_singleton, sSup_empty, sup_bot_eq]
  ac_rfl

theorem sec5_qsub_eq_of_gamma_eq {K₁ K₂ P₁ P₂ : Subgroup G} {h h' : G}
    (hΓ : Gamma5 P₁ P₂ h' = Gamma5 K₁ K₂ h) : Qsub P₁ P₂ h' = Qsub K₁ K₂ h := by
  rw [s888D4_qsub_eq_sSup P₁ P₂ h', s888D4_qsub_eq_sSup K₁ K₂ h, hΓ]

theorem asc82CHdLeN_of [Finite G] (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (h513 : Asc82Lemma513) (h514 : Asc82Lemma514) (h515c : Asc82Lemma515c) : Asc82CHdLeN := by
  intro G₀ _ _ t L S z r B A K₁ K₂ h c d hd
  obtain ⟨S', r', B', A', P₁, P₂, h', hc', hΓ⟩ :=
    h515c G₀ t L S z r B A K₁ K₂ h c d hd
  have h := sec5_cht_le_normalizer h37 h52a h513 h514 hc'
  rw [sec5_qsub_eq_of_gamma_eq hΓ] at h
  exact h

end CFSG.OddStandard.SmallF3.Omega
