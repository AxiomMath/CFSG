module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthSmall
public import CFSG.ClassicalInvolution.SmallOrth.PlusFourMain

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small

theorem orthSmallLayer :
    ∀ (F W : Type) [Field F] [Finite F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (Q : QuadraticForm F W), (polarBilin Q).Nondegenerate → Odd (Nat.card F) →
      5 ≤ Nat.card F → 3 ≤ Module.finrank F W → Module.finrank F W ≤ 6 →
      GeneratedByQuasisimple Q := by
  intro F W _ _ _ _ _ Q hQ hodd h5 h3 h6
  by_cases hplus : Module.finrank F W = 4 ∧ ∃ P P' : HypPair Q, P.Orth P'
  · obtain ⟨hdim, P, P', h⟩ := hplus
    obtain ⟨H₁, H₂, hH₁, hH₂, hq₁, hq₂, hgen, hn₁, hn₂⟩ :=
      exists_quasisimple_pair_of_plus_four h hdim (by omega) hQ
    refine ⟨{H₁, H₂}, ?_, ?_⟩
    · rintro H (rfl | rfl)
      · exact ⟨hH₁, hq₁, hn₁⟩
      · exact ⟨hH₂, hq₂, hn₂⟩
    · refine hgen.trans (sup_le ?_ ?_)
      · exact le_iSup₂_of_le H₁ (by simp) le_rfl
      · exact le_iSup₂_of_le H₂ (by simp) le_rfl
  · have hne : Module.finrank F W ≠ 4 ∨ ∀ P P' : HypPair Q, ¬ P.Orth P' := by
      by_contra! hcon
      exact hplus ⟨hcon.1, by simpa using hcon.2⟩
    have hq := isQuasisimple_elementaryGroup_small hodd h5 hQ h3 hne
    refine ⟨{elementaryGroup Q}, ?_, ?_⟩
    · rintro H rfl
      exact ⟨le_rfl, hq, fun g hg x hx => mul_mem (mul_mem hg hx) (inv_mem hg)⟩
    · exact le_iSup₂_of_le (elementaryGroup Q) (by simp) le_rfl

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
