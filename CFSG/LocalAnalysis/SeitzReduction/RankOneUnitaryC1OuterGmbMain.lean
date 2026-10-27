module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmgLayer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmbEven
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmbOdd

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open scoped MatrixGroups

theorem psl2BorelInput_holds : PSL2BorelInput := by
  intro X _ _ K p n _ hpn hK Q hQ E hEK hEN hE
  obtain ⟨e⟩ := hK
  have hn : n ≠ 0 := by
    rintro rfl
    rcases hpn with ⟨-, hn⟩ | ⟨-, h3 | h5⟩
    · omega
    · simp at h3
    · simp at h5
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  have hΓ : ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ), GmbProp Γ ∧ Nonempty (K ≃* Γ) := by
    rcases hpn with ⟨rfl, hn2⟩ | ⟨-, h8⟩
    · refine ⟨SL(2, GaloisField 2 n), inferInstance, inferInstance,
        gmbProp_sl2_charTwo ?_, ⟨e.trans gmbPSL2EquivSL2⟩⟩
      rw [hcard]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    · exact ⟨PSL(2, GaloisField p n), inferInstance, inferInstance,
        gmbProp_psl2_odd (by rw [hcard]; exact h8), ⟨e⟩⟩
  obtain ⟨Γ, _, _, hΓ, ⟨e'⟩⟩ := hΓ
  obtain ⟨H, hEH, hHK, hH⟩ := gmb_transport hΓ e' hQ hEK hEN hE
  exact ⟨H, hEH, hHK, hH.le_normalizer, hH.odd_card, hH.comm, hH.fixed, hH.irred⟩

end CFSG.SeitzReduction.RankOne
