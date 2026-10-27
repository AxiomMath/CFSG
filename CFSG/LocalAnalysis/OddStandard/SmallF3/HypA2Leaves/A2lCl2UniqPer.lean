module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqUpA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqUpB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDownA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDownB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDAA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDAB

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

theorem cl24_ppd_le {τ : StatedLieTag} {n j k ℓ : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hℓ : ℓ.Prime) (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i)
    (hd : ℓ ∣ lieOrderCofactor τ n (3 ^ j)) : k ≤ j * cl24E τ n := by
  cases τ
  case PSL => exact cl24_ppd_le_PSL hadm hℓ hk hd
  case PSU => exact cl24_ppd_le_PSU hadm hℓ hk hd
  case PSp => exact cl24_ppd_le_PSp hadm hℓ hk hd
  case POmegaOdd => exact cl24_ppd_le_POmegaOdd hadm hℓ hk hd
  case POmegaPlus => exact cl24_ppd_le_POmegaPlus hadm hℓ hk hd
  case POmegaMinus => exact cl24_ppd_le_POmegaMinus hadm hℓ hk hd
  case G2 => exact cl24_ppd_le_G2 hadm hℓ hk hd
  case F4 => exact cl24_ppd_le_F4 hadm hℓ hk hd
  case E6 => exact cl24_ppd_le_E6 hadm hℓ hk hd
  case E7 => exact cl24_ppd_le_E7 hadm hℓ hk hd
  case E8 => exact cl24_ppd_le_E8 hadm hℓ hk hd
  case twistedE6 => exact cl24_ppd_le_twistedE6 hadm hℓ hk hd
  case trialityD4 => exact cl24_ppd_le_trialityD4 hadm hℓ hk hd
  case twistedG2 => exact cl24_ppd_le_twistedG2 hadm hℓ hk hd
  all_goals exact absurd hadm.2.2.2.1 (by norm_num)

theorem cl24_ppd_dvd {τ : StatedLieTag} {n j k ℓ : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hℓ : ℓ.Prime) (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E τ n) :
    ℓ ∣ lieOrderCofactor τ n (3 ^ j) := by
  cases τ
  case PSL => exact cl24_ppd_dvd_PSL hadm hℓ hk hke
  case PSU => exact cl24_ppd_dvd_PSU hadm hℓ hk hke
  case PSp => exact cl24_ppd_dvd_PSp hadm hℓ hk hke
  case POmegaOdd => exact cl24_ppd_dvd_POmegaOdd hadm hℓ hk hke
  case POmegaPlus => exact cl24_ppd_dvd_POmegaPlus hadm hℓ hk hke
  case POmegaMinus => exact cl24_ppd_dvd_POmegaMinus hadm hℓ hk hke
  case G2 => exact cl24_ppd_dvd_G2 hadm hℓ hk hke
  case F4 => exact cl24_ppd_dvd_F4 hadm hℓ hk hke
  case E6 => exact cl24_ppd_dvd_E6 hadm hℓ hk hke
  case E7 => exact cl24_ppd_dvd_E7 hadm hℓ hk hke
  case E8 => exact cl24_ppd_dvd_E8 hadm hℓ hk hke
  case twistedE6 => exact cl24_ppd_dvd_twistedE6 hadm hℓ hk hke
  case trialityD4 => exact cl24_ppd_dvd_trialityD4 hadm hℓ hk hke
  case twistedG2 => exact cl24_ppd_dvd_twistedG2 hadm hℓ hk hke
  all_goals exact absurd hadm.2.2.2.1 (by norm_num)

theorem cl24_cofMod {τ : StatedLieTag} {n j : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hτ : τ ≠ .twistedG2) : Cl24CofMod (lieOrderCofactor τ n (3 ^ j)) j := by
  cases τ
  case PSL => exact cl24_cofMod_PSL hadm
  case PSU => exact cl24_cofMod_PSU hadm
  case PSp => exact cl24_cofMod_PSp hadm
  case POmegaOdd => exact cl24_cofMod_POmegaOdd hadm
  case POmegaPlus => exact cl24_cofMod_POmegaPlus hadm
  case POmegaMinus => exact cl24_cofMod_POmegaMinus hadm
  case G2 => exact cl24_cofMod_G2 hadm
  case F4 => exact cl24_cofMod_F4 hadm
  case E6 => exact cl24_cofMod_E6 hadm
  case E7 => exact cl24_cofMod_E7 hadm
  case E8 => exact cl24_cofMod_E8 hadm
  case twistedE6 => exact cl24_cofMod_twistedE6 hadm
  case trialityD4 => exact cl24_cofMod_trialityD4 hadm
  case twistedG2 => exact absurd rfl hτ
  all_goals exact absurd hadm.2.2.2.1 (by norm_num)

theorem cl24_cls {τ : StatedLieTag} {n j : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hτ : τ ≠ .twistedG2) :
    (τ = .PSL ∨ τ = .PSU ∨ τ = .PSp ∨ τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus) ∨
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨
        τ = .trialityD4) := by
  cases τ
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · exact absurd rfl hτ
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · exact absurd hadm.2.2.2.1 (by norm_num)

end CFSG.OddStandard.SmallF3.HypA2Leaves
