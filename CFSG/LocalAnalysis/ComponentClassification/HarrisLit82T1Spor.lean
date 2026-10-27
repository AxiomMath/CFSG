module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporDataA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporDataB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporDataC

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint Assembly.LowTwoRank


theorem sporT1Data_of (s : TauCeti.SporadicName) (hs : s ≠ .M11) : SporT1Data s := by
  cases s with
  | M11 => exact absurd rfl hs
  | M12 => exact sporT1Data_M12
  | M22 => exact sporT1Data_M22
  | M23 => exact sporT1Data_M23
  | M24 => exact sporT1Data_M24
  | J1 => exact sporT1Data_J1
  | J2 => exact sporT1Data_J2
  | J3 => exact sporT1Data_J3
  | J4 => exact sporT1Data_J4
  | HS => exact sporT1Data_HS
  | McL => exact sporT1Data_McL
  | He => exact sporT1Data_He
  | Ru => exact sporT1Data_Ru
  | Suz => exact sporT1Data_Suz
  | ONan => exact sporT1Data_ONan
  | Co1 => exact sporT1Data_Co1
  | Co2 => exact sporT1Data_Co2
  | Co3 => exact sporT1Data_Co3
  | Fi22 => exact sporT1Data_Fi22
  | Fi23 => exact sporT1Data_Fi23
  | Fi24Prime => exact sporT1Data_Fi24Prime
  | HN => exact sporT1Data_HN
  | Ly => exact sporT1Data_Ly
  | Th => exact sporT1Data_Th
  | B => exact sporT1Data_B
  | M => exact sporT1Data_M

theorem rowCore_spor_perfect :
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
      (NativeSporadic.SporadicRep S ∧ ¬ Nonempty (S ≃* ↥NativeSporadic.M11)) →
      ∀ t : S, orderOf t = 2 → ∀ J : Subgroup S, J ≤ centralizer {t} →
      (J.subgroupOf (centralizer {t})).IsSubnormal → t ∈ J →
      ¬ (IsTwoQuasisimple ↥J ∧ ∃ (L : Type) (_ : Group L) (_ : Finite L), IsMTypeSchur p L ∧
          (∃ f : ℕ, 1 ≤ f ∧
            (IsCoverOf .POmegaOdd 3 p f 2 (L ⧸ pPrimeCore 2 L) ∨
              IsCoverOf .PSL 4 p f (Nat.gcd 4 (p ^ f - 1)) (L ⧸ pPrimeCore 2 L) ∨
              IsCoverOf .PSU 4 p f (Nat.gcd 4 (p ^ f + 1)) (L ⧸ pPrimeCore 2 L) ∨
              IsCoverOf .PSp 2 p f 2 (L ⧸ pPrimeCore 2 L) ∨
              (Even f ∧ IsSLTwoOver (p ^ f) (L ⧸ pPrimeCore 2 L)))) ∧
          Nonempty (L ⧸ Open.fusionZStar L ≃* ↥J ⧸ Open.fusionZStar ↥J)) := by
  rintro S _ _ _ hna p hp hp2 ⟨⟨s, ⟨e⟩⟩, hM11⟩ t ht J hJC hJs htJ ⟨hJq, L, _, _, -, hLI, ⟨eL⟩⟩
  have hs : s ≠ .M11 := by
    rintro rfl
    exact hM11 ⟨e⟩
  have hd := sporT1Data_of s hs
  exact false_of_perfect (hd.oddCore S hna e t ht) hJC hJs htJ hJq hp hp2 hLI eL
    (hd.comps S hna e t ht)

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
