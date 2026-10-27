module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsLie
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroBlock

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactLieOutNorm : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p.Coprime (Nat.card J) →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ∈ Subgroup.normalizer (J : Set Y) → x ^ p = 1 →
      x ∉ L ⊔ Subgroup.centralizer (L : Set Y) →
      ¬ (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) ∧
      ((∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
        ∃ D : Subgroup Y, D ≤ L ∧ D ≠ ⊥ ∧ ⁅D, D⁆ = D ∧ D ≤ Subgroup.centralizer ({x} : Set Y))

@[expose] def KFactLieOutAltParabolic : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    ∀ p : ℕ, (p = 5 ∨ p = 7) → IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
    IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    PerfectSectionsAltSq p J → ∀ x ∈ Subgroup.normalizer (L : Set Y), x ^ p = 1 →
    x ∉ L ⊔ Subgroup.centralizer (L : Set Y) →
    (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) → p.Coprime (Nat.card J)

theorem kFactLieOutNorm_of_lieOut (h : KFactLieOutPrime) : KFactLieOutNorm := by
  intro Y _ _ L J hL hcl hpar hne p hp hp5 hpJ x hx _ hxp hxo
  rcases h Y L hL hcl p hp hp5 x hx hxp hxo with hd | ⟨hf, hD⟩
  · obtain ⟨-, T, hT, hNT⟩ := hpar
    have h1 := (hd T hT).trans (Subgroup.card_dvd_of_le hNT)
    exact absurd (Nat.Coprime.eq_one_of_dvd hpJ h1) hp.one_lt.ne'
  · exact ⟨fun hfix => hne (hf J hpar hfix), fun hnB => hD ⟨J, hpar, hne, hnB⟩⟩

theorem kFactLieOutAltParabolic_of (hO : KFactLieOutPrime) (hD : KFactLieOutDiagLevi) :
    KFactLieOutAltParabolic := by
  intro Y _ _ L J hL p hp hcl hpar hne hnB hJ x hx hxp hxo hfix
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  exfalso
  rcases hO Y L hL hcl p hpp hp5 x hx hxp hxo with hd | ⟨hf, -⟩
  · obtain ⟨X, hXJ, hXq, hpX, hno⟩ := hD Y L J hL hcl hpar hne hnB p hp x hx hxp hxo hd hfix
    obtain ⟨φ, hφ⟩ := exists_hom_alternating_of_altSq hJ hXJ hXq hpX hpp
    exact hno φ hφ
  · exact hne (hf J hpar hfix)

theorem kFactBlockAutPrimeInnerN_of (hO : KFactLieOutNorm) (hOP : KFactBlockOutPrime) :
    KFactBlockAutPrimeInner := by
  intro Y _ _ L J hL p hp hp5 hpL htype x hx hxJ hxp hfix
  rcases htype with hOA | hOA | ⟨hcl, hpar, hne⟩
  · exact hOP Y L hL p hp hp5 (Or.inl hOA) x hx hxp
  · exact hOP Y L hL p hp hp5 (Or.inr hOA) x hx hxp
  · by_contra hxo
    have hpJ : p.Coprime (Nat.card J) := (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
      hpL (h.trans (Subgroup.card_dvd_of_le hpar.1))
    exact (hO Y L J hL hcl hpar hne p hp hp5 hpJ x hx hxJ hxp hxo).1 hfix

theorem kFactBlockOuterPerfectCentN_of (hO : KFactLieOutNorm) : KFactBlockOuterPerfectCent := by
  intro Y _ _ L J hL hcl hpar hne hnB p hp hp5 hpJ x hx hxJ hxp hxo
  exact (hO Y L J hL hcl hpar hne p hp hp5 hpJ x hx hxJ hxp hxo).2 hnB

theorem kFactBlockAutAltInnerN_of (hO : KFactLieOutNorm) (hA : KFactLieOutAltParabolic) :
    KFactBlockAutAltInner := by
  intro Y _ _ L J hL p hp hcl hpar hne hnB hJ x hx hxJ hxp hfix
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  by_contra hxo
  have hpJ := hA Y L J hL p hp hcl hpar hne hnB hJ x hx hxp hxo hfix
  exact (hO Y L J hL hcl hpar hne p hpp hp5 hpJ x hx hxJ hxp hxo).1 hfix

end CFSG.AGLEmbedding
