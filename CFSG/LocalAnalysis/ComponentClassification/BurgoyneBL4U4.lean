module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDUc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSL4Lift

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.UnbalancingLocal
open scoped MatrixGroups

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem burgoynePropB_PSL4_uncond {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .PSL 4 p' f') :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ :=
  burgoynePropB_PSL4 K burgoynePropBSL4CoverInput CatFactsL4U4.BurgD.burgoynePropBSL4ExcInput hH
    hp2' hL

theorem burgoynePropB_PSU4_uncond {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .PSU 4 p' f') :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ :=
  burgoynePropB_PSU4 K burgoynePropBSU4CoverInput CatFactsL4U4.BurgD.burgoynePropBSU4ExcInput hH
    hp2' hL

end CFSG.ComponentClassification.Burgoyne.B
