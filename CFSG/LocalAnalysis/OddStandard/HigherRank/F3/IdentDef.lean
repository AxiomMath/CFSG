module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentTable
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

theorem exists_deficiency (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] (hK2 : IsTwoQuasisimple K)
    (hKchev : IsSimpleChevalleyOver 3 (K ⧸ fusionZStar K)) (hnot : ¬ IsMTypeSchur 3 K)
    (hev : Even (Nat.card ↥(fusionZStar K))) :
    (∀ x y : griessHopfMultiplier ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)),
        orderOf x = 2 → orderOf y = 2 → x = y) ∧
      ordProj[2] (Nat.card ↥(center (K ⧸ pPrimeCore 2 K))) ≠
        ordProj[2] (Nat.card (griessHopfMultiplier
          ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : ¬ (∀ n r : ℕ, 0 < n → 0 < r →
      (Blueprint.LieModel (K ⧸ fusionZStar K) .PSL (2 * n) 3 r ∨
        Blueprint.LieModel (K ⧸ fusionZStar K) .PSU (2 * n) 3 r) →
      ordProj[2] (Nat.card ↥(fusionZStar K)) =
        ordProj[2] (Nat.card (griessHopfMultiplier (K ⧸ fusionZStar K)))) :=
    fun h => hnot (Or.inl ⟨hK2, hKchev, hev, h⟩)
  rw [not_forall] at hD
  obtain ⟨n, hD⟩ := hD
  rw [not_forall] at hD
  obtain ⟨r, hD⟩ := hD
  rw [not_imp] at hD
  obtain ⟨hn, hD⟩ := hD
  rw [not_imp] at hD
  obtain ⟨hr, hD⟩ := hD
  rw [not_imp] at hD
  obtain ⟨hmod, hne⟩ := hD
  have hker : ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 K)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  have hO : Open.fusionZStar (K ⧸ pPrimeCore 2 K) = center (K ⧸ pPrimeCore 2 K) :=
    fusionZStar_eq_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨eZ⟩ := ComponentClassification.GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective
    (QuotientGroup.mk' (pPrimeCore 2 K)) (QuotientGroup.mk'_surjective _) hker
  have e : K ⧸ Open.fusionZStar K ≃*
      (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K) :=
    eZ.trans (QuotientGroup.quotientMulEquivOfEq hO)
  have hM : Nat.card (griessHopfMultiplier (K ⧸ Open.fusionZStar K)) =
      Nat.card (griessHopfMultiplier
        ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K))) :=
    Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv
  have hcard : Nat.card ↥(fusionZStar K) =
      Nat.card ((QuotientGroup.mk' (pPrimeCore 2 K)).ker) *
        Nat.card ↥(center (K ⧸ pPrimeCore 2 K)) := by
    have h := card_fusionZStar_of_surjective (QuotientGroup.mk' (pPrimeCore 2 K))
      (QuotientGroup.mk'_surjective _) hker
    rwa [hO] at h
  have hZeq : ordProj[2] (Nat.card ↥(fusionZStar K)) =
      ordProj[2] (Nat.card ↥(center (K ⧸ pPrimeCore 2 K))) := by
    rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  refine ⟨?_, ?_⟩
  · rcases hmod with hPSL | hPSU
    · exact unique_involution_of_psl_psu (τ := .PSL) hGA (Or.inl rfl) hn
        (ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv e hPSL)
    · exact unique_involution_of_psl_psu (τ := .PSU) hGA (Or.inr rfl) hn
        (ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv e hPSU)
  · intro h
    apply hne
    calc ordProj[2] (Nat.card ↥(fusionZStar K))
        = ordProj[2] (Nat.card ↥(center (K ⧸ pPrimeCore 2 K))) := hZeq
      _ = ordProj[2] (Nat.card (griessHopfMultiplier
            ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)))) := h
      _ = ordProj[2] (Nat.card (griessHopfMultiplier (K ⧸ Open.fusionZStar K))) :=
            (congrArg (fun m => ordProj[2] m) hM).symm

end CFSG.OddStandard.HigherRank.F3.Ident
