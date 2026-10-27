module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.RankOneSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SLTwoDatum
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Phase2Inputs
public import CFSG.Holt.General.Simple
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

private theorem ordA_one_le_252_of_odd_le_seven {q : ℕ} (hq : Odd q) (hq7 : q ≤ 7) :
    CFSG.Open.ordA 1 q ≤ 252 := by
  have h1 : 1 ≤ q := by
    obtain ⟨k, hk⟩ := hq
    omega
  interval_cases q <;> decide

theorem centralDatum_of_pRank_le_one (hGr : TBLit.GriessMultipliersOdd) (hD : DihedralStd)
    {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K) (hO : oddCore K = ⊥)
    (hbig : 20160 ≤ Nat.card (K ⧸ center K)) (h1 : CFSG.pRank 2 K ≤ 1) : CentralDatum K := by
  haveI : IsSimpleGroup (K ⧸ center K) := hK.2.1
  haveI : Finite (K ⧸ center K) :=
    Finite.of_surjective (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective (center K))
  have hnonab : ∃ a b : K ⧸ center K, a * b ≠ b * a := hK.2.2
  have hev : Even (Nat.card K) := by
    have hbar : Even (Nat.card (K ⧸ center K)) :=
      CFSG.Holt.General.even_card_of_isSimpleGroup hnonab
    exact even_iff_two_dvd.mpr
      ((even_iff_two_dvd.mp hbar).trans (Subgroup.card_quotient_dvd_card (center K)))
  obtain ⟨hZne, n, hn2, P, heP⟩ := rankOne_sylow_dihedral hK hO hev h1
  rcases hD (K ⧸ center K) hnonab P n hn2 heP with
    ⟨p, f, hp, hp2, hf, hmodel⟩ | ⟨ealt⟩
  ·
    have hm : LieModel (K ⧸ center K) .PSL 2 p f := Or.inl ⟨by decide, hmodel⟩
    have hcard : Nat.card (K ⧸ center K) = CFSG.Open.ordA 1 (p ^ f) :=
      GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hm
    have hO2 : CFSG.pPrimeCore 2 K = ⊥ := by
      rw [← oddCore_eq_pPrimeCore_two K]
      exact hO
    have h2 : IsPGroup 2 ↥(center K) := Sol78.center_isPGroup_two hO2
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hqodd : Odd (p ^ f) := hpodd.pow
    have h9 : 9 ≤ p ^ f := by
      by_contra hcon
      have hle : p ^ f ≤ 8 := by omega
      have hle7 : p ^ f ≤ 7 := by
        obtain ⟨k, hk⟩ := hqodd
        omega
      have hbound : CFSG.Open.ordA 1 (p ^ f) ≤ 252 :=
        ordA_one_le_252_of_odd_le_seven hqodd hle7
      have hbig' : 20160 ≤ CFSG.Open.ordA 1 (p ^ f) := by
        simpa [hcard] using hbig
      omega
    exact centralDatum_of_psl_two hGr hK h2 hZne hp hp2 h9 hm
  ·
    exfalso
    obtain ⟨e⟩ := ealt
    have hcard7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hle : Nat.card (K ⧸ center K) ≤ 2520 := by
      rw [Nat.card_congr e.toEquiv, hcard7]
    omega

end CFSG.OddStandard.SmallF3.HypA2
