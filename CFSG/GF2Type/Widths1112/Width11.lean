module

public import CFSG.GF2Type.Widths1112.Transport
public import CFSG.GF2Type.Widths1112.NotWeaklyClosed
public import CFSG.GF2Type.Widths1112.Co2Native
public import CFSG.GF2Type.Widths1112.Co2Ident
public import CFSG.GF2Type.Entry
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.L32NSp4Over

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.Blueprint CFSG.Open

namespace CFSG.GF2Type.Widths1112

theorem factorization_two_card_co2 :
    (Nat.card NativeSporadic.Co2).factorization 2 = 18 := by
  rw [CFSG.Sporadic.Co2.card_Co2,
    show (42305421312000 : ℕ) = 2 ^ 18 * 161382375 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem widthEleven_false (hU : Co2ModuleUniqueness)
    (hAS : S14.AschbacherSmith35Input)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G} (hchar : IsCharTwoType G)
    (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) = 2 ^ 23)
    {Mbar : Type} [Group Mbar]
    (hMbar : timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar)
    (hCo2 : Nonempty (Mbar ≃* NativeSporadic.Co2)) : False := by
  obtain ⟨hext', hcard'⟩ := CFSG.GF2Type.timmesfeld_hypotheses (w := 11) hext
    (by rw [hcard])
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← Bridge.generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have hw : (Setting.ofFStar z hz hext').width = 11 := Bridge.width_ofFStar hz hext' hcard'
  obtain ⟨e₁⟩ := Bridge.nonempty_mulEquiv_Mbar_ofFStar hz hext' hMbar'
  obtain ⟨e₂⟩ := hCo2
  generalize Setting.ofFStar z hz hext' = S at hw e₁
  have e : S.Mbar ≃* NativeSporadic.Co2 := e₁.trans e₂
  obtain ⟨ψ, hψ, hq⟩ := co2_ident hU S e hw
  have hMc : Nat.card S.Mbar = 42305421312000 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Co2.card_Co2]
  have hcardΓ : ¬ 2 ^ (2 * S.width - 2) ∣ Nat.card NativeSporadic.Co2 := by
    rw [hw, CFSG.Sporadic.Co2.card_Co2]
    norm_num
  have hGTS : GoodThroughSingular S :=
    goodThroughSingular_of_native S e.toEquiv ψ (fun A => co2Act A) hψ q₀₂ hq (co2Orbit 0)
      co2_hgood co2_hF3 hcardΓ
  have hf : (Nat.card S.Mbar).factorization 2 = 18 := by
    rw [hMc, ← CFSG.Sporadic.Co2.card_Co2]
    exact factorization_two_card_co2
  have h2 : (Nat.card S.Mbar).factorization 2 + 3 ≤ 2 * S.width := by omega
  have hnwc := exists_conj_mem_QG_of_card S hAS (by omega) (by omega)
    (by rw [hf, hw]; decide)
  exact false_of_goodThroughSingular S hchar (by omega) hGTS h2 hnwc

end CFSG.GF2Type.Widths1112
