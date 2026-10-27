module

public import CFSG.GF2Type.Widths1112.Transport
public import CFSG.GF2Type.Widths1112.NotWeaklyClosed
public import CFSG.GF2Type.Widths1112.Co1Native
public import CFSG.GF2Type.Widths1112.Co1Ident
public import CFSG.GF2Type.Entry
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32NSp4Over

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.Blueprint CFSG.Open

namespace CFSG.GF2Type.Widths1112

theorem factorization_two_card_co1 :
    (Nat.card NativeSporadic.Co1).factorization 2 = 21 := by
  rw [CFSG.Sporadic.Co1.card_Co1,
    show (4157776806543360000 : ℕ) = 2 ^ 21 * 1982582476875 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def co1ActFun (A : NativeSporadic.Co1) : Module.End (ZMod 2) (Fin 24 → ZMod 2) :=
  Matrix.mulVecLin (A.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2))

theorem widthTwelve_false
    (hAS : S14.AschbacherSmith35Input)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G} (hchar : IsCharTwoType G)
    (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) = 2 ^ 25)
    {Mbar : Type} [Group Mbar]
    (hMbar : timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar)
    (hCo1 : Nonempty (Mbar ≃* NativeSporadic.Co1)) : False := by
  obtain ⟨hext', hcard'⟩ := CFSG.GF2Type.timmesfeld_hypotheses (w := 12) hext
    (by rw [hcard])
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← Bridge.generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have hw : (Setting.ofFStar z hz hext').width = 12 := Bridge.width_ofFStar hz hext' hcard'
  obtain ⟨e₁⟩ := Bridge.nonempty_mulEquiv_Mbar_ofFStar hz hext' hMbar'
  obtain ⟨e₂⟩ := hCo1
  generalize Setting.ofFStar z hz hext' = S at hw e₁
  have e : S.Mbar ≃* NativeSporadic.Co1 := e₁.trans e₂
  obtain ⟨ψ, hψ, hq⟩ := co1_ident S e hw
  have hMc : Nat.card S.Mbar = 4157776806543360000 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Co1.card_Co1]
  have hcardΓ : ¬ 2 ^ (2 * S.width - 2) ∣ Nat.card NativeSporadic.Co1 := by
    rw [hw, CFSG.Sporadic.Co1.card_Co1]
    norm_num
  have hGTS : GoodThroughSingular S :=
    goodThroughSingular_of_native S e.toEquiv ψ co1ActFun hψ CFSG.Sporadic.Co1.Module.q₀ hq
      (CFSG.Monster.GMS.co1Orbit 0) co1_hgood co1_hF3 hcardΓ
  have hf : (Nat.card S.Mbar).factorization 2 = 21 := by
    rw [hMc, ← CFSG.Sporadic.Co1.card_Co1]
    exact factorization_two_card_co1
  have h2 : (Nat.card S.Mbar).factorization 2 + 3 ≤ 2 * S.width := by omega
  have hnwc := exists_conj_mem_QG_of_card S hAS (by omega) (by omega)
    (by rw [hf, hw]; decide)
  exact false_of_goodThroughSingular S hchar (by omega) hGTS h2 hnwc

end CFSG.GF2Type.Widths1112
