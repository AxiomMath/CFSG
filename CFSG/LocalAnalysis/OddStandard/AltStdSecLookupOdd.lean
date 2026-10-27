module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG CFSG.ComponentClassification.CatLeaf CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_largeAlt_centralQuotient_of_oddLieType
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    {S : Type} [Group S] (hodd : OddLieType S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    ¬ IsLargeAlt (↥D ⧸ Subgroup.center ↥D) := by
  rintro ⟨m, hm, ⟨e⟩⟩
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hmod⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hmod σ hσ D hD with
    ⟨τ', n', f', hadm', hmod'⟩ | ⟨-, -, -, h8⟩
  · exact false_of_lieModel_alt hO hm e hadm' hmod'
  · have hadm8 : StatedLieAdmissible .PSL 2 2 3 := by
      refine ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩ <;> decide
    obtain ⟨-, hord, -⟩ := hO D .PSL 2 2 3 hadm8 h8
    have h1 : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
    have h2 : lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
    rw [h1, h2, mul_one] at hord
    have h3 := dvd_card_of_isLargeAlt (Y := ↥D ⧸ Subgroup.center ↥D) ⟨m, hm, ⟨e⟩⟩
    have hquot : Nat.card (↥D ⧸ Subgroup.center ↥D) ∣ Nat.card ↥D :=
      Subgroup.card_quotient_dvd_card (Subgroup.center ↥D)
    have h3D : 181440 ∣ Nat.card ↥D := h3.trans hquot
    rw [hord] at h3D
    exact absurd h3D (by norm_num)

theorem not_largeAlt_of_oddLieType (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) {S : Type} [Group S] (hodd : OddLieType S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {B : Subgroup (fixedSubgroup σ)} (hB : IsComponent B) :
    ¬ IsLargeAlt B := by
  rintro ⟨m, hm, ⟨e⟩⟩
  have hz : center B = ⊥ := center_eq_bot_of_alt (by omega) e
  let q : (B ⧸ center B) ≃* alternatingGroup (Fin m) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
  exact not_largeAlt_centralQuotient_of_oddLieType hGLS hO hodd hσ hB ⟨m, hm, ⟨q⟩⟩

end CFSG.OddStandard.AltStdSec
