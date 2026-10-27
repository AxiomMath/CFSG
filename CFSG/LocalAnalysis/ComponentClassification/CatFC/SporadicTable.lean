module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableRu
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableMonster
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableFi
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableCo
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableHN
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableSuzON
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableHeLy
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableMcL
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableHS

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Rows


theorem sporadic_comp_rows {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow s (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow s (Nat.card (D ⧸ center D))) := by
  cases s
  case M11 => exact sporadic_rows_m11 hS hna e hσ hD
  case M12 => exact sporadic_rows_m12 hS hna e hσ hD
  case M22 => exact sporadic_rows_m22 hS hna e hσ hD
  case M23 => exact sporadic_rows_m23 hS hna e hσ hD
  case M24 => exact sporadic_rows_m24 hS hna e hσ hD
  case J1 => exact sporadic_rows_j1 hS hna e hσ hD
  case J2 => exact sporadic_rows_j2 hS hna e hσ hD
  case J3 => exact sporadic_rows_j3 hS hna e hσ hD
  case J4 => exact sporadic_rows_j4 hS hna e hσ hD
  case HS => exact sporadic_rows_hs hS hna e hσ hD
  case McL => exact sporadic_rows_mcl hS hna e hσ hD
  case He => exact sporadic_rows_he hS hna e hσ hD
  case Ru => exact sporadic_rows_ru hS hna e hσ hD
  case Suz => exact sporadic_rows_suz hS hna e hσ hD
  case ONan => exact sporadic_rows_onan hS hna e hσ hD
  case Co1 => exact sporadic_rows_co1 hS hna e hσ hD
  case Co2 => exact sporadic_rows_co2 hS hna e hσ hD
  case Co3 => exact sporadic_rows_co3 hS hna e hσ hD
  case Fi22 => exact sporadic_rows_fi22 hS hna e hσ hD
  case Fi23 => exact sporadic_rows_fi23 hS hna e hσ hD
  case Fi24Prime => exact sporadic_rows_fi24 hS hna e hσ hD
  case HN => exact sporadic_rows_hn hS hna e hσ hD
  case Ly => exact sporadic_rows_ly hS hna e hσ hD
  case Th => exact sporadic_rows_th hS hna e hσ hD
  case B => exact sporadic_rows_b hS hna e hσ hD
  case M => exact sporadic_rows_m hS hna e hσ hD

end Rows

section Order


theorem sporadic_comp_order (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {s : TauCeti.SporadicName} (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) ∣ AGLEmbedding.sporOrd s ∧
      (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow s (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow s (Nat.card (D ⧸ center D))) :=
  ⟨card_quotient_center_dvd_sporOrd hMcard e D, (sporadic_comp_rows hS hna e hσ hD).1,
    (sporadic_comp_rows hS hna e hσ hD).2⟩

end Order

end CFSG.ComponentClassification.CatFC
