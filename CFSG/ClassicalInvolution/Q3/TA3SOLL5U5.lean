module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDefs
public import CFSG.ClassicalInvolution.Q3.TA3SOLL5U5Uni
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQuot

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
open scoped MatrixGroups

section Pair

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {t : X}

theorem datum_not_fourGenerated_of_sl2_pair (hD : TightDatum R S t) {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) {H₁ H₂ : Subgroup X}
    (h₁ : H₁ ≤ Subgroup.centralizer ({t} : Set X)) (h₂ : H₂ ≤ Subgroup.centralizer ({t} : Set X))
    (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) (e₁ : H₁ ≃* SL(2, F)) (e₂ : H₂ ≃* SL(2, F)) :
    ¬ TwoSubgroupsFourGenerated X := by
  have : Group.IsPerfect H₁ := isPerfect_of_equiv_sl2 h4 e₁
  have : Group.IsPerfect H₂ := isPerfect_of_equiv_sl2 h4 e₂
  obtain ⟨φ₁, hi₁, hr₁, -⟩ := exists_q8_of_mulEquiv_sl2 hodd H₁ e₁
  obtain ⟨φ₂, hi₂, hr₂, -⟩ := exists_q8_of_mulEquiv_sl2 hodd H₂ e₂
  exact datum_not_fourGenerated hD h₁ h₂ hcomm φ₁ φ₂ hi₁ hi₂ hr₁ hr₂

end Pair

theorem noDatumL5U5_holds : NoDatumL5U5 := by
  intro X _ _ _ p f hp hp2 h5 hm hF ⟨R, S, t, hD⟩
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  rcases hm with ⟨-, hm⟩ | ⟨-, hm⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    have hoddK : Odd (Nat.card K) := by rw [hK]; exact hodd
    obtain ⟨H₁, H₂, h₁, h₂, hc, ⟨e₁⟩, ⟨e₂⟩⟩ := exists_sl2_pair_of_psl5 hoddK e hD.order
    exact datum_not_fourGenerated_of_sl2_pair hD hoddK (by rw [hK]; omega) h₁ h₂ hc e₁ e₂ hF
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := ClassicalGroups.Unitary.charP_of_card_sq hK
    obtain ⟨H₁, H₂, h₁, h₂, hc, ⟨e₁⟩, ⟨e₂⟩⟩ := exists_sl2_pair_of_psu5 hK hp2 h5 e hD.order
    have hq := card_fixedSubfield hK
    exact datum_not_fourGenerated_of_sl2_pair hD (by rw [hq]; exact hodd) (by rw [hq]; omega)
      h₁ h₂ hc e₁ e₂ hF

end CFSG.ClassicalInvolution.Q3.TA3
