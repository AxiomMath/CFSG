module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4Large
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P5StepB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Fix
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Glue
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4H2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4I
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Rank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

theorem noE9Z4LargeBig_of_parts_F4 (h35 : Lemma1435) (h5 : Stage1461Five) (h2 : Stage1461Two)
    (hN1 : E9Fstar) (hN2 : E9Normalizer) (hcab : GoldschmidtCentralAbelianBound)
    (h9 : Stage1469W) (h105 : Stage14610FiveW_F4) (h1 : Stage1463One) (h2' : Stage1463Two)
    (h3 : Stage1463Three) (h4 : Stage1463Four) : NoE9Z4LargeBig_F4 := by
  intro G _ _ T M S H PQ p hred hmax hshape hlt _
  have hTH : T ≤ H := hred.isHTM.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hTcard : Nat.card T = 4 * Nat.card (pCoreOf 2 H) := by
    have := Subgroup.relIndex_mul_card (pCoreOf 2 H) T
    rw [inf_eq_left.mpr hTsyl.pCoreOf_le, hshape.2] at this
    exact this.symm
  have hT : 2 ^ 11 < Nat.card T := by
    rw [hTcard]
    have : 2 ^ 11 = 4 * 2 ^ 9 := by norm_num
    omega
  obtain ⟨R₁, R₂, s, hdat⟩ := exists_isE9Dat h35 S hred hshape
  obtain ⟨u, hu, huZ, huT⟩ := e9z4_exists_fixed h35 S hred hshape hdat
  obtain ⟨hA, hB, hC, hD⟩ := e9z4_H₂ h35 h2 S hred hshape hdat hu huZ huT
  have hF := hN1 G T M S H PQ p hred hmax hshape
  have h16 := hN2 G T M S H PQ p hred hmax hshape R₁ R₂ s hdat
  exact stepB_E9_F4 hcab h9 h105 h1 h2' h3 h4 S ⟨H, u, R₂ ⊔ (T ⊓ Subgroup.normalizer (R₁ : Set G)),
    hred.isHTM, e9z4_isInvU h35 h5 S hred hmax hshape hdat hF h16 (Or.inl hu) huZ huT,
    e9z4_isI h35 h5 h2 h4 S hred hmax hshape hdat hF h16 (Or.inl hu) huZ huT, hT,
    e9z4_rank h35 h5 S hred hshape, hA, hB, hC, hD,
    e9z4_card_conjClosure_H₂ h35 S hred hshape hdat⟩

end CFSG.Quasithin
