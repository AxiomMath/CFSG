module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166E7Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R16ExcLabel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.SeitzReduction.EPilot CFSG.StandardType CFSG.StandardType.TableBExc


theorem i166On_famE7_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J)
    (hD6 : ∀ n : ℕ, 2 ≤ n → LayerData166At ⟨.D, 6, n⟩) :
    I166On i166FamE7 := by
  intro K _ _ lab p hK hfam hp hp2 hns he hr
  obtain ⟨ht, hn, hpD⟩ := hfam
  have hZ : Subgroup.center K = ⊥ :=
    rk2_center_eq_bot_of_large hK (Or.inr (Or.inr (Or.inr (Or.inl ht)))) hn
  obtain ⟨F, hField, hFinite, hCard, ⟨e⟩⟩ :=
    exists_mulEquiv_adjointGroup_E7_of_hasLabel hK ht hZ
  letI : Field F := hField
  letI : Finite F := hFinite
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hCard
  letI : CharP F 2 := hchar
  have hmodel := concl166S_E7_model_of_layerData (F := F) hn hCard hp hp2 hpD (hD6 lab.n hn)
  exact htr e hmodel

end CFSG.LocalAnalysis.GLTheoremA.Y10F
