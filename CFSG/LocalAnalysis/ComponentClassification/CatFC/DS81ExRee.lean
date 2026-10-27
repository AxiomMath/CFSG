module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeClass
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
  CFSG.ComponentClassification.RankTwoExceptional.Exc

set_option linter.unusedSectionVars false


theorem ree_exists_order_eightynine_commute {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (h89 : 89 ∣ 2 ^ (2 * a + 1) - 1)
    (hz : centralZ K a 1 ∈ F4.reeGamma K a) (ht : sylowL a K 1 ∈ F4.reeGamma K a) :
    ∀ y ∈ ([⟨centralZ K a 1, hz⟩, ⟨sylowL a K 1, ht⟩] : List (F4.reeGamma K a)),
      ∃ w : F4.reeGamma K a, orderOf w = 89 ∧ Commute w y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcz, hct, -⟩ :=
    large_Ree_two_involution_centralizers a ha K hK
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  haveI : Finite (ModGL F4.tag K) := finite_modGL
  have key : ∀ (r : ModGL F4.tag K) (hr : r ∈ F4.reeGamma K a),
      89 ∣ Nat.card ↥(F4.reeGamma K a ⊓ Subgroup.centralizer {r}) →
      ∃ w : F4.reeGamma K a, orderOf w = 89 ∧ Commute w ⟨r, hr⟩ := by
    intro r hr hdvd
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(F4.reeGamma K a ⊓ Subgroup.centralizer {r})) 89 hdvd
    have hwΓ : (w : ModGL F4.tag K) ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 w.2).1
    have hwC : (w : ModGL F4.tag K) ∈ Subgroup.centralizer {r} := (Subgroup.mem_inf.1 w.2).2
    refine ⟨⟨w, hwΓ⟩, ?_, Subtype.ext ?_⟩
    · rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hw]
    · exact Subgroup.mem_centralizer_singleton_iff.1 hwC
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · refine key _ hz ?_
    rw [hcz]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h89 _) _
  · refine key _ ht ?_
    rw [hct]
    refine Dvd.dvd.mul_left ?_ _
    have : (2 ^ (2 * a + 1)) ^ 2 - 1 = (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) + 1) := by
      have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
      zify [h1, Nat.one_le_pow 2 (2 ^ (2 * a + 1)) (Nat.two_pow_pos _)]
      ring
    rw [this]
    exact Dvd.dvd.mul_right h89 _

theorem lie23To89At_twistedF4 : Lie23To89At .twistedF4 := by
  intro X _ _ n f hadm hM τ hτ h23
  have hn : n = 0 := hadm.2.2.1
  subst hn
  have h11 : 11 ∣ f := eleven_dvd_of_twentythree_dvd_card (by simp) hadm hM
    (dvd_trans h23 (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨-, hRM⟩ := hM.reeTitsModel (by decide)
  have hmodel := large_Ree_model_Schreier X 2 f hRM
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hRM
  haveI : CharP K F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hadm.2.1 hK
  have ha : 1 ≤ a := by
    have := hadm.2.2.2.2.2
    omega
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨E⟩ := hmodel.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hz : centralZ K a 1 ∈ F4.reeGamma K a := (zK_le ha hK') ((mem_zK hK').2 ⟨1, rfl⟩)
  have ht : sylowL a K 1 ∈ F4.reeGamma K a := (tK_le ha hK') ((mem_tK hK').2 ⟨1, rfl⟩)
  have h89 : 89 ∣ 2 ^ (2 * a + 1) - 1 := by
    rw [← hfa]
    exact (eightynine_dvd_two_pow_sub_one_iff f).2 h11
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  exact prime_dvd_card_centralizer_of_classesCover E (classesCover_ree ha hK' hz ht)
    (ree_exists_order_eightynine_commute ha hK' h89 hz ht) hτ

end CFSG.ComponentClassification.CatFC.DS81.Ex
