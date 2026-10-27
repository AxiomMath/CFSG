module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenHe
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenHeE8
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenZShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenPair
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenQ
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveGen

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Dickson.I271.TabMFive
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (orderOf_dG orderOf_zG orderOf_tG
  isTwoBCentralizer_tG centralizer_pow_eq_of_prime)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus (monsterSevenClasses)
open CFSG.Monster.Generated (Gmat)
open CFSG.AGLEmbedding.Norton.MON5_7 (dG zG tG)

section SevenA


variable {G : Type} [Group G] [Finite G]

theorem tabMSeven_sevenA_facts (hE8 : HePE8)
    (hcls : ∀ t : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder ∨
        Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder)
    (h2A : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        1128960)
    (h2B : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        150528)
    (hG5 : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = twoBCentralizerOrder)
    {k : G} (hk : orderOf k = 7) {H : Subgroup G}
    (hHk : H ≤ Subgroup.centralizer ({k} : Set G)) (e : ↥H ≃* ↥CFSG.Sporadic.HeldB.heP) :
    Nat.card ↥(Subgroup.centralizer ({k} : Set G)) = 7 * 4030387200 ∧
      (∃ t : G, orderOf t = 2 ∧ t * k = k * t ∧
        Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder) ∧
      (∃ u : G, orderOf u = 2 ∧ u * k = k * u ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = twoBCentralizerOrder ∧
        35280 < Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓
          Subgroup.centralizer ({k} : Set G))) ∧
      (∀ u : G, orderOf u = 2 → u * k = k * u →
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = twoBCentralizerOrder →
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓
          Subgroup.centralizer ({k} : Set G)) = 150528) := by
  have hHI : HeInvolutions H := HeInvolutions.of_equiv hE8 e
  have hKH : ∀ g ∈ Subgroup.zpowers k, g ∈ H → g = 1 := fun _ hg hgH =>
    eq_one_of_mem_zpowers_of_center hHk (center_eq_bot_of_equiv_heP e) hg hgH
  have hkC : k ∈ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hcomm : ∀ t ∈ H, t * k = k * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.1 (hHk ht)
  have hlow : ∀ t ∈ H, 7 * Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) :=
    fun t ht => mul_card_le_cent_inf' hk hHk hKH ht
  have hup := centSevenA_of_bounds hE8 hcls h2A h2B hG5 hk hHk e
  have hge := mul_card_le_of_prod' hk hKH hkC hHk
  rw [hHI.card] at hge
  have hcard : Nat.card ↥(Subgroup.centralizer ({k} : Set G)) = 7 * 4030387200 :=
    le_antisymm hup hge
  have hrep := eq_prod_of_card_le' hk hKH hkC hHk (by rw [hcard, hHI.card])
  refine ⟨hcard, ?_, ?_, ?_⟩
  ·
    obtain ⟨t, htH, hto, htc⟩ := hHI.exists_A
    refine ⟨t, hto, hcomm t htH, ?_⟩
    rcases hcls t hto with hA | hB
    · exact hA
    · exfalso
      have h1 := hlow t htH
      have h2 := h2B t k hto hB hk (hcomm t htH)
      rw [htc] at h1
      omega
  ·
    obtain ⟨A, hAc, hAs, hA8, hAH⟩ := hHI.exists_E8
    obtain ⟨u, huA, huo, huc⟩ := hG5 A hAc hAs hA8
    have huH : u ∈ H := hAH huA
    refine ⟨u, huo, hcomm u huH, huc, ?_⟩
    have h1 := hlow u huH
    rcases hHI.cases u huH huo with h | h <;> rw [h] at h1 <;> omega
  · intro u huo huk huc
    have huC : u ∈ Subgroup.centralizer ({k} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 huk
    obtain ⟨i, x, hx, hu⟩ := hrep u huC
    have huH : u ∈ H := mem_of_orderOf_two' (by norm_num) (by norm_num) hk hKH (hHk := hHk)
      ⟨(i : ℤ), x, hx, by rw [hu, zpow_natCast]⟩ huo
    have h1 := hlow u huH
    have h2 := h2B u k huo huc hk huk
    rcases hHI.cases u huH huo with h | h <;> rw [h] at h1 <;> omega

end SevenA

section Gmat


theorem mSevenShapeGmat_of_sevenB
    (hOut : SporadicOuterLeTwo)
    (h7B : ∃ z f : Gmat, orderOf z = 7 ∧ orderOf f = 5 ∧ z * f = f * z ∧ z * tG = tG * z ∧
      f * tG = tG * f ∧ ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({z} : Set Gmat) ∧
        Nonempty (↥S ≃* QuaternionGroup 4)) :
    MSevenShapeGmat := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨hcls, h2A, h2B, hG5⟩ := gmat_seven_bounds
  obtain ⟨hHk, ⟨e⟩⟩ := tabMSeven_he_le_cent_dG
  have hE8 : HePE8 := hePE8
  have hdG : ShapeRkAt' 7 (GoodSpor 7 [.He]) (RkSpor 7 [.He]) dG :=
    (tabMSeven_shape_and_bound_of_heP hOut hE8 hcls h2A h2B hG5 orderOf_dG hHk e).1
  obtain ⟨hcard, htA, huB, h2Bd⟩ :=
    tabMSeven_sevenA_facts hE8 hcls h2A h2B hG5 orderOf_dG hHk e
  have hzd : ∀ (g : Gmat) (m : ℕ), g * zG * g⁻¹ ≠ dG ^ m := by
    intro g m h
    by_cases hm : dG ^ m = 1
    · rw [hm] at h
      apply CFSG.AGLEmbedding.Norton.MON5_7.zG_ne_one
      have h' := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using h'
    · have h1 : Nat.card ↥(Subgroup.centralizer ({zG} : Set Gmat)) = 7 * 4030387200 := by
        haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        rw [← card_centralizer_conj g zG, h, centralizer_pow_eq_of_prime orderOf_dG hm, hcard]
      have h6 := seven_pow_dvd_card_cent_zG
      rw [h1] at h6
      norm_num at h6
  have hQ : ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({zG} : Set Gmat) ∧
      Nonempty (↥S ≃* QuaternionGroup 4) := by
    obtain ⟨z, f, hz, hf, hzf, hzt, hft, S, hSz, ⟨eS⟩⟩ := h7B
    rcases monsterSevenClasses z hz with h | h
    ·
      exfalso
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      have huo : orderOf (c * tG * c⁻¹) = 2 := by rw [orderOf_conj_eq, orderOf_tG]
      have hud : c * tG * c⁻¹ * dG = dG * (c * tG * c⁻¹) := by
        rw [← hc]
        exact Commute.conj hzt.symm c
      have huc : Nat.card ↥(Subgroup.centralizer ({c * tG * c⁻¹} : Set Gmat)) =
          twoBCentralizerOrder := by
        rw [card_centralizer_conj]
        exact isTwoBCentralizer_tG.2.2.2.2.1
      have hf' : c * f * c⁻¹ ∈ Subgroup.centralizer ({c * tG * c⁻¹} : Set Gmat) ⊓
          Subgroup.centralizer ({dG} : Set Gmat) := by
        refine ⟨Subgroup.mem_centralizer_singleton_iff.2 (Commute.conj hft c),
          Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        rw [← hc]
        exact Commute.conj hzf.symm c
      have h5 := Subgroup.orderOf_dvd_natCard _ hf'
      rw [h2Bd _ huo hud huc, orderOf_conj_eq, hf] at h5
      norm_num at h5
    ·
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine ⟨S.map (MulAut.conj c).toMonoidHom, ?_,
        ⟨(S.equivMapOfInjective _ (MulAut.conj c).injective).symm.trans eS⟩⟩
      rintro _ ⟨s, hs, rfl⟩
      have hsz := Subgroup.mem_centralizer_singleton_iff.1 (hSz hs)
      rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ← hc]
      exact Commute.conj hsz c
  have hzG : ShapeRkAt' 7 (GoodSpor 7 [.He]) (RkSpor 7 [.He]) zG :=
    tabMSeven_shape_of_not_conj_dG orderOf_zG hzd htA huB hQ
  intro k hk1 hk7
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hk : orderOf k = 7 := orderOf_eq_prime hk7 hk1
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → GoodSpor 7 [.He] T →
      GoodSpor 7 [.He] T' := fun _ _ _ _ f h => GoodSpor.of_equiv f h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → RkSpor 7 [.He] T →
      RkSpor 7 [.He] T' := fun _ _ _ _ f h => RkSpor.of_equiv f h
  rcases monsterSevenClasses k hk with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hkc : k = c⁻¹ * dG * c⁻¹⁻¹ := by rw [← hc]; group
    rw [hkc]
    exact shapeRkAt'_conj (by norm_num) hGood hRk c⁻¹ dG hdG
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hkc : k = c⁻¹ * zG * c⁻¹⁻¹ := by rw [← hc]; group
    rw [hkc]
    exact shapeRkAt'_conj (by norm_num) hGood hRk c⁻¹ zG hzG

section Final


theorem mSevenShapeGmat
    (hOut : SporadicOuterLeTwo) : MSevenShapeGmat :=
  mSevenShapeGmat_of_sevenB hOut tabMSeven_sevenB_data

end Final

end Gmat

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
