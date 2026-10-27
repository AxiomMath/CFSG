module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

section Lemma8

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem isHzOne_normalizer_F4 (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    IsHzOne T L V₁ (Subgroup.normalizer (V₁ : Set G)) := by
  have hlOne : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  refine ⟨⟨sup_le (hlOne.trans inf_le_right) hV₁.2.2, fun hb => ?_⟩, le_rfl,
    lemma12_8_3_four_F4 h12213 h hV₁⟩
  have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 V₁ (IsPGroup.of_card hV₁.2.1)
  rw [hb, le_bot_iff] at h1
  have h2 := hV₁.2.1
  rw [h1, Subgroup.card_bot] at h2
  norm_num at h2

theorem Setting1282One.almostSpecial_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    AlmostSpecialHyp V V₁ L T (Subgroup.normalizer (V₁ : Set G)) :=
  lemma12_8_4_one_F4 h1222 hs.hyp hs.v1 (isHzOne_normalizer_F4 h12213 hs.hyp hs.v1)

theorem Setting1282One.le_centerOf_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    V₁ ≤ zU128 V V₁ := by
  have hA := hs.almostSpecial_F4 h1222 h12213
  refine le_inf (hs.v1.1.trans (le_conjClosure V _)) ?_
  exact (le_centralizer_normalizer_of_card_eq_two (by simpa using hs.v1.2.1)).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hA.conjClosure_le_N))

theorem display12_8_frattini_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
      Setting1282One G T L V n V₁ V₂ → frattiniOf (u128 V V₁) = V₁ := by
  intro G _ _ T L V n V₁ V₂ hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hs.almostSpecial_F4 h1222 h12213
  have : Fact (IsPGroup 2 ↥(u128 V V₁)) := ⟨hs.hyp.hyp.sylow.1.to_le hA.G22_three.1⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hs.exists_mul_ne
  have hc1 : x * y * x⁻¹ * y⁻¹ ≠ 1 := fun h => hxy (by
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h, one_mul])
  have hc : x * y * x⁻¹ * y⁻¹ ∈ frattiniOf (u128 V V₁) := by
    refine ⟨⁅(⟨x, hx⟩ : ↥(u128 V V₁)), ⟨y, hy⟩⁆, ?_, by simp [commutatorElement_def]⟩
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine Subgroup.subset_closure (Or.inl ?_)
    rw [SetLike.mem_coe, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine le_antisymm hA.G22_two ?_
  calc V₁ = Subgroup.zpowers (x * y * x⁻¹ * y⁻¹) :=
        (zpowers_eq_of_card_eq_two (by simpa using hs.v1.2.1) (hA.G22_two hc) hc1).symm
    _ ≤ frattiniOf (u128 V V₁) := Subgroup.zpowers_le.2 hc

theorem lemma12_8_8_one_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    ∃ U₀ : Subgroup G, U₀ ≤ u128 V V₁ ∧ CFSG.IsExtraspecialPGroup 2 ↥U₀ ∧
      frattiniOf U₀ = V₁ ∧ U₀ ⊔ zU128 V V₁ = u128 V V₁ := by
  have hA := hs.almostSpecial_F4 h1222 h12213
  have hZ := hs.le_centerOf_F4 h1222 h12213
  obtain ⟨U₀, hU₀U, hext, hΦ, hsup, -⟩ := exists_extraspecial_sup_centerOf
    (hs.hyp.hyp.sylow.1.to_le hA.G22_three.1) (hZ.trans inf_le_left)
    (by simpa using hs.v1.2.1) (hZ.trans inf_le_right)
    (fun x hx y hy => hA.G22_commutator_mem hx hy) (fun x hx => hA.G22_sq_mem hx)
    hs.exists_mul_ne
  exact ⟨U₀, hU₀U, hext, hΦ, hsup⟩

theorem lemma12_8_8_three_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    V ⊓ zU128 V V₁ = V₁ := by
  have hirr := irred_lOne_F4 h1222 hs.hyp hs.v1
  have hG₁Z : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    (le_normalizer_conjClosure V _).trans (normalizer_le_normalizer_centerOf _)
  rcases hirr.2.2.2 (V ⊓ zU128 V V₁) (le_inf hs.v1.1 (hs.le_centerOf_F4 h1222 h12213)) inf_le_left
    ((le_inf hirr.2.1 (hirr.2.2.1.trans hG₁Z)).trans Subgroup.inf_normalizer_le_normalizer_inf)
    with h | h
  · exact h
  · exfalso
    have hVZ : V ≤ zU128 V V₁ := inf_eq_left.1 h
    have hUZ : u128 V V₁ ≤ zU128 V V₁ := conjClosure_le fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.1 (hG₁Z hg) z).1 (hVZ hz)
    exact hs.nonabelian ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 (hUZ b.2).2 a a.2)⟩⟩

theorem lemma12_8_8_six_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    u128 V V₁ = conjClosure V₂ (Subgroup.normalizer (V₁ : Set G)) := by
  have hirr := irred_lOne_F4 h1222 hs.hyp hs.v1
  have hG₁U₂ := le_normalizer_conjClosure V₂ (Subgroup.normalizer (V₁ : Set G))
  refine le_antisymm ?_ (conjClosure_mono hs.v2.1 le_rfl)
  rcases hirr.2.2.2 (V ⊓ conjClosure V₂ (Subgroup.normalizer (V₁ : Set G)))
    (le_inf hs.v1.1 (hs.le.trans (le_conjClosure V₂ _))) inf_le_left
    ((le_inf hirr.2.1 (hirr.2.2.1.trans hG₁U₂)).trans Subgroup.inf_normalizer_le_normalizer_inf)
    with h | h
  · exfalso
    have h1 := Subgroup.card_le_of_le ((le_inf hs.v2.1 (le_conjClosure V₂ _)).trans h.le)
    rw [hs.v2.2.1, hs.v1.2.1] at h1
    norm_num at h1
  · have hVU₂ := inf_eq_left.1 h
    exact conjClosure_le fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.1 (hG₁U₂ hg) z).1 (hVU₂ hz)

@[expose] def Lemma12_8_8_five_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ →
      Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (lOne L V₁ : Set G) → n ≤ 3

theorem lemma12_8_8_n3_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 3 V₁ V₂) :
    (∃ U₀ : Subgroup G, U₀ ≤ u128 V V₁ ∧ CFSG.IsExtraspecialPGroup 2 ↥U₀ ∧
        frattiniOf U₀ = V₁ ∧ U₀ ⊔ zU128 V V₁ = u128 V V₁) ∧
      V ⊓ zU128 V V₁ = V₁ ∧
      (Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (lOne L V₁ : Set G) → 3 ≤ 3) ∧
      u128 V V₁ = conjClosure V₂ (Subgroup.normalizer (V₁ : Set G)) :=
  ⟨lemma12_8_8_one_F4 h1222 h12213 hs, lemma12_8_8_three_F4 h1222 h12213 hs, fun _ => le_rfl,
    lemma12_8_8_six_F4 h1222 hs⟩

end Lemma8

end CFSG.Quasithin.H13
