module

public import CFSG.GH74.GLS.C3.Layer1.EvenSelFin

public section

namespace CFSG.GH74.GLS.C3.Layer1.Ivk79

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74 CFSG.Blueprint
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.EvenSelP
open CFSG.Open (ordA)

section Numbers

theorem fm9_big {q : ℕ} (hq : IsFM9 q) (h4 : 4 < q) (h5 : q ≠ 5) (h7 : q ≠ 7) (h9 : q ≠ 9)
    (h17 : q ≠ 17) : q = 31 ∨ 127 ≤ q := by
  rcases hq with h | ⟨hp, ⟨k, hk⟩ | ⟨n, hn⟩⟩
  · exact absurd h h9
  · by_cases hk3 : 3 ≤ k
    · right
      have h1 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      have h2 : 2 ^ (2 ^ 3) ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) h1
      omega
    · push Not at hk3
      interval_cases k <;> simp at hk <;> omega
  · by_cases hn7 : 7 ≤ n
    · right
      have h1 : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn7
      omega
    · push Not at hn7
      interval_cases n
      · omega
      · omega
      · omega
      · omega
      · exfalso
        have : q = 15 := by omega
        subst this
        exact absurd hp (by norm_num)
      · left; omega
      · exfalso
        have : q = 63 := by omega
        subst this
        exact absurd hp (by norm_num)

theorem not_dvd_ordA_one_big {q n : ℕ} (hq : q = 31 ∨ 127 ≤ q) (hqo : Odd q)
    (hn : n ∈ ({504, 5616, 6048, 7920, 29120, 58240, 190080} : Finset ℕ)) : ¬ ordA 1 q ∣ n := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  have hpos : 0 < n := by rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  intro hd
  obtain ⟨k, rfl⟩ := hqo
  rw [PumpClass.ordA_one_odd] at hd
  rcases hq with h31 | h127
  · have hk : k = 15 := by omega
    subst hk
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · have hk : 63 ≤ k := by omega
    have hle := Nat.le_of_dvd hpos hd
    have h1 : 2 * 63 * (63 + 1) * (2 * 63 + 1) ≤ 2 * k * (k + 1) * (2 * k + 1) := by gcongr
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end Numbers

section Shapes

@[expose] def BigShape : Prop :=
  ∀ (L : Type) [Group L] [Finite L], TwoThin.Gen4Comp L → InC2 L → ∀ q : ℕ, (q = 31 ∨ 127 ≤ q) →
    Odd q → ordA 1 q ∣ Nat.card L → HasL2Model L IsFM9

theorem bigShape_of_facts
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) : BigShape := by
  intro L _ _ hP hC q hq hqo hdvd
  rcases c2Shape_of_inC2 hG hF hC hP with ⟨-, hsimple⟩ | ⟨-, hc2, hM⟩ | ⟨-, hc2, hS⟩
  · rcases hsimple with ⟨p, f, hp, -, hfm, hL⟩ | hL28 | hL33 | hU33 | hSz | hM11
    · exact ⟨p, f, hp, (Generic.stated_of_lieModel_PSL hL).1.2.1, hfm, hL⟩
    · exfalso
      have hc : Nat.card L = 504 := by
        rw [card_of_lieModel_PSL (by norm_num) hL28]
        decide
      rw [hc] at hdvd
      exact not_dvd_ordA_one_big hq hqo (by decide) hdvd
    · exfalso
      have hc : Nat.card L = 5616 := by
        rw [card_of_lieModel_PSL (by norm_num) hL33]
        decide
      rw [hc] at hdvd
      exact not_dvd_ordA_one_big hq hqo (by decide) hdvd
    · exfalso
      have hc : Nat.card L = 6048 := by
        rw [card_of_lieModel_PSU (by norm_num) (by norm_num) hU33]
        decide
      rw [hc] at hdvd
      exact not_dvd_ordA_one_big hq hqo (by decide) hdvd
    · exfalso
      have hc : Nat.card L = 29120 := by
        rw [card_of_lieModel_twistedB2 hSz]
        decide
      rw [hc] at hdvd
      exact not_dvd_ordA_one_big hq hqo (by decide) hdvd
    · exfalso
      have hc : Nat.card L = 7920 :=
        card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hM11
      rw [hc] at hdvd
      exact not_dvd_ordA_one_big hq hqo (by decide) hdvd
  · exfalso
    have hc : Nat.card L = 190080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hc2,
        card_of_isSporadic_M12 hM]
      norm_num
    rw [hc] at hdvd
    exact not_dvd_ordA_one_big hq hqo (by decide) hdvd
  · exfalso
    have hc : Nat.card L = 58240 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hc2,
        card_of_lieModel_twistedB2 hS]
      decide
    rw [hc] at hdvd
    exact not_dvd_ordA_one_big hq hqo (by decide) hdvd

theorem c2Facts_of_facts
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) : PumpCalc.C2Facts :=
  ⟨fun _ _ _ hP hC hU hno => PumpClass.c2_u2_fm9 hG hF hP hC hU hno,
    fun _ _ _ hP hC hcen _ _ _ hS hno ⟨e⟩ =>
      PumpClass.not_inU2_quotient_of_centre hG hF hP hC hcen hS hno e⟩

end Shapes

section Step

variable {G : Type} [Group G] [Finite G]

theorem ivk_7_9_step (hC2 : PumpCalc.C2Facts) (hbig : BigShape) (hG : C3Hyp G) (hE : IsEvenType G)
    {z u : G} {J H : Subgroup G} (hlt : PumpUpLT 2 z J u H)
    (hJ : HasL2Model (kBar J) (fun q => IsFM9 q ∧ ¬ (q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 17))) :
    Nonempty (kBar H ≃* kBar J) := by
  obtain ⟨p, f, hp, hf, ⟨hfm, hne⟩, hLie⟩ := hJ
  have hp2 : p ≠ 2 := ne_two_of_isFM9 hf hfm
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq4 : 4 < p ^ f := by
    obtain ⟨F, _, _, e, hF, hFq⟩ := exists_l2Field_of_lieModel' hp hp2 hLie
    have h3 := hF.2
    rw [hFq] at h3
    obtain ⟨k, hk⟩ := hodd
    omega
  have hbigq : p ^ f = 31 ∨ 127 ≤ p ^ f :=
    fm9_big hfm hq4 (fun h => hne (Or.inl h)) (fun h => hne (Or.inr (Or.inl h)))
      (fun h => hne (Or.inr (Or.inr (Or.inl h)))) (fun h => hne (Or.inr (Or.inr (Or.inr h))))
  have hJc : IsPCompIn 2 (centralizer ({z} : Set G)) J := hlt.1.2.2
  have hH : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  have hu : orderOf u = 2 := hlt.2.1.1
  have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
  have hJU2 : InU2 (kBar J) :=
    ⟨isQuasisimple_hat hJc, Or.inl (hasL2Model_of_lieModel' hp hp2 hodd hLie)⟩
  have hJno : ¬ IsL34Quotient (kBar J) := not_isL34Quotient_of_lieModel hp hp2 hLie
  have hJs : IsSimpleGroup (kBar J) := isSimpleGroup_of_lieModel' hp hp2 hLie
  obtain ⟨Λ, hΛ⟩ := PumpCalc.exists_isLam hu hJc hlt.2.2.2.1
  have hzH : z ∈ normalizer (H : Set G) :=
    PumpCalc.stable_pumpup hG.pRank_eq_four hG.gen4 hE.1 hC2 hJU2 hJno hJs hlt hΛ
  have hΛL := PumpCalc.bar_le_of_stable hlt hΛ hzH
  have hΛJ : Λ ≤ J := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({u} : Set G) := hΛ.le.trans inf_le_right
  obtain ⟨φ, hφs, -, -⟩ := exists_phi hΛJ hΛY hΛ.cover
  have hd1 : Nat.card (kBar J) ∣ Nat.card ↥(PumpCalc.bar u Λ) := Subgroup.card_dvd_of_surjective hφs
  have hd2 : Nat.card ↥(PumpCalc.bar u Λ) ∣ Nat.card ↥(PumpCalc.bar u H) :=
    Subgroup.card_dvd_of_le hΛL
  have hcard : Nat.card (kBar J) = ordA 1 (p ^ f) := card_of_lieModel_psl2' hLie
  have hHC : InC2 ↥(PumpCalc.bar u H) := hE.1 u hu _ (PumpCalc.isComponent_bar hH)
  have hHP : Gen4Comp ↥(PumpCalc.bar u H) :=
    gen4Comp_of_gen4Cen (gen4Cen_barQ hG.gen4 hu) _
  have hL2H : HasL2Model ↥(PumpCalc.bar u H) IsFM9 :=
    hbig _ hHP hHC (p ^ f) hbigq hodd (hcard ▸ hd1.trans hd2)
  have hcen := PumpCalc.sbar_central hlt hΛ hzY hzH hL2H
  exact (PumpCalc.stable_trivial hlt hΛ hzY hzH hcen (PumpCalc.isSimple_of_hasL2Model hL2H)).1

end Step

end CFSG.GH74.GLS.C3.Layer1.Ivk79

namespace CFSG.GH74.GLS

open CFSG.GH74.GLS.C3.Layer1

theorem b_ivk_7_9_pump_of (hC2 : PumpCalc.C2Facts) (hbig : Ivk79.BigShape) : B_ivk_7_9_pump := by
  intro G _ _ hG hE x' K' x K _ hJ hlong
  have key : ∀ (a b : G × Subgroup G),
      Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT 2 a.1 a.2 b.1 b.2) a b →
      HasL2Model (kBar a.2) (fun q => IsFM9 q ∧ ¬ (q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 17)) →
      Nonempty (kBar b.2 ≃* kBar a.2) := by
    intro a b hab
    induction hab with
    | refl => exact fun _ => ⟨MulEquiv.refl _⟩
    | @tail c b hac hstep ih =>
      intro hP
      obtain ⟨e₁⟩ := ih hP
      have hPc := TwoThin.hasL2Model_of_mulEquiv e₁.symm hP
      obtain ⟨e₂⟩ := Ivk79.ivk_7_9_step hC2 hbig hG hE hstep hPc
      exact ⟨e₂.trans e₁⟩
  exact key (x', K') (x, K) hlong.2 hJ

theorem b_ivk_7_9_pump_proved
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) : B_ivk_7_9_pump :=
  b_ivk_7_9_pump_of (Ivk79.c2Facts_of_facts hGKF hE2) (Ivk79.bigShape_of_facts hGKF hE2)

end CFSG.GH74.GLS
