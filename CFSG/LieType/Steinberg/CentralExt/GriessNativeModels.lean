module

public import CFSG.LieType.Steinberg.CentralExt.GriessAllModels
import CFSG.Blueprint.LieModelAPI

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.BenderSuzuki.MatrixGroups (SuzukiMatrixGroup)

namespace CFSG.LieType.Steinberg.CentralExt.GriessNative

section Rows

variable {X : Type} [Group X]

theorem admissible_of_lieModel {t : StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem classical_of_lieModel {t : StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X t n p f) (ht : t ∈ classicalTags) :
    StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem models_lieModel_of_classical {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel X t n p f) : CFSG.Models.LieModel X t n p f :=
  ⟨h.1, Or.inl h⟩

theorem chevalley_of_lieModel {t : StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X t n p f) (ht : t ∈ chevalleyExceptionalTags) :
    n = 0 ∧ ChevalleyExceptionalModel X t p f :=
  (CFSG.Blueprint.LieModel.chevalleyExceptional_iff ht).1 h

theorem reeTits_of_lieModel {t : StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X t n p f) (ht : t ∈ reeTitsTags) :
    n = 0 ∧ ReeTitsModel X t p f :=
  CFSG.Blueprint.LieModel.reeTitsModel h ht

theorem suzuki_of_lieModel {n p f : ℕ} (h : CFSG.Blueprint.LieModel X .twistedB2 n p f) :
    n = 0 ∧ SuzukiModel X p f :=
  CFSG.Blueprint.LieModel.suzukiModel h

theorem charP_two_of_card {K : Type} [Field K] {p f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hp : p = 2) : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
    (by rw [hK, hp])

theorem twistedB2_row
    {p f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel X .twistedB2 0 p f) :
    GriessAll.GriessRow X .twistedB2 0 p f := by
  obtain ⟨-, rfl, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := suzuki_of_lieModel hmodel
  rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
  · obtain ⟨hX, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Sz8.multiplier_Sz_eight X hmodel
    let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
    exact ⟨hX, ⟨eM.trans (MulEquiv.uniqueProd.symm.trans
      (GriessClassical.toGenEx (t := .twistedB2) (n := 0) (p := 2) (f := 3) (a₁ := 1) (a₂ := 1)
        (b₁ := 2) (b₂ := 2) rfl (by decide)))⟩⟩
  · let e' : X ≃* SuzukiMatrixGroup a :=
      e.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)
    let eZ : SuzukiMatrixGroup a ⧸ Subgroup.center (SuzukiMatrixGroup a) ≃* SuzukiMatrixGroup a :=
      (QuotientGroup.quotientMulEquivOfEq (SuzukiClosed.suzuki_center_eq_bot ha2)).trans
        QuotientGroup.quotientBot
    refine GriessClassical.of_mulEquiv (e'.trans eZ.symm)
      (GriessExceptional.row_of_subsingleton rfl ?_ (SuzukiClosed.suzuki_hopfMultiplier ha2))
    unfold exceptionalOrders
    split <;> first | rfl | omega

section Exceptional

theorem g2_row {p f : ℕ} (h : ChevalleyExceptionalModel X .G2 p f) (hq : 5 ≤ p ^ f) :
    GriessAll.GriessRow X .G2 0 p f := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  refine GriessClassical.of_mulEquiv e (GriessExceptional.row_of_subsingleton rfl ?_
    (AdjointClosed.g2_hopfMultiplier (by rw [hK]; exact hq)))
  have h22 : ¬(p = 2 ∧ f = 2) := by
    rintro ⟨rfl, rfl⟩
    norm_num at hq
  have h31 : ¬(p = 3 ∧ f = 1) := by
    rintro ⟨rfl, rfl⟩
    norm_num at hq
  unfold exceptionalOrders
  split <;> simp_all

theorem f4_row
    {p f : ℕ} (h : ChevalleyExceptionalModel X .F4 p f)
    (hq : 3 ≤ p ^ f) : GriessAll.GriessRow X .F4 0 p f := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hM : commutator (AdjointQuotient .F4 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) := by
    rcases (show p ^ f = 3 ∨ p ^ f = 4 ∨ 5 ≤ p ^ f by omega) with h3 | h4 | h5
    · exact FieldThree.f4_three_hopfMultiplier (hK.trans h3)
    · have := charP_two_of_card hf hK (GriessAll.eq_of_pow_eq_four hp h4).1
      exact FieldFour.f4_four_hopfMultiplier (hK.trans (h4.trans (by norm_num)))
    · exact AdjointClosed.f4_hopfMultiplier (by rw [hK]; exact h5)
  refine GriessClassical.of_mulEquiv e (GriessExceptional.row_of_subsingleton rfl ?_ hM)
  have h21 : ¬(p = 2 ∧ f = 1) := by
    rintro ⟨rfl, rfl⟩
    norm_num at hq
  unfold exceptionalOrders
  split <;> simp_all

theorem e8_row
    {p f : ℕ} (h : ChevalleyExceptionalModel X .E8 p f) :
    GriessAll.GriessRow X .E8 0 p f := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hM : commutator (AdjointQuotient .E8 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) := by
    by_cases h3 : p ^ f = 3
    · exact FieldThree.e8_three_hopfMultiplier (hK.trans h3)
    rcases GriessExceptional.pow_cases hp (by omega) h3 with ⟨hp2, h2⟩ | ⟨hp2, h4⟩ | h5
    · have := charP_two_of_card hf hK hp2
      exact FieldTwo.e8_two_hopfMultiplier (hK.trans h2)
    · have := charP_two_of_card hf hK hp2
      exact FieldFour.e8_four_hopfMultiplier (hK.trans (h4.trans (by norm_num)))
    · exact AdjointClosed.e8_hopfMultiplier (by rw [hK]; exact h5)
  refine GriessClassical.of_mulEquiv e (GriessExceptional.row_of_subsingleton rfl ?_ hM)
  unfold exceptionalOrders
  split <;> simp_all

theorem e6_row
    {p f : ℕ} (h : ChevalleyExceptionalModel X .E6 p f) :
    GriessAll.GriessRow X .E6 0 p f := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hM : commutator (AdjointQuotient .E6 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 K) ≃*
        Multiplicative (ZMod (Nat.gcd 3 (Nat.card K - 1)))) := by
    by_cases h3 : p ^ f = 3
    · exact FieldThree.e6_three_hopfMultiplier (hK.trans h3)
    rcases GriessExceptional.pow_cases hp (by omega) h3 with ⟨hp2, h2⟩ | ⟨hp2, h4⟩ | h5
    · have := charP_two_of_card hf hK hp2
      exact FieldTwo.e6_two_hopfMultiplier (hK.trans h2)
    · have := charP_two_of_card hf hK hp2
      exact FieldFour.e6_four_hopfMultiplier (hK.trans (h4.trans (by norm_num)))
    · exact MinusculeClosed.e6_hopfMultiplier (by rw [hK]; exact h5)
  rw [hK] at hM
  refine GriessClassical.of_mulEquiv e (GriessClassical.of_mulEquiv_target ?_ hM)
  refine (GriessClassical.padOne _).trans (GriessClassical.toGenEx (t := .E6) (n := 0)
    (p := p) (f := f) (a₁ := Nat.gcd 3 (p ^ f - 1)) (a₂ := 1) (b₁ := 1) (b₂ := 1) rfl ?_)
  unfold exceptionalOrders
  split <;> simp_all

theorem e7_row
    {p f : ℕ} (h : ChevalleyExceptionalModel X .E7 p f) :
    GriessAll.GriessRow X .E7 0 p f := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hM : commutator (AdjointQuotient .E7 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
    by_cases h3 : p ^ f = 3
    · exact FieldThree.e7_three_hopfMultiplier (hK.trans h3)
    rcases GriessExceptional.pow_cases hp (by omega) h3 with ⟨hp2, h2⟩ | ⟨hp2, h4⟩ | h5
    · have := charP_two_of_card hf hK hp2
      exact FieldTwo.e7_two_hopfMultiplier (hK.trans h2)
    · have := charP_two_of_card hf hK hp2
      exact FieldFour.e7_four_hopfMultiplier (hK.trans (h4.trans (by norm_num)))
    · exact MinusculeClosed.e7_hopfMultiplier (by rw [hK]; exact h5)
  rw [hK] at hM
  refine GriessClassical.of_mulEquiv e (GriessClassical.of_mulEquiv_target ?_ hM)
  refine (GriessClassical.padOne _).trans (GriessClassical.toGenEx (t := .E7) (n := 0)
    (p := p) (f := f) (a₁ := Nat.gcd 2 (p ^ f - 1)) (a₂ := 1) (b₁ := 1) (b₂ := 1) rfl ?_)
  unfold exceptionalOrders
  split <;> simp_all

theorem twistedE6_row
    {p f : ℕ}
    (h : ChevalleyExceptionalModel X .twistedE6 p f) (hq : 3 ≤ p ^ f) :
    GriessAll.GriessRow X .twistedE6 0 p f := by
  obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  refine GriessClassical.of_mulEquiv e (GriessClassical.of_mulEquiv_target ?_
    (GriessExceptional.twistedE6_hopfMultiplier hq hK hσ))
  refine (GriessClassical.padOne _).trans (GriessClassical.toGenEx (t := .twistedE6) (n := 0)
    (p := p) (f := f) (a₁ := Nat.gcd 3 (p ^ f + 1)) (a₂ := 1) (b₁ := 1) (b₂ := 1) rfl ?_)
  have h21 : ¬(p = 2 ∧ f = 1) := by
    rintro ⟨rfl, rfl⟩
    norm_num at hq
  unfold exceptionalOrders
  split <;> simp_all

theorem trialityD4_row
    {p f : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 p f) :
    GriessAll.GriessRow X .trialityD4 0 p f := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  refine GriessClassical.of_mulEquiv e (GriessExceptional.row_of_subsingleton rfl ?_
    (GriessExceptional.triality_hopfMultiplier
      (le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hK hσ))
  unfold exceptionalOrders
  split <;> simp_all

theorem twistedG2_row {p f : ℕ} (h : ReeTitsModel X .twistedG2 p f) :
    GriessAll.GriessRow X .twistedG2 0 p f := by
  obtain ⟨⟨-, -, -, rfl, -, hf3⟩, a, rfl, K, _, _, hK, ⟨e⟩⟩ := h
  have ha : 1 ≤ a := by omega
  have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (p := 3)
      Nat.prime_three (by omega) hK
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) ≃*
        DerivedCentralQuotient (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a) := by
    rw [CFSG.LieType.Ree.ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ :=
    CFSG.LieType.Ree.ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2 ha hK
  let eZ : CFSG.LieType.Ree.ReeTag.G2.reeGamma K a ⧸
      Subgroup.center (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a) ≃*
        CFSG.LieType.Ree.ReeTag.G2.reeGamma K a :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Ree.ReeTag.center_reeGamma_G2_eq_bot hK)).trans QuotientGroup.quotientBot
  refine GriessClassical.of_mulEquiv (((e.trans e1).trans E).trans eZ.symm)
    (GriessExceptional.row_of_subsingleton rfl ?_ (SmallReeClosed.smallRee_hopfMultiplier hK ha))
  unfold exceptionalOrders
  split <;> first | rfl | omega

theorem twistedF4_row
    {p f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel X .twistedF4 0 p f) :
    GriessAll.GriessRow X .twistedF4 0 p f := by
  obtain ⟨-, ⟨-, -, -, rfl, -, hf3⟩, a, rfl, -⟩ := reeTits_of_lieModel hmodel (by decide)
  refine GriessExceptional.row_of_subsingleton rfl ?_
    (GriessExceptional.reeF4_hopfMultiplier (by omega) hmodel)
  unfold exceptionalOrders
  split <;> simp_all

theorem tits_row
    {p f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel X .Tits 0 p f) : GriessAll.GriessRow X .Tits 0 p f := by
  obtain ⟨-, ⟨-, -, -, rfl, rfl⟩, -⟩ := reeTits_of_lieModel hmodel (by decide)
  obtain ⟨hX, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Tits.multiplier_Tits X hmodel
  refine GriessExceptional.row_of_subsingleton rfl ?_ ⟨hX, eM.toEquiv.subsingleton⟩
  unfold exceptionalOrders
  split <;> simp_all

end Exceptional

end Rows

section Table

theorem griess_native_models_of_remaining
    (hG23 : ∀ (Y : Type) [Group Y], CFSG.Blueprint.LieModel Y .G2 0 3 1 →
      GriessAll.GriessRow Y .G2 0 3 1)
    (hG24 : ∀ (Y : Type) [Group Y], CFSG.Blueprint.LieModel Y .G2 0 2 2 →
      GriessAll.GriessRow Y .G2 0 2 2)
    (hF42 : ∀ (Y : Type) [Group Y], CFSG.Blueprint.LieModel Y .F4 0 2 1 →
      GriessAll.GriessRow Y .F4 0 2 1)
    (h2E62 : ∀ (Y : Type) [Group Y], CFSG.Blueprint.LieModel Y .twistedE6 0 2 1 →
      GriessAll.GriessRow Y .twistedE6 0 2 1)
    {X : Type} [Group X] (t : StatedLieTag) (n p f : ℕ)
    (hmodel : CFSG.Blueprint.LieModel X t n p f) :
    GriessAll.GriessRow X t n p f := by
  have hadm := admissible_of_lieModel hmodel
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  cases t with
  | PSL => exact GriessClassical.psl_row (classical_of_lieModel hmodel (by decide))
  | PSU =>
    have hcl := classical_of_lieModel hmodel (by decide)
    have hn : 3 ≤ n := hadm.2.2.1
    by_cases he : Even n
    · by_cases hq : 4 ≤ p ^ f ∨ (p ^ f = 2 ∧ 8 ≤ n) ∨ (p ^ f = 3 ∧ 6 ≤ n)
      · exact GriessClassical.psu_row hcl he hq
      · have hq' : p ^ f = 2 ∨ p ^ f = 3 := by omega
        obtain ⟨k, hk⟩ := he
        rcases hq' with h2 | h3
        · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
          have : n = 4 ∨ n = 6 := by omega
          rcases this with rfl | rfl
          · exact GriessClassical.psu_four_two_row (models_lieModel_of_classical hcl)
          · exact GriessClassical.psu_six_two_row (models_lieModel_of_classical hcl)
        · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_three h3
          have : n = 4 := by omega
          subst this
          exact GriessClassical.psu_four_three_row (models_lieModel_of_classical hcl)
    · exact GriessClassical.psu_odd_row hcl he
  | PSp =>
    have hcl := classical_of_lieModel hmodel (by decide)
    have hn : 2 ≤ n := hadm.2.2.1
    by_cases hq : 5 ≤ p ^ f ∨ p ^ f = 4 ∨ (p ^ f = 2 ∧ 4 ≤ n) ∨ (p ^ f = 3 ∧ 3 ≤ n)
    · exact GriessClassical.psp_row hcl hq
    · have hq' : p ^ f = 2 ∨ p ^ f = 3 := by omega
      rcases hq' with h2 | h3
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
        have hn3 : n = 2 ∨ n = 3 := by omega
        rcases hn3 with rfl | rfl
        · exact absurd rfl hadm.2.2.2
        · exact GriessClassical.psp_three_two_row (models_lieModel_of_classical hcl)
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_three h3
        have : n = 2 := by omega
        subst this
        exact GriessClassical.psp_four_three_row (models_lieModel_of_classical hcl)
  | POmegaOdd =>
    have hcl := classical_of_lieModel hmodel (by decide)
    have hn : 3 ≤ n := hadm.2.2.1
    have hp2 : p ≠ 2 := hadm.2.2.2
    by_cases hq : 5 ≤ p ^ f ∨ (p ^ f = 3 ∧ 4 ≤ n)
    · exact GriessClassical.pomegaOdd_row hcl hq
    · have hq' : p ^ f = 3 ∨ p ^ f = 4 ∨ p ^ f = 2 := by omega
      rcases hq' with h3 | h4 | h2
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_three h3
        have : n = 3 := by omega
        subst this
        exact GriessClassical.pomegaOdd_three_three_row (models_lieModel_of_classical hcl)
      · exact absurd (GriessAll.eq_of_pow_eq_four hp h4).1 hp2
      · exact absurd (GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2).1 hp2
  | POmegaPlus =>
    have hcl := classical_of_lieModel hmodel (by decide)
    have hn : 4 ≤ n := hadm.2.2
    by_cases hq : 3 ≤ p ^ f ∨ (p ^ f = 2 ∧ 5 ≤ n)
    · exact GriessClassical.pomegaPlus_row hcl hq
    · have h2 : p ^ f = 2 := by omega
      obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
      have : n = 4 := by omega
      subst this
      exact GriessClassical.pomegaPlus_four_two_row (models_lieModel_of_classical hcl)
  | POmegaMinus =>
    exact GriessClassical.pomegaMinus_row (classical_of_lieModel hmodel (by decide))
  | G2 =>
    obtain ⟨rfl, hce⟩ := chevalley_of_lieModel hmodel (by decide)
    have hq3 : 3 ≤ p ^ f := hadm.2.2.2
    by_cases hq : 5 ≤ p ^ f
    · exact g2_row hce hq
    · have hq' : p ^ f = 3 ∨ p ^ f = 4 := by omega
      rcases hq' with h3 | h4
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_three h3
        exact hG23 X hmodel
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_four hp h4
        exact hG24 X hmodel
  | F4 =>
    obtain ⟨rfl, hce⟩ := chevalley_of_lieModel hmodel (by decide)
    by_cases hq : 3 ≤ p ^ f
    · exact f4_row hce hq
    · have h2 : p ^ f = 2 := by omega
      obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
      exact hF42 X hmodel
  | E6 =>
    obtain ⟨rfl, hce⟩ := chevalley_of_lieModel hmodel (by decide)
    exact e6_row hce
  | E7 =>
    obtain ⟨rfl, hce⟩ := chevalley_of_lieModel hmodel (by decide)
    exact e7_row hce
  | E8 =>
    obtain ⟨rfl, hce⟩ := chevalley_of_lieModel hmodel (by decide)
    exact e8_row hce
  | twistedE6 =>
    obtain ⟨rfl, hce⟩ := chevalley_of_lieModel hmodel (by decide)
    by_cases hq : 3 ≤ p ^ f
    · exact twistedE6_row hce hq
    · have h2 : p ^ f = 2 := by omega
      obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
      exact h2E62 X hmodel
  | trialityD4 =>
    obtain ⟨rfl, hce⟩ := chevalley_of_lieModel hmodel (by decide)
    exact trialityD4_row hce
  | twistedB2 =>
    obtain ⟨rfl, -⟩ := suzuki_of_lieModel hmodel
    exact twistedB2_row hmodel
  | twistedG2 =>
    obtain ⟨rfl, hR⟩ := reeTits_of_lieModel hmodel (by decide)
    exact twistedG2_row hR
  | twistedF4 =>
    obtain ⟨rfl, -⟩ := reeTits_of_lieModel hmodel (by decide)
    exact twistedF4_row hmodel
  | Tits =>
    obtain ⟨rfl, -⟩ := reeTits_of_lieModel hmodel (by decide)
    exact tits_row hmodel

end Table

end CFSG.LieType.Steinberg.CentralExt.GriessNative
