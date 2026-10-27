module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverUnitaryPairing

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open scoped commutatorElement
open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

variable {J : Type*} [Group J] [Finite J] {Q : Subgroup J} {u : J}

theorem inCenterOf_mul {G : Type*} [Group G] {P : Subgroup G} {a b : G} (ha : InCenterOf P a)
    (hb : InCenterOf P b) : InCenterOf P (a * b) :=
  ⟨P.mul_mem ha.1 hb.1, fun q hq => (ha.2 q hq).mul_right (hb.2 q hq)⟩

omit [Finite J] in
theorem coverPairing_one_right (a : J ⧸ Subgroup.center J) : coverPairing a 1 = 0 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← QuotientGroup.mk_one, coverPairing_mk, commutatorElement_one_right, neOneIndicator_one]

theorem zmod_two_three_vectors : ∀ A₁ B₁ A₂ B₂ A₃ B₃ : ZMod 2, A₁ = 1 → B₂ = 1 → A₃ + B₃ = 1 →
    A₁ * A₂ + B₁ * B₂ + (A₁ + B₁) * (A₂ + B₂) = 0 →
    A₁ * A₃ + B₁ * B₃ + (A₁ + B₁) * (A₃ + B₃) = 0 →
    A₂ * A₃ + B₂ * B₃ + (A₂ + B₂) * (A₃ + B₃) = 0 → False := by
  decide

theorem exists_central_lift_of_borelFacts (hZQ : Subgroup.center J ≤ Q)
    (hu : ∀ s ∈ Subgroup.center J, s * s = 1 → s = 1 ∨ s = u)
    (hBF : BenderBorelFacts (J ⧸ Subgroup.center J) (centralImage Q))
    (hab : ∀ x y : J, x ∈ Q → y ∈ Q → InCenterOf (centralImage Q) (x : J ⧸ Subgroup.center J) →
      InCenterOf (centralImage Q) (y : J ⧸ Subgroup.center J) → x * y = y * x)
    (hW2 : ∀ ω, InCenterOf (centralImage Q) ω → ω * ω = 1)
    (hcard : Nat.card {ω : J ⧸ Subgroup.center J // InCenterOf (centralImage Q) ω} = 4) :
    ∃ w₀ ∈ Q, (∀ q ∈ Q, Commute q w₀) ∧ w₀ ∉ Subgroup.center J := by
  classical
  obtain ⟨D, -, hDN, -, -, hform⟩ := hBF.torus
  have hfin := Set.toFinite {ω : J ⧸ Subgroup.center J | InCenterOf (centralImage Q) ω}
  set Wf := hfin.toFinset with hWf_def
  have hWf : ∀ ω, ω ∈ Wf ↔ InCenterOf (centralImage Q) ω := fun ω => Set.Finite.mem_toFinset _
  have hWcard : Wf.card = 4 := by
    rw [hWf_def, ← Nat.card_eq_card_finite_toFinset]
    exact hcard
  obtain ⟨β, hβ⟩ : ∃ β : J ⧸ Subgroup.center J → J ⧸ Subgroup.center J → ZMod 2,
      ∀ a b, β a b = ∑ ω ∈ Wf, coverPairing a ω * coverPairing b ω := ⟨_, fun _ _ => rfl⟩
  obtain ⟨ω₁, hω₁W, hω₁1⟩ := Finset.exists_mem_ne (by omega : 1 < Wf.card) 1
  obtain ⟨ω₂, hω₂W', hω₂₁⟩ := Finset.exists_mem_ne
    (by rw [Finset.card_erase_of_mem hω₁W]; omega : 1 < (Wf.erase ω₁).card) 1
  have hω₂W : ω₂ ∈ Wf := Finset.mem_of_mem_erase hω₂W'
  have hω₂ω₁ : ω₂ ≠ ω₁ := Finset.ne_of_mem_erase hω₂W'
  have hω₁ := (hWf ω₁).mp hω₁W
  have hω₂ := (hWf ω₂).mp hω₂W
  have hω₁₂ : InCenterOf (centralImage Q) (ω₁ * ω₂) := inCenterOf_mul hω₁ hω₂
  have h12_1 : ω₁ * ω₂ ≠ 1 := fun h => hω₂ω₁ (by
    have := hW2 ω₁ hω₁
    calc ω₂ = ω₁ * (ω₁ * ω₂) := by rw [← mul_assoc, this, one_mul]
      _ = ω₁ := by rw [h, mul_one])
  have h12_a : ω₁ * ω₂ ≠ ω₁ := fun h => hω₂₁ (by
    calc ω₂ = ω₁⁻¹ * (ω₁ * ω₂) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have h12_b : ω₁ * ω₂ ≠ ω₂ := fun h => hω₁1 (by
    calc ω₁ = (ω₁ * ω₂) * ω₂⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  have hWeq : Wf = {1, ω₁, ω₂, ω₁ * ω₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro ω hω
      simp only [Finset.mem_insert, Finset.mem_singleton] at hω
      rcases hω with rfl | rfl | rfl | rfl
      · exact (hWf 1).mpr (inCenterOf_one _)
      · exact hω₁W
      · exact hω₂W
      · exact (hWf _).mpr hω₁₂
    · rw [hWcard, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair (Ne.symm h12_b)]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hω₂ω₁.symm, Ne.symm h12_a⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hω₁1, Ne.symm hω₂₁, Ne.symm h12_1⟩
  have hsum : ∀ f : J ⧸ Subgroup.center J → ZMod 2,
      ∑ ω ∈ Wf, f ω = f 1 + f ω₁ + f ω₂ + f (ω₁ * ω₂) := by
    intro f
    rw [hWeq, Finset.sum_insert, Finset.sum_insert, Finset.sum_pair (Ne.symm h12_b)]
    · ring
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hω₂ω₁.symm, Ne.symm h12_a⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hω₁1, Ne.symm hω₂₁, Ne.symm h12_1⟩
  have hP12 : ∀ a ∈ centralImage Q,
      coverPairing a (ω₁ * ω₂) = coverPairing a ω₁ + coverPairing a ω₂ := fun a ha =>
    coverPairing_mul_right hZQ hu ha hω₁ hω₂ (hW2 _ hω₁) (hW2 _ hω₂)
  have hβe : ∀ a ∈ centralImage Q, ∀ b ∈ centralImage Q, β a b =
      coverPairing a ω₁ * coverPairing b ω₁ + coverPairing a ω₂ * coverPairing b ω₂ +
        (coverPairing a ω₁ + coverPairing a ω₂) * (coverPairing b ω₁ + coverPairing b ω₂) := by
    intro a ha b hb
    rw [hβ, hsum, coverPairing_one_right, coverPairing_one_right, hP12 a ha, hP12 b hb,
      zero_mul, zero_add]
  have h1 : ∀ a ∈ centralImage Q, ∀ b ∈ centralImage Q, ∀ c ∈ centralImage Q,
      β (a * b) c = β a c + β b c := by
    intro a ha b hb c _
    rw [hβ, hβ, hβ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [coverPairing_mul_left hZQ hu ha hb ((hWf ω).mp hω) (hW2 _ ((hWf ω).mp hω)), add_mul]
  have h2 : ∀ a ∈ centralImage Q, ∀ b ∈ centralImage Q, ∀ c ∈ centralImage Q,
      β a (b * c) = β a b + β a c := by
    intro a _ b hb c hc
    rw [hβ, hβ, hβ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [coverPairing_mul_left hZQ hu hb hc ((hWf ω).mp hω) (hW2 _ ((hWf ω).mp hω)), mul_add]
  have h3 : ∀ a ∈ centralImage Q, β a a = 0 := by
    intro a ha
    rw [hβe a ha a ha]
    generalize coverPairing a ω₁ = A
    generalize coverPairing a ω₂ = B
    revert A B
    decide
  have h4 : ∀ a ∈ centralImage Q, ∀ b, InCenterOf (centralImage Q) b → β a b = 0 := by
    intro a _ b hb
    rw [hβ]
    refine Finset.sum_eq_zero fun ω hω => ?_
    rw [coverPairing_eq_zero_of_inCenterOf hZQ hab hb ((hWf ω).mp hω), mul_zero]
  have h5 : ∀ d ∈ D, ∀ a ∈ centralImage Q, ∀ b ∈ centralImage Q,
      β (d⁻¹ * a * d) (d⁻¹ * b * d) = β a b := by
    intro d hd a _ b _
    rw [hβ, hβ]
    simp only [coverPairing_conj]
    have hdN := hDN hd
    have hdN' : d⁻¹ ∈ Subgroup.normalizer ((centralImage Q : Subgroup _) : Set _) :=
      Subgroup.inv_mem _ hdN
    apply Finset.sum_nbij' (fun ω => d * ω * d⁻¹) (fun ω => d⁻¹ * ω * d)
    · intro ω hω
      exact (hWf _).mpr (inCenterOf_conj hdN ((hWf ω).mp hω))
    · intro ω hω
      have := inCenterOf_conj hdN' ((hWf ω).mp hω)
      rw [inv_inv] at this
      exact (hWf _).mpr this
    · intro ω _
      group
    · intro ω _
      group
    · intro ω _
      rfl
  have hβ0 := hform β h1 h2 h3 h4 h5
  by_contra hno
  push Not at hno
  have hlift : ∀ ω, InCenterOf (centralImage Q) ω → ω ≠ 1 →
      ∃ a ∈ centralImage Q, coverPairing a ω = 1 := by
    intro ω hω hω1
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ω
    have hyQ : y ∈ Q := (mk_mem_centralImage_iff hZQ).mp hω.1
    have hyZ : y ∉ Subgroup.center J := fun h => hω1 ((QuotientGroup.eq_one_iff y).mpr h)
    have hnc : ¬ ∀ q ∈ Q, Commute q y := fun h => hyZ (hno y hyQ h)
    push Not at hnc
    obtain ⟨q, hq, hqy⟩ := hnc
    refine ⟨q, (mk_mem_centralImage_iff hZQ).mpr hq, ?_⟩
    rw [coverPairing_mk]
    have hne : ⁅q, y⁆ ≠ 1 := fun h => hqy (commutatorElement_eq_one_iff_mul_comm.mp h)
    simp [neOneIndicator, hne]
  obtain ⟨a₁, ha₁, hA₁⟩ := hlift ω₁ hω₁ hω₁1
  obtain ⟨a₂, ha₂, hB₂⟩ := hlift ω₂ hω₂ hω₂₁
  obtain ⟨a₃, ha₃, h₃⟩ := hlift _ hω₁₂ h12_1
  rw [hP12 a₃ ha₃] at h₃
  exact zmod_two_three_vectors _ _ _ _ _ _ hA₁ hB₂ h₃
    (by rw [← hβe a₁ ha₁ a₂ ha₂]; exact hβ0 _ ha₁ _ ha₂)
    (by rw [← hβe a₁ ha₁ a₃ ha₃]; exact hβ0 _ ha₁ _ ha₃)
    (by rw [← hβe a₂ ha₂ a₃ ha₃]; exact hβ0 _ ha₂ _ ha₃)

end CFSG.ProperTwoGeneratedCore.Lemma37
