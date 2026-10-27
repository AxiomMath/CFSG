module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveInputs
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSplit
public import CFSG.LieType.SeitzGeneration.ExcHigh.Leaves

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  TauCeti

section Arith

theorem e8Five_dvd_pred_of_orderOf_eq_one {q : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod 5) = 1) : 5 ∣ q - 1 := by
  rw [orderOf_eq_one_iff] at h
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, h, Nat.cast_one, sub_self]

theorem e8Five_dvd_succ_of_orderOf_eq_two {q : ℕ} (h : orderOf ((q : ℕ) : ZMod 5) = 2) :
    5 ∣ q + 1 := by
  have h2 : ((q : ℕ) : ZMod 5) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  have h1 : ((q : ℕ) : ZMod 5) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at h; omega
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
  generalize ((q : ℕ) : ZMod 5) = x at h2 h1
  revert x
  decide

theorem e8Five_not_dvd_of_orderOf_eq_four {q : ℕ} (h : orderOf ((q : ℕ) : ZMod 5) = 4) :
    ¬ 5 ∣ q := by
  intro hd
  rw [← ZMod.natCast_eq_zero_iff] at hd
  rw [hd, orderOf_zero] at h
  omega

theorem e8Five_not_dvd_pred_of_orderOf_eq_four {q : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod 5) = 4) : ¬ 5 ∣ q - 1 := by
  intro hd
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at hd
  rw [hd, orderOf_one] at h
  omega

theorem e8Five_not_dvd_of_orderOf_eq_one {q : ℕ} (h : orderOf ((q : ℕ) : ZMod 5) = 1) :
    ¬ 5 ∣ q := by
  intro hd
  rw [← ZMod.natCast_eq_zero_iff] at hd
  rw [hd, orderOf_zero] at h
  omega

theorem e8Five_not_dvd_of_orderOf_eq_two {q : ℕ} (h : orderOf ((q : ℕ) : ZMod 5) = 2) :
    ¬ 5 ∣ q := by
  intro hd
  rw [← ZMod.natCast_eq_zero_iff] at hd
  rw [hd, orderOf_zero] at h
  omega

end Arith

section Assembly


theorem seitzExcHighE8_five_of_native {R : ℕ → Prop} (hR : ∀ p : ℕ, p.Prime → 5 ≤ p → R p → p = 5)
    {e : ℕ}
    (h : ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = e →
      ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
        ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤) :
    SeitzExcHighForAt IsE8Index fun d p =>
      R p ∧ ClassRange LieTypeIndex.E8 (fun _ => True) e d p := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hR', hp5, q, hdq, -, hord⟩, -, hn⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, hchar, ⟨eq⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  have hp5' : p = 5 := hR p hp hp5 hR'
  subst hp5'
  have hord' : orderOf ((Nat.card K : ℕ) : ZMod 5) = e := by
    rw [hKq]
    exact hord
  have hr : ringChar K = (LieTypeIndex.E8 q).characteristic := by
    rw [LieTypeIndex.characteristic_E8]
    exact ringChar.eq K q.p
  refine planeGen_of_native_closure_cond (r := ringChar K) eq center_adjointGroup_eq_bot
    (fun E₀ hE₀p hE₀c hN => h K hord' E₀ hE₀p hE₀c hN) hE hcard hin ?_
  rw [hr]
  exact hn

theorem e8Five_one_native (hC : E8FiveOneClosing) :
    ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 1 →
      ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
        ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  intro K _ _ he E₀ hE₀p hE₀c hN
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpq : 5 ∣ Nat.card K - 1 := e8Five_dvd_pred_of_orderOf_eq_one hq1 he
  have hpK : ¬ 5 ∣ Nat.card K := e8Five_not_dvd_of_orderOf_eq_one he
  have hn' : ¬ NormalizesRNative Tag.E8 K E₀ := fun h => hN (normalizesRGroup_of_native h)
  obtain ⟨D, hD⟩ := e8Five_regular_datum hpK hE₀p hE₀c hn'
  exact hC K hpq E₀ hE₀p hE₀c D hD (fun hw => hn' (e8_normalizesRNative_of_split_datum D hw))

theorem e8Five_two_native (hC : E8FiveTwoClosing) (hF : E8FiveTwoFrameDatum) :
    ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 2 →
      ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
        ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  intro K _ _ he E₀ hE₀p hE₀c hN
  have hpq : 5 ∣ Nat.card K + 1 := e8Five_dvd_succ_of_orderOf_eq_two he
  have hpK : ¬ 5 ∣ Nat.card K := e8Five_not_dvd_of_orderOf_eq_two he
  have hn' : ¬ NormalizesRNative Tag.E8 K E₀ := fun h => hN (normalizesRGroup_of_native h)
  obtain ⟨D, hD⟩ := e8Five_regular_datum hpK hE₀p hE₀c hn'
  by_cases hw : ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -u
  · obtain ⟨k, hk⟩ := exists_conj_le_of_frameDatum hE₀p D (hF K hpq D.Fr D.hFr D.w hw)
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
    exact closure_centralizers_eq_top_of_two_conj (p := 5) (⨆ k, e8D8Chain K k) (e8FrameGroup K)
      (weylWordElt .E8 K e8Word) e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
      (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
      (fun E hE hEp hEc => iSup_d8Chain_le_closure_centralizers_two Nat.prime_five le_rfl hpq Ψ
        hker hrange E hE hEp hEc) E₀ hE₀p hE₀c ⟨k, hk⟩
  · exact hC K hpq E₀ hE₀p hE₀c D hD (not_forall.1 hw)

theorem e8Five_four_native (hSq : E8FiveFourSquare) (hF : E8FiveFourFrameDatum) :
    ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 4 →
      ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
        ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  intro K _ _ he E₀ hE₀p hE₀c hN
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK : ¬ 5 ∣ Nat.card K := e8Five_not_dvd_of_orderOf_eq_four he
  have hpq1 : ¬ 5 ∣ Nat.card K - 1 := e8Five_not_dvd_pred_of_orderOf_eq_four hq1 he
  have hn' : ¬ NormalizesRNative Tag.E8 K E₀ := fun h => hN (normalizesRGroup_of_native h)
  obtain ⟨D, hD⟩ := e8Five_regular_datum hpK hE₀p hE₀c hn'
  obtain ⟨k, hk⟩ := exists_conj_le_of_frameDatum hE₀p D
    (hF K he D.Fr D.hFr D.w (hSq K he E₀ hE₀p hE₀c D hD))
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  exact closure_centralizers_eq_top_of_two_conj (p := 5) (⨆ k, e8D8Chain K k) (e8D4Group K)
    (weylWordElt .E8 K e8Word) e8D4Group_le_d8 e8D4Group_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_d8Chain_le_closure_centralizers_of_ne Nat.prime_five le_rfl hpK hpq1 Ψ
      hker hrange E hE hEp hEc) E₀ hE₀p hE₀c ⟨k, hk⟩

theorem seitzExcHighE8OneLtSeven_of_inputs (hC : E8FiveOneClosing) :
    SeitzExcHighE8OneLtSeven :=
  seitzExcHighE8_five_of_native (R := fun p => p < 7) (e := 1)
    (fun p hp h5 h7 => by
      rcases (by omega : p = 5 ∨ p = 6) with rfl | rfl
      · rfl
      · exact absurd hp (by norm_num))
    (e8Five_one_native hC)

theorem seitzExcHighE8TwoFive_of_inputs (hC : E8FiveTwoClosing) (hF : E8FiveTwoFrameDatum) :
    SeitzExcHighE8TwoFive :=
  seitzExcHighE8_five_of_native (R := fun p => p = 5) (e := 2) (fun _ _ _ h => h)
    (e8Five_two_native hC hF)

theorem seitzExcHighE8FourLtSeven_of_inputs (hSq : E8FiveFourSquare) (hF : E8FiveFourFrameDatum) :
    SeitzExcHighE8FourLtSeven :=
  seitzExcHighE8_five_of_native (R := fun p => p < 7) (e := 4)
    (fun p hp h5 h7 => by
      rcases (by omega : p = 5 ∨ p = 6) with rfl | rfl
      · rfl
      · exact absurd hp (by norm_num))
    (e8Five_four_native hSq hF)

end Assembly

end CFSG.LieType.SeitzGeneration.ExcHigh
