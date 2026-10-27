module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Cases
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open scoped commutatorElement

@[expose] def sporOrd : TauCeti.SporadicName → ℕ
  | .M11 => 7920
  | .M12 => 95040
  | .M22 => 443520
  | .M23 => 10200960
  | .M24 => 244823040
  | .J1 => 175560
  | .J2 => 604800
  | .J3 => orderJ3
  | .J4 => orderJ4
  | .HS => 44352000
  | .McL => 898128000
  | .He => 4030387200
  | .Ru => orderRu
  | .Suz => 448345497600
  | .ONan => orderON
  | .Co1 => orderCo1
  | .Co2 => 42305421312000
  | .Co3 => 495766656000
  | .Fi22 => 64561751654400
  | .Fi23 => orderFi23
  | .Fi24Prime => orderFi24Prime
  | .HN => orderHN
  | .Ly => orderLy
  | .Th => orderTh
  | .B => orderBabyMonster
  | .M => orderMonster

@[expose] def SporadicOrdersTable : Prop :=
  ∀ name : TauCeti.SporadicName, Nat.card (TauCeti.CFSGIndex.sporadic name).Group = sporOrd name

@[expose] def sporResidualNames : Finset TauCeti.SporadicName :=
  {.M12, .M22, .J3, .J4, .McL, .Suz, .He, .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .HN, .Ly,
    .Th, .B, .M}

@[expose] def SporNoPumpup (name : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → CFSG.Open.IsKGroup Y →
    GLAPPrimeCore 3 Y = ⊥ →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
    ∀ x : MulAut Y, orderOf x = 3 →
      ∀ J₁ : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ →
        (IsHatON (barOf 3 J₁) ∨ IsHatSix (barOf 3 J₁)) → False

@[expose] def ONSimpleNoPumpup : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → CFSG.Open.IsKGroup Y →
    GLAPPrimeCore 3 Y = ⊥ → Nat.card (Subgroup.center Y) = 1 →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) →
    ∀ x : MulAut Y, orderOf x = 3 →
      ∀ J₁ : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ →
        (IsHatON (barOf 3 J₁) ∨ IsHatSix (barOf 3 J₁)) → False

theorem odd_dvd_twelve {z : ℕ} (h : z ∣ 12) (ho : Odd z) : z = 1 ∨ z = 3 := by
  have hz : z ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases z <;> simp_all [Nat.odd_iff] <;> omega

theorem spor_arith : ∀ name : TauCeti.SporadicName, ∀ z : ℕ, (z = 1 ∨ z = 3) →
    z ∣ sporadicMultiplierOrder name →
      (3 * orderON ∣ z * sporOrd name → (name = .ONan ∧ z = 3) ∨ (name = .M ∧ z = 1)) ∧
      (1080 ∣ z * sporOrd name →
        name ≠ .M11 ∧ name ≠ .M23 ∧ name ≠ .J1 ∧ name ≠ .HS ∧ (name = .M22 → z = 3)) ∧
      (z = 3 → name = .M22 ∨ name = .J3 ∨ name = .McL ∨ name = .Suz ∨ name = .ONan ∨
        name = .Fi22 ∨ name = .Fi24Prime) := by
  intro name z hz hdvd
  revert hdvd
  rcases hz with rfl | rfl <;> cases name <;> decide +kernel

theorem card_center_dvd_mult (hSpM : SporadicMultipliers) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (name : TauCeti.SporadicName)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.sporadic name).Group) :
    Nat.card (Subgroup.center Y) ∣ sporadicMultiplierOrder name := by
  have hq' : CFSG.IsQuasisimple Y :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      Y hq⟩
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
  rw [hSpM.1 name] at hdvd
  exact hdvd

theorem gfr2_type_dvd (hOG : UniquenessMaximal.InputONGroup) {Y : Type} [Group Y] [Finite Y]
    {J : Subgroup Y} (hty : IsHatON (barOf 3 J) ∨ IsHatSix (barOf 3 J)) :
    (IsHatON (barOf 3 J) ∧ 3 * orderON ∣ Nat.card Y) ∨
      (IsHatSix (barOf 3 J) ∧ 1080 ∣ Nat.card Y) := by
  have hbar : Nat.card (barOf 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  have hJY : Nat.card J ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card J
  have hbc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (barOf 3 J))
  rcases hty with h | h
  · left
    refine ⟨h, ?_⟩
    have h2 := (UniquenessMaximal.isSimple_card_of_isHatON hOG h).2
    rw [h2, h.2.1] at hbc
    rw [mul_comm, ← hbc]
    exact hbar.trans hJY
  · right
    exact ⟨h, by rw [← gfr2_card_isHatSix h]; exact hbar.trans hJY⟩

theorem gapFinalPumpupSpor_of_residuals (hSpM : SporadicMultipliers) (hOrd : SporadicOrdersTable)
    (hOG : UniquenessMaximal.InputONGroup)
    (hR : ∀ name ∈ sporResidualNames, SporNoPumpup name) (hON : ONSimpleNoPumpup) :
    ∀ name, GapFinalPumpupSpor name := by
  intro name Y _ _ hq hKg hcore ⟨e⟩ x hxo J₁ hJ₁ hty
  by_cases hname : name ∈ sporResidualNames
  · exact (hR name hname Y hq hKg hcore ⟨e⟩ x hxo J₁ hJ₁ hty).elim
  have hl : name = .M11 ∨ name = .M23 ∨ name = .J1 ∨ name = .HS ∨ name = .M24 ∨ name = .J2 ∨
      name = .Ru ∨ name = .ONan := by
    revert hname
    cases name <;> simp [sporResidualNames]
  have hzodd := odd_card_center_of_core_bot hcore
  have hzd := card_center_dvd_mult hSpM hq name e
  have hz13 : Nat.card (Subgroup.center Y) = 1 ∨ Nat.card (Subgroup.center Y) = 3 :=
    odd_dvd_twelve (hzd.trans (sporadicMultiplierOrder_dvd_twelve name)) hzodd
  have hcard : Nat.card Y = Nat.card (Subgroup.center Y) * sporOrd name := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
    rw [Nat.card_congr e.toEquiv, hOrd name] at h1
    rw [h1, mul_comm]
  have harith := spor_arith name _ hz13 hzd
  have htd := gfr2_type_dvd hOG hty
  rw [hcard] at htd
  have hMJR : ∀ n : TauCeti.SporadicName, n = name → (n = .M24 ∨ n = .J2 ∨ n = .Ru) →
      Nat.card (Subgroup.center Y) = 1 → Nonempty (Y ≃* (TauCeti.CFSGIndex.sporadic name).Group) := by
    intro n _ _ h1
    have hbot : Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact ⟨((QuotientGroup.quotientBot (G := Y)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e))⟩
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    rcases htd with ⟨-, hd⟩ | ⟨-, hd⟩
    · rcases harith.1 hd with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
    · exact (harith.2.1 hd).1 rfl
  · exfalso
    rcases htd with ⟨-, hd⟩ | ⟨-, hd⟩
    · rcases harith.1 hd with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
    · exact (harith.2.1 hd).2.1 rfl
  · exfalso
    rcases htd with ⟨-, hd⟩ | ⟨-, hd⟩
    · rcases harith.1 hd with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
    · exact (harith.2.1 hd).2.2.1 rfl
  · exfalso
    rcases htd with ⟨-, hd⟩ | ⟨-, hd⟩
    · rcases harith.1 hd with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
    · exact (harith.2.1 hd).2.2.2.1 rfl
  · rcases hz13 with h1 | h3
    · obtain ⟨f⟩ := hMJR _ rfl (Or.inl rfl) h1
      exact Or.inr (Or.inr (Or.inl ⟨f⟩))
    · rcases harith.2.2 h3 with h | h | h | h | h | h | h <;> exact absurd h (by decide)
  · rcases hz13 with h1 | h3
    · obtain ⟨f⟩ := hMJR _ rfl (Or.inr (Or.inl rfl)) h1
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f⟩)))
    · rcases harith.2.2 h3 with h | h | h | h | h | h | h <;> exact absurd h (by decide)
  · rcases hz13 with h1 | h3
    · obtain ⟨f⟩ := hMJR _ rfl (Or.inr (Or.inr rfl)) h1
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f⟩)))
    · rcases harith.2.2 h3 with h | h | h | h | h | h | h <;> exact absurd h (by decide)
  · rcases hz13 with h1 | h3
    · exfalso
      rcases htd with ⟨-, hd⟩ | ⟨-, hd⟩
      · rcases harith.1 hd with ⟨-, h⟩ | ⟨h, -⟩
        · rw [h1] at h; exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact hON Y hq hKg hcore h1 ⟨e⟩ x hxo J₁ hJ₁ hty
    · exact Or.inl ⟨hq.1, h3, ⟨e⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator
