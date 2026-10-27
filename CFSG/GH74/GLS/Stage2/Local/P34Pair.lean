module

public import CFSG.GH74.GLS.Stage2.Local.P34Step1
public import CFSG.GH74.GLS.Stage2.Local.P34Rank
public import CFSG.GH74.GLS.Stage2.Local.IVK33A

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

section Invol

variable {X : Type} [Group X]

theorem mem_zpowers_of_sq {e x : X} (he : e * e = 1) (hx : x ∈ zpowers e) : x = 1 ∨ x = e := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' m
  · left
    rw [zpow_mul, zpow_two, he, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, he, one_zpow, one_mul]

theorem isElemAbelian_zpowers {e : X} (he : e * e = 1) : Open.IsElemAbelian 2 (zpowers e) :=
  CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact he)

theorem card_zpowers_sq {e : X} (he : e * e = 1) (he1 : e ≠ 1) : Nat.card ↥(zpowers e) = 2 ^ 1 := by
  rw [Nat.card_zpowers, orderOf_eq_two_of_sq he he1, pow_one]

end Invol

section E8

variable {X : Type} [Group X]

theorem exists_E8 {c e₁ e₂ : X} (hc : c * c = 1) (h1 : e₁ * e₁ = 1) (h2 : e₂ * e₂ = 1)
    (hce₁ : c * e₁ = e₁ * c) (hce₂ : c * e₂ = e₂ * c) (he : e₁ * e₂ = e₂ * e₁)
    (hc1 : c ≠ 1) (h21 : e₂ ≠ 1) (h2c : e₂ ≠ c) (h11 : e₁ ≠ 1) (h1c : e₁ ≠ c) (h12 : e₁ ≠ e₂)
    (h1ce : e₁ ≠ c * e₂) :
    ∃ F : Subgroup X, F ≤ zpowers c ⊔ zpowers e₂ ⊔ zpowers e₁ ∧ Open.IsElemAbelian 2 F ∧
      Nat.card ↥F = 2 ^ 3 := by
  have hK₁₂ : ∀ a ∈ zpowers c, ∀ b ∈ zpowers e₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute c e₂ from hce₂) m n).eq
  have hinf₁₂ : zpowers c ⊓ zpowers e₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases mem_zpowers_of_sq hc hx.1 with rfl | rfl
    · exact Subgroup.one_mem _
    · rcases mem_zpowers_of_sq h2 hx.2 with h | h
      · exact absurd h hc1
      · exact absurd h.symm h2c
  obtain ⟨F₁, hF₁le, hF₁ea, hF₁card⟩ := exists_elemAbelian_join hK₁₂ hinf₁₂ (E := zpowers c)
    (E' := zpowers e₂) le_rfl le_rfl (isElemAbelian_zpowers hc) (isElemAbelian_zpowers h2)
    (card_zpowers_sq hc hc1) (card_zpowers_sq h2 h21)
  have hK₃₄ : ∀ a ∈ zpowers e₁, ∀ b ∈ zpowers c ⊔ zpowers e₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_commute' hK₁₂ hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hc' : Commute e₁ c := hce₁.symm
    have he' : Commute e₁ e₂ := he
    exact (Commute.mul_right (hc'.zpow_zpow m i) (he'.zpow_zpow m j)).eq
  have hinf₃₄ : zpowers e₁ ⊓ (zpowers c ⊔ zpowers e₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases mem_zpowers_of_sq h1 hx.1 with rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      obtain ⟨u, hu, v, hv, huv⟩ := exists_mul_of_mem_sup_of_commute' hK₁₂ hx.2
      rcases mem_zpowers_of_sq hc hu with rfl | rfl <;> rcases mem_zpowers_of_sq h2 hv with rfl | rfl
      · exact h11 (by simpa using huv)
      · exact h12 (by simpa using huv)
      · exact h1c (by simpa using huv)
      · exact h1ce huv
  obtain ⟨F₂, hF₂le, hF₂ea, hF₂card⟩ := exists_elemAbelian_join hK₃₄ hinf₃₄ (E := zpowers e₁)
    (E' := F₁) le_rfl hF₁le (isElemAbelian_zpowers h1) hF₁ea (card_zpowers_sq h1 h11) hF₁card
  refine ⟨F₂, hF₂le.trans (by rw [sup_comm]), hF₂ea, ?_⟩
  rw [hF₂card]

end E8

section Pair

variable {X : Type} [Group X] [Finite X] {L₁ L₂ : Subgroup X}

omit [Finite X] in
theorem inf_sq (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2) {c : X} (hc : c ∈ L₁ ⊓ L₂) : c * c = 1 := by
  have h : (⟨c, hc⟩ : ↥(L₁ ⊓ L₂)) ^ Nat.card ↥(L₁ ⊓ L₂) = 1 := pow_card_eq_one'
  rw [hcard] at h
  have := congrArg Subtype.val h
  simpa [pow_two] using this

omit [Finite X] in
theorem exists_inf_ne_one (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2) : ∃ c : X, c ∈ L₁ ∧ c ∈ L₂ ∧ c ≠ 1 := by
  by_contra hno
  push Not at hno
  have hbot : L₁ ⊓ L₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hno x hx.1 hx.2)
  rw [hbot] at hcard
  simp at hcard

omit [Finite X] in
theorem pair_perfect (hq₁ : IsQuasisimple ↥L₁) (hq₂ : IsQuasisimple ↥L₂) :
    ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ = L₁ ⊔ L₂ := by
  have h₁ : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.1 hq₁.1
  have h₂ : ⁅L₂, L₂⁆ = L₂ := Subgroup.isPerfect_iff.1 hq₂.1
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact (L₁ ⊔ L₂).mul_mem ((L₁ ⊔ L₂).mul_mem ((L₁ ⊔ L₂).mul_mem ha hb) ((L₁ ⊔ L₂).inv_mem ha))
      ((L₁ ⊔ L₂).inv_mem hb)
  · calc L₁ = ⁅L₁, L₁⁆ := h₁.symm
      _ ≤ ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc L₂ = ⁅L₂, L₂⁆ := h₂.symm
      _ ≤ ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem pair_rank_three (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2)
    (h₁ : HasSL2Model ↥L₁ Odd) (h₂ : HasSL2Model ↥L₂ Odd) : 3 ≤ Open.pRank 2 (L₁ ⊔ L₂) := by
  obtain ⟨c, hc₁, hc₂, hc1⟩ := exists_inf_ne_one hcard
  have hcc : c * c = 1 := inf_sq hcard ⟨hc₁, hc₂⟩
  have hcen₁ : (⟨c, hc₁⟩ : ↥L₁) ∈ Subgroup.center ↥L₁ :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm g g.2 c hc₂)
  have hcen₂ : (⟨c, hc₂⟩ : ↥L₂) ∈ Subgroup.center ↥L₂ :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm c hc₁ g g.2).symm
  have hc1' : (⟨c, hc₁⟩ : ↥L₁) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hc2' : (⟨c, hc₂⟩ : ↥L₂) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨a₁, b₁, _, ha₁, hb₁, hba₁, -, -⟩ := exists_quat_of_hasSL2Model h₁ hcen₁ hc1'
  obtain ⟨a₂, b₂, _, ha₂, hb₂, hba₂, -, -⟩ := exists_quat_of_hasSL2Model h₂ hcen₂ hc2'
  obtain ⟨A1, B1, hA1L, hB1L, hA1, hB1, hBA1⟩ : ∃ A1 B1 : X, A1 ∈ L₁ ∧ B1 ∈ L₁ ∧ A1 * A1 = c ∧
      B1 * B1 = c ∧ B1 * A1 = c * (A1 * B1) :=
    ⟨a₁, b₁, a₁.2, b₁.2, congrArg Subtype.val ha₁, congrArg Subtype.val hb₁,
      congrArg Subtype.val hba₁⟩
  obtain ⟨A2, B2, hA2L, hB2L, hA2, hB2, hBA2⟩ : ∃ A2 B2 : X, A2 ∈ L₂ ∧ B2 ∈ L₂ ∧ A2 * A2 = c ∧
      B2 * B2 = c ∧ B2 * A2 = c * (A2 * B2) :=
    ⟨a₂, b₂, a₂.2, b₂.2, congrArg Subtype.val ha₂, congrArg Subtype.val hb₂,
      congrArg Subtype.val hba₂⟩
  have c11 : A1 * A2 = A2 * A1 := hcomm A1 hA1L A2 hA2L
  have c12 : A1 * B2 = B2 * A1 := hcomm A1 hA1L B2 hB2L
  have c21 : B1 * A2 = A2 * B1 := hcomm B1 hB1L A2 hA2L
  have c22 : B1 * B2 = B2 * B1 := hcomm B1 hB1L B2 hB2L
  have cA1 : c * A1 = A1 * c := (hcomm A1 hA1L c hc₂).symm
  have cB1 : c * B1 = B1 * c := (hcomm B1 hB1L c hc₂).symm
  have cA2 : c * A2 = A2 * c := hcomm c hc₁ A2 hA2L
  have cB2 : c * B2 = B2 * c := hcomm c hc₁ B2 hB2L
  have hnc : (A1 * B1) ≠ B1 * A1 := by
    intro h
    rw [hBA1] at h
    have h' : c * (A1 * B1) = 1 * (A1 * B1) := by rw [one_mul]; exact h.symm
    exact hc1 (mul_right_cancel h')
  have e1sq : (A1 * A2) * (A1 * A2) = 1 := by
    calc A1 * A2 * (A1 * A2) = A1 * (A2 * A1) * A2 := by group
      _ = A1 * (A1 * A2) * A2 := by rw [← c11]
      _ = (A1 * A1) * (A2 * A2) := by group
      _ = 1 := by rw [hA1, hA2, hcc]
  have e2sq : (B1 * B2) * (B1 * B2) = 1 := by
    calc B1 * B2 * (B1 * B2) = B1 * (B2 * B1) * B2 := by group
      _ = B1 * (B1 * B2) * B2 := by rw [← c22]
      _ = (B1 * B1) * (B2 * B2) := by group
      _ = 1 := by rw [hB1, hB2, hcc]
  have e12 : (A1 * A2) * (B1 * B2) = (B1 * B2) * (A1 * A2) := by
    have l1 : (A1 * A2) * (B1 * B2) = (A1 * B1) * (A2 * B2) := by
      calc A1 * A2 * (B1 * B2) = A1 * (A2 * B1) * B2 := by group
        _ = A1 * (B1 * A2) * B2 := by rw [← c21]
        _ = (A1 * B1) * (A2 * B2) := by group
    have l2 : (B1 * B2) * (A1 * A2) = (A1 * B1) * (A2 * B2) := by
      calc B1 * B2 * (A1 * A2) = B1 * (B2 * A1) * A2 := by group
        _ = B1 * (A1 * B2) * A2 := by rw [← c12]
        _ = (B1 * A1) * (B2 * A2) := by group
        _ = (c * (A1 * B1)) * (c * (A2 * B2)) := by rw [hBA1, hBA2]
        _ = c * ((A1 * B1) * c) * (A2 * B2) := by group
        _ = c * (c * (A1 * B1)) * (A2 * B2) := by
          have : (A1 * B1) * c = c * (A1 * B1) := by
            calc (A1 * B1) * c = A1 * (B1 * c) := by group
              _ = A1 * (c * B1) := by rw [cB1]
              _ = (A1 * c) * B1 := by group
              _ = (c * A1) * B1 := by rw [cA1]
              _ = c * (A1 * B1) := by group
          rw [this]
        _ = (c * c) * (A1 * B1) * (A2 * B2) := by group
        _ = (A1 * B1) * (A2 * B2) := by rw [hcc, one_mul]
    rw [l1, l2]
  have ce1 : c * (A1 * A2) = (A1 * A2) * c := by
    calc c * (A1 * A2) = (c * A1) * A2 := by group
      _ = (A1 * c) * A2 := by rw [cA1]
      _ = A1 * (c * A2) := by group
      _ = A1 * (A2 * c) := by rw [cA2]
      _ = (A1 * A2) * c := by group
  have ce2 : c * (B1 * B2) = (B1 * B2) * c := by
    calc c * (B1 * B2) = (c * B1) * B2 := by group
      _ = (B1 * c) * B2 := by rw [cB1]
      _ = B1 * (c * B2) := by group
      _ = B1 * (B2 * c) := by rw [cB2]
      _ = (B1 * B2) * c := by group
  have keyA : ∀ f₁ ∈ L₁, ∀ f₂ ∈ L₂, f₁ * B1 = B1 * f₁ → A1 * A2 = f₁ * f₂ → False := by
    intro f₁ hf₁ f₂ hf₂ hfB heq
    have hu : f₁⁻¹ * A1 = f₂ * A2⁻¹ := by
      have : f₁⁻¹ * (A1 * A2) = f₂ := by rw [heq]; group
      calc f₁⁻¹ * A1 = f₁⁻¹ * (A1 * A2) * A2⁻¹ := by group
        _ = f₂ * A2⁻¹ := by rw [this]
    have hu₂ : f₁⁻¹ * A1 ∈ L₂ := by
      rw [hu]
      exact L₂.mul_mem hf₂ (L₂.inv_mem hA2L)
    have hcb : B1 * (f₁⁻¹ * A1) = (f₁⁻¹ * A1) * B1 := hcomm B1 hB1L _ hu₂
    apply hnc
    calc A1 * B1 = f₁ * ((f₁⁻¹ * A1) * B1) := by group
      _ = f₁ * (B1 * (f₁⁻¹ * A1)) := by rw [hcb]
      _ = (f₁ * B1) * (f₁⁻¹ * A1) := by group
      _ = (B1 * f₁) * (f₁⁻¹ * A1) := by rw [hfB]
      _ = B1 * A1 := by group
  have keyB : ∀ f₁ ∈ L₁, ∀ f₂ ∈ L₂, f₁ * A1 = A1 * f₁ → B1 * B2 = f₁ * f₂ → False := by
    intro f₁ hf₁ f₂ hf₂ hfA heq
    have hu : f₁⁻¹ * B1 = f₂ * B2⁻¹ := by
      have : f₁⁻¹ * (B1 * B2) = f₂ := by rw [heq]; group
      calc f₁⁻¹ * B1 = f₁⁻¹ * (B1 * B2) * B2⁻¹ := by group
        _ = f₂ * B2⁻¹ := by rw [this]
    have hu₂ : f₁⁻¹ * B1 ∈ L₂ := by
      rw [hu]
      exact L₂.mul_mem hf₂ (L₂.inv_mem hB2L)
    have hca : A1 * (f₁⁻¹ * B1) = (f₁⁻¹ * B1) * A1 := hcomm A1 hA1L _ hu₂
    apply hnc
    calc A1 * B1 = A1 * (f₁ * (f₁⁻¹ * B1)) := by group
      _ = (A1 * f₁) * (f₁⁻¹ * B1) := by group
      _ = (f₁ * A1) * (f₁⁻¹ * B1) := by rw [hfA]
      _ = f₁ * (A1 * (f₁⁻¹ * B1)) := by group
      _ = f₁ * ((f₁⁻¹ * B1) * A1) := by rw [hca]
      _ = B1 * A1 := by group
  have hcB1 : c * B1 = B1 * c := cB1
  have hcA1 : c * A1 = A1 * c := cA1
  have i11 : A1 * A2 ≠ 1 := fun h => keyA 1 L₁.one_mem 1 L₂.one_mem (by simp) (by simpa using h)
  have i1c : A1 * A2 ≠ c := fun h =>
    keyA c hc₁ 1 L₂.one_mem hcB1 (by simpa using h)
  have i12 : A1 * A2 ≠ B1 * B2 := fun h => keyA B1 hB1L B2 hB2L rfl h
  have hcB1' : c * B1 * B1 = B1 * (c * B1) := by
    calc c * B1 * B1 = (B1 * c) * B1 := by rw [cB1]
      _ = B1 * (c * B1) := by group
  have i1ce : A1 * A2 ≠ c * (B1 * B2) := fun h =>
    keyA (c * B1) (L₁.mul_mem hc₁ hB1L) B2 hB2L hcB1' (by rw [h]; group)
  have i21 : B1 * B2 ≠ 1 := fun h => keyB 1 L₁.one_mem 1 L₂.one_mem (by simp) (by simpa using h)
  have i2c : B1 * B2 ≠ c := fun h =>
    keyB c hc₁ 1 L₂.one_mem hcA1 (by simpa using h)
  obtain ⟨F, hFle, hFea, hFcard⟩ := exists_E8 hcc e1sq e2sq ce1 ce2 e12 hc1 i21 i2c i11 i1c i12
    i1ce
  have hL : zpowers c ⊔ zpowers (B1 * B2) ⊔ zpowers (A1 * A2) ≤ L₁ ⊔ L₂ := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_sup_left hc₁
    · rw [Subgroup.zpowers_le]
      exact (L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left hB1L) (Subgroup.mem_sup_right hB2L)
    · rw [Subgroup.zpowers_le]
      exact (L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left hA1L) (Subgroup.mem_sup_right hA2L)
  exact SectionRank.le_pRank (by norm_num) (hFle.trans hL) hFea hFcard

omit [Finite X] in
theorem pair_normal_mem {r₁ r₂ : ℕ} (hr₁ : Odd r₁) (h4₁ : 4 ≤ r₁) (hr₂ : Odd r₂) (h4₂ : 4 ≤ r₂)
    (h₁ : HasSL2Model ↥L₁ (fun r => r = r₁)) (h₂ : HasSL2Model ↥L₂ (fun r => r = r₂))
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2)
    {N : Subgroup X} (hNle : N ≤ L₁ ⊔ L₂) (hNn : ∀ l ∈ L₁ ⊔ L₂, ∀ n ∈ N, l * n * l⁻¹ ∈ N)
    (hN1 : N ≠ ⊥) {c : X} (hc₁ : c ∈ L₁) (hc₂ : c ∈ L₂) (hc1 : c ≠ 1) : c ∈ N := by
  classical
  have hcc : c * c = 1 := inf_sq hcard ⟨hc₁, hc₂⟩
  have hq₁ : IsQuasisimple ↥L₁ := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 h4₁ h₁
  have hq₂ : IsQuasisimple ↥L₂ := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 h4₂ h₂
  obtain ⟨t₁, -, -, -, ht₁c⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hr₁ h₁
  obtain ⟨t₂, -, -, -, ht₂c⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hr₂ h₂
  have hZ₁ : ∀ x ∈ L₁, (∀ w ∈ L₁, x * w = w * x) → x = 1 ∨ x = c := by
    intro x hx hxc
    have hct : c = t₁ := by
      rcases ht₁c c hc₁ (fun w hw => (hcomm w hw c hc₂).symm) with h | h
      · exact absurd h hc1
      · exact h
    rw [hct]
    exact ht₁c x hx hxc
  have hZ₂ : ∀ x ∈ L₂, (∀ w ∈ L₂, x * w = w * x) → x = 1 ∨ x = c := by
    intro x hx hxc
    have hct : c = t₂ := by
      rcases ht₂c c hc₂ (fun w hw => hcomm c hc₁ w hw) with h | h
      · exact absurd h hc1
      · exact h
    rw [hct]
    exact ht₂c x hx hxc
  have hNL₁ : (N.subgroupOf L₁).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn _ (Subgroup.mem_sup_left g.2) _ hn⟩
  have hNL₂ : (N.subgroupOf L₂).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn _ (Subgroup.mem_sup_right g.2) _ hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq₁ hNL₁ with htop₁ | hcen₁
  · have : (⟨c, hc₁⟩ : ↥L₁) ∈ N.subgroupOf L₁ := by rw [htop₁]; trivial
    exact this
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq₂ hNL₂ with htop₂ | hcen₂
  · have : (⟨c, hc₂⟩ : ↥L₂) ∈ N.subgroupOf L₂ := by rw [htop₂]; trivial
    exact this
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hno x hx)
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := exists_mul_of_mem_sup_of_commute' hcomm (hNle hnN)
  have hl₁c : l₁ = 1 ∨ l₁ = c := by
    refine hZ₁ l₁ hl₁ (fun w hw => ?_)
    have hcen : (⟨l₁, hl₁⟩ : ↥L₁) ∈ Subgroup.center ↥L₁ := by
      apply mem_center_of_commutators_central hq₁
      intro y
      have hcB : l₁ * (y : X) * l₁⁻¹ * (y : X)⁻¹ ∈ N := by
        have h1 : (l₁ * l₂) * ((y : X) * (l₁ * l₂)⁻¹ * (y : X)⁻¹) ∈ N :=
          N.mul_mem hnN (hNn (y : X) (Subgroup.mem_sup_left y.2) _ (N.inv_mem hnN))
        have h3 : (l₁ * l₂) * ((y : X) * (l₁ * l₂)⁻¹ * (y : X)⁻¹) =
            l₁ * (y : X) * l₁⁻¹ * (y : X)⁻¹ := by
          have hyl : (y : X) * l₂ = l₂ * (y : X) := hcomm y y.2 l₂ hl₂
          calc (l₁ * l₂) * ((y : X) * (l₁ * l₂)⁻¹ * (y : X)⁻¹)
              = l₁ * (l₂ * (y : X) * l₂⁻¹) * l₁⁻¹ * (y : X)⁻¹ := by group
            _ = l₁ * (y : X) * l₁⁻¹ * (y : X)⁻¹ := by
              rw [← hyl]; group
        rwa [h3] at h1
      exact hcen₁ (show (⟨l₁, hl₁⟩ : ↥L₁) * y * (⟨l₁, hl₁⟩ : ↥L₁)⁻¹ * y⁻¹ ∈ N.subgroupOf L₁ from hcB)
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨w, hw⟩)
    exact this.symm
  have hl₂c : l₂ = 1 ∨ l₂ = c := by
    refine hZ₂ l₂ hl₂ (fun w hw => ?_)
    have hcen : (⟨l₂, hl₂⟩ : ↥L₂) ∈ Subgroup.center ↥L₂ := by
      apply mem_center_of_commutators_central hq₂
      intro y
      have hcB : l₂ * (y : X) * l₂⁻¹ * (y : X)⁻¹ ∈ N := by
        have h1 : (l₁ * l₂) * ((y : X) * (l₁ * l₂)⁻¹ * (y : X)⁻¹) ∈ N :=
          N.mul_mem hnN (hNn (y : X) (Subgroup.mem_sup_right y.2) _ (N.inv_mem hnN))
        have h3 : (l₁ * l₂) * ((y : X) * (l₁ * l₂)⁻¹ * (y : X)⁻¹) =
            l₂ * (y : X) * l₂⁻¹ * (y : X)⁻¹ := by
          have hyl : (y : X) * l₁ = l₁ * (y : X) := (hcomm l₁ hl₁ y y.2).symm
          calc (l₁ * l₂) * ((y : X) * (l₁ * l₂)⁻¹ * (y : X)⁻¹)
              = l₂ * (l₁ * (y : X) * l₁⁻¹) * l₂⁻¹ * (y : X)⁻¹ := by
                have hl12 : l₁ * l₂ = l₂ * l₁ := hcomm l₁ hl₁ l₂ hl₂
                rw [hl12]
                group
            _ = l₂ * (y : X) * l₂⁻¹ * (y : X)⁻¹ := by
              rw [← hyl]; group
        rwa [h3] at h1
      exact hcen₂ (show (⟨l₂, hl₂⟩ : ↥L₂) * y * (⟨l₂, hl₂⟩ : ↥L₂)⁻¹ * y⁻¹ ∈ N.subgroupOf L₂ from hcB)
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨w, hw⟩)
    exact this.symm
  rcases hl₁c with h1 | h1 <;> rcases hl₂c with h2 | h2
  · exact absurd (by rw [h1, h2]; simp) hn1
  · rw [h1, h2] at hnN
    simpa using hnN
  · rw [h1, h2] at hnN
    simpa using hnN
  · exfalso
    apply hn1
    rw [h1, h2]
    exact hcc

end Pair

end CFSG.GH74.GLS.Stage2.Local.P34
