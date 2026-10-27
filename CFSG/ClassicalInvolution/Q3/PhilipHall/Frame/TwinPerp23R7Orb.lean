module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Str
public import CFSG.ClassicalInvolution.Q3.Sec13L94Tight
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY1c

public section

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7O

section Gen

variable {G : Type} [Group G] {Q : Type} [Group Q]

theorem q8_exists_inv_conj {Y : Type*} [Group Y] {P : Subgroup Y} (φ : ↥P ≃* QuaternionGroup 2)
    {b : Y} (hb : b ∈ P) (hb2 : b * b ≠ 1) : ∃ y ∈ P, y * b * y⁻¹ = b⁻¹ := by
  have key : ∀ q : QuaternionGroup 2, q * q ≠ 1 → ∃ y : QuaternionGroup 2, y * q * y⁻¹ = q⁻¹ := by
    decide
  have hq : φ ⟨b, hb⟩ * φ ⟨b, hb⟩ ≠ 1 := by
    intro h
    apply hb2
    have : (⟨b, hb⟩ * ⟨b, hb⟩ : ↥P) = 1 := φ.injective (by rw [← map_mul] at h; rw [h, map_one])
    exact congrArg Subtype.val this
  obtain ⟨y0, hy0⟩ := key _ hq
  refine ⟨((φ.symm y0 : ↥P) : Y), (φ.symm y0).2, ?_⟩
  have : φ.symm y0 * ⟨b, hb⟩ * (φ.symm y0)⁻¹ = (⟨b, hb⟩ : ↥P)⁻¹ := by
    apply φ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hy0
  exact congrArg Subtype.val this

theorem mem_sup_zpowers_of_comm {H : Subgroup Q} {w : Q} (hw : w * w = 1)
    (hc : ∀ a ∈ H, a * w = w * a) {a : Q} (ha : a ∈ H ⊔ Subgroup.zpowers w) :
    a ∈ H ∨ a * w ∈ H := by
  have hc' : ∀ b : Q, b * w ∈ H → b * w = w * b := by
    intro b h
    have e : b * w * w = w * (b * w) := hc _ h
    calc b * w = b * w * (w * w) := by rw [hw, mul_one]
      _ = w * (b * w) * w := by rw [← mul_assoc, e]
      _ = w * b * (w * w) := by group
      _ = w * b := by rw [hw, mul_one]
  let K : Subgroup Q :=
    { carrier := {b | b ∈ H ∨ b * w ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (H.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact H.mul_mem ha hb)
        · refine Or.inr ?_
          have e : a * b * w = a * w * b := by rw [mul_assoc, hc b hb, ← mul_assoc]
          rw [e]
          exact H.mul_mem ha hb
        · refine Or.inl ?_
          have e : a * b = a * w * (b * w) := by
            rw [hc' b hb]
            calc a * b = a * (w * w) * b := by rw [hw, mul_one]
              _ = a * w * (w * b) := by group
          rw [e]
          exact H.mul_mem ha hb
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (H.inv_mem ha)
        · refine Or.inr ?_
          have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
          have h1 := hc' a ha
          have e : a⁻¹ * w = (a * w)⁻¹ := by
            rw [mul_inv_rev, hwi]
            calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
              _ = a⁻¹ * (a * w) * a⁻¹ := by rw [h1]
              _ = w * a⁻¹ := by group
          show a⁻¹ * w ∈ H
          rw [e]
          exact H.inv_mem ha }
  have hle : H ⊔ Subgroup.zpowers w ≤ K :=
    sup_le (fun b hb => Or.inl hb)
      (Subgroup.zpowers_le.mpr (Or.inr (by rw [hw]; exact H.one_mem)))
  exact hle ha

theorem two_mul_card_le [Finite Q] {H K : Subgroup Q} (hHK : H ≤ K) {w : Q} (hw : w ∈ K)
    (hwH : w ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  have hlt : H < K := lt_of_le_of_ne hHK (fun h => hwH (h ▸ hw))
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hHK
  have h1 := Subgroup.card_lt_of_lt hlt
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [hk] at h1 ⊢
  rcases k with _ | _ | k
  · simp at h1
  · simp at h1
  · nlinarith

@[expose] def cj (π : G →* Q) (X₀ : Q) (c : G) : Q := π c * X₀ * (π c)⁻¹

theorem cj_mul (π : G →* Q) (X₀ : Q) (c d : G) :
    cj π X₀ (c * d) = π c * cj π X₀ d * (π c)⁻¹ := by
  simp only [cj, map_mul, mul_inv_rev]
  group

theorem cj_inv_mul (π : G →* Q) (X₀ : Q) (c d : G) :
    cj π X₀ (c⁻¹ * d) = (π c)⁻¹ * cj π X₀ d * π c := by
  simp only [cj, map_mul, map_inv, mul_inv_rev, inv_inv]
  group

theorem cj_one (π : G →* Q) (X₀ : Q) : cj π X₀ 1 = X₀ := by simp [cj]

@[expose] def InCoset (π : G →* Q) (X₀ T : Q) (c : G) : Prop :=
  cj π X₀ c = X₀ ∨ cj π X₀ c = X₀ * T

theorem T_mem_closure (π : G →* Q) {X₀ T : Q} (hX₀2 : X₀ * X₀ = 1) {a : G}
    (ha : cj π X₀ a = X₀ * T) : T ∈ Subgroup.closure {q | ∃ c : G, q = cj π X₀ c} := by
  have h1 : X₀ ∈ Subgroup.closure {q | ∃ c : G, q = cj π X₀ c} :=
    Subgroup.subset_closure ⟨1, (cj_one π X₀).symm⟩
  have h2 : X₀ * T ∈ Subgroup.closure {q | ∃ c : G, q = cj π X₀ c} :=
    Subgroup.subset_closure ⟨a, ha.symm⟩
  have h := Subgroup.mul_mem _ h1 h2
  rwa [← mul_assoc, hX₀2, one_mul] at h

theorem orbit_cover [Finite G] [Finite Q] (π : G →* Q) {V : Subgroup Q} {X₀ T : Q}
    (hV : V = Subgroup.closure {q | ∃ c : G, q = cj π X₀ c})
    (hexp : ∀ v ∈ V, v * v = 1) (hcard : Nat.card V ≤ 8)
    (hT : ∀ c : G, π c * T = T * π c) {a : G} (ha : cj π X₀ a = X₀ * T)
    (hT1 : T ≠ 1) (hX1 : X₀ ≠ 1) (hXT : X₀ ≠ T) (P : Sylow 2 G)
    (hP : ∀ s ∈ (P : Subgroup G), InCoset π X₀ T s) :
    ∀ q ∈ V, q ≠ 1 → q = T ∨ ∃ c : G, q = cj π X₀ c := by
  intro q hqV hq1
  by_contra hcon
  push_neg at hcon
  obtain ⟨hqT, hqX⟩ := hcon
  have hTi : ∀ c : G, (π c)⁻¹ * T = T * (π c)⁻¹ := fun c => by
    rw [← map_inv]; exact hT c⁻¹
  have hXV : ∀ c : G, cj π X₀ c ∈ V := fun c => by
    rw [hV]; exact Subgroup.subset_closure ⟨c, rfl⟩
  have hX₀V : X₀ ∈ V := by simpa [cj_one] using hXV 1
  have hX₀2 : X₀ * X₀ = 1 := hexp _ hX₀V
  have hTV : T ∈ V := hV ▸ T_mem_closure π hX₀2 ha
  have hT2 : T * T = 1 := hexp _ hTV
  have hq2 : q * q = 1 := hexp _ hqV
  have hcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    have h1 := hexp _ (V.mul_mem hv hw)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hexp v hv)
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hexp w hw)
    calc v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = w * v := by rw [mul_inv_rev, hv', hw']
  have hcjT : ∀ (c : G) (y : Q), π c * (y * T) * (π c)⁻¹ = π c * y * (π c)⁻¹ * T := by
    intro c y
    calc π c * (y * T) * (π c)⁻¹ = π c * y * (T * (π c)⁻¹) := by group
      _ = π c * y * ((π c)⁻¹ * T) := by rw [hTi c]
      _ = π c * y * (π c)⁻¹ * T := by group
  have hcjTi : ∀ (c : G) (y : Q), (π c)⁻¹ * (y * T) * π c = (π c)⁻¹ * y * π c * T := by
    intro c y
    calc (π c)⁻¹ * (y * T) * π c = (π c)⁻¹ * y * (T * π c) := by group
      _ = (π c)⁻¹ * y * (π c * T) := by rw [hT c]
      _ = (π c)⁻¹ * y * π c * T := by group
  have hback : ∀ c : G, (π c)⁻¹ * cj π X₀ c * π c = X₀ := fun c => by simp only [cj]; group
  have hcj1 : ∀ c : G, cj π X₀ c ≠ 1 := fun c h => hX1 (by
    rw [← hback c, h]; group)
  have hcjT' : ∀ c : G, cj π X₀ c ≠ T := fun c h => hXT (by
    rw [← hback c, h, hTi c]; group)
  have hconjV : ∀ c : G, ∀ v ∈ V, π c * v * (π c)⁻¹ ∈ V := by
    intro c v hv
    rw [hV] at hv ⊢
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨d, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨c * d, (cj_mul π X₀ c d).symm⟩
    | one => simp
    | mul y z _ _ hy hz =>
      have e : π c * (y * z) * (π c)⁻¹ = (π c * y * (π c)⁻¹) * (π c * z * (π c)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have e : π c * y⁻¹ * (π c)⁻¹ = (π c * y * (π c)⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hy
  set A₁ : Subgroup Q := ⊥ ⊔ Subgroup.zpowers T with hA₁
  set A₂ : Subgroup Q := A₁ ⊔ Subgroup.zpowers X₀ with hA₂
  set A₃ : Subgroup Q := A₂ ⊔ Subgroup.zpowers q with hA₃
  have hA₁V : A₁ ≤ V := sup_le bot_le (Subgroup.zpowers_le.mpr hTV)
  have hA₂V : A₂ ≤ V := sup_le hA₁V (Subgroup.zpowers_le.mpr hX₀V)
  have hA₃V : A₃ ≤ V := sup_le hA₂V (Subgroup.zpowers_le.mpr hqV)
  have mem1 : ∀ y ∈ A₁, y = 1 ∨ y = T := by
    intro y hy
    rcases mem_sup_zpowers_of_comm hT2
        (fun b hb => by rw [Subgroup.mem_bot.mp hb, one_mul, mul_one]) hy with h | h
    · exact Or.inl (Subgroup.mem_bot.mp h)
    · right
      calc y = y * T * T := by rw [mul_assoc, hT2, mul_one]
        _ = T := by rw [Subgroup.mem_bot.mp h, one_mul]
  have mem2 : ∀ y ∈ A₂, y = 1 ∨ y = T ∨ y = X₀ ∨ y = X₀ * T := by
    intro y hy
    rcases mem_sup_zpowers_of_comm hX₀2 (fun b hb => hcomm b (hA₁V hb) X₀ hX₀V) hy with h | h
    · rcases mem1 y h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hy' : y = y * X₀ * X₀ := by rw [mul_assoc, hX₀2, mul_one]
      rcases mem1 _ h with h | h
      · right; right; left
        calc y = y * X₀ * X₀ := hy'
          _ = X₀ := by rw [h, one_mul]
      · right; right; right
        calc y = y * X₀ * X₀ := hy'
          _ = T * X₀ := by rw [h]
          _ = X₀ * T := hcomm T hTV X₀ hX₀V
  have hX₀T : X₀ * T = cj π X₀ a := ha.symm
  have hqA₂ : q ∉ A₂ := by
    intro h
    rcases mem2 q h with h | h | h | h
    · exact hq1 h
    · exact hqT h
    · exact hqX 1 (by rw [h, cj_one])
    · exact hqX a (by rw [h, hX₀T])
  have mem3 : ∀ y ∈ A₃, y ∈ A₂ ∨ y * q ∈ A₂ := fun y hy =>
    mem_sup_zpowers_of_comm hq2 (fun b hb => hcomm b (hA₂V hb) q hqV) hy
  have hVA₃ : ∀ v ∈ V, v ∈ A₃ := by
    intro v hv
    by_contra hvA
    have hX₀A₁ : X₀ ∉ A₁ := fun h => by
      rcases mem1 _ h with h | h
      · exact hX1 h
      · exact hXT h
    have h0 : Nat.card (⊥ : Subgroup Q) = 1 := Subgroup.card_bot
    have h1 : 2 * Nat.card (⊥ : Subgroup Q) ≤ Nat.card A₁ :=
      two_mul_card_le le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers T))
        (fun h => hT1 (Subgroup.mem_bot.mp h))
    have h2 : 2 * Nat.card A₁ ≤ Nat.card A₂ :=
      two_mul_card_le le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers X₀)) hX₀A₁
    have h3 : 2 * Nat.card A₂ ≤ Nat.card A₃ :=
      two_mul_card_le le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers q)) hqA₂
    have h4 : 2 * Nat.card A₃ ≤ Nat.card (A₃ ⊔ Subgroup.zpowers v : Subgroup Q) :=
      two_mul_card_le le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)) hvA
    have h5 : Nat.card (A₃ ⊔ Subgroup.zpowers v : Subgroup Q) ≤ Nat.card V :=
      Subgroup.card_le_of_le (sup_le hA₃V (Subgroup.zpowers_le.mpr hv))
    omega
  have hFG : ∀ c : G, InCoset π X₀ T c ∨
      (cj π X₀ c = q * X₀ ∨ cj π X₀ c = q * X₀ * T) := by
    intro c
    have hyV : cj π X₀ c ∈ V := hXV c
    have hyq : cj π X₀ c * q * q = cj π X₀ c := by rw [mul_assoc, hq2, mul_one]
    rcases mem3 _ (hVA₃ _ hyV) with h | h
    · rcases mem2 _ h with h | h | h | h
      · exact absurd h (hcj1 c)
      · exact absurd h (hcjT' c)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
    · rcases mem2 _ h with h | h | h | h
      · exact (hqX c (by rw [← hyq, h, one_mul])).elim
      · refine (hqX (c * a) ?_).elim
        rw [cj_mul, ha, hcjT c X₀]
        show q = cj π X₀ c * T
        calc q = q * T * T := by rw [mul_assoc, hT2, mul_one]
          _ = T * q * T := by rw [hcomm q hqV T hTV]
          _ = cj π X₀ c * q * q * T := by rw [h]
          _ = cj π X₀ c * T := by rw [hyq]
      · right; left
        calc cj π X₀ c = cj π X₀ c * q * q := hyq.symm
          _ = X₀ * q := by rw [h]
          _ = q * X₀ := hcomm X₀ hX₀V q hqV
      · right; right
        calc cj π X₀ c = cj π X₀ c * q * q := hyq.symm
          _ = X₀ * T * q := by rw [h]
          _ = X₀ * (q * T) := by rw [mul_assoc, hcomm T hTV q hqV]
          _ = q * X₀ * T := by rw [← mul_assoc, hcomm X₀ hX₀V q hqV]
  have hc₀ : ∃ c₀ : G, ¬ InCoset π X₀ T c₀ := by
    by_contra hall
    push_neg at hall
    apply hqA₂
    have hle : V ≤ A₂ := by
      rw [hV, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      rcases hall c with h | h
      · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers X₀)
      · rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers X₀))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers T)))
    exact hle hqV

  obtain ⟨c₀, hc₀⟩ := hc₀
  have L1 : ∀ c₁ c₂ : G, InCoset π X₀ T c₁ → InCoset π X₀ T c₂ → InCoset π X₀ T (c₁ * c₂) := by
    intro c₁ c₂ h₁ h₂
    unfold InCoset at h₁ h₂ ⊢
    rw [cj_mul]
    rcases h₂ with h₂ | h₂ <;> rw [h₂]
    · exact h₁
    · rw [hcjT]
      rcases h₁ with h₁ | h₁
      · exact Or.inr (by rw [show π c₁ * X₀ * (π c₁)⁻¹ = cj π X₀ c₁ from rfl, h₁])
      · exact Or.inl (by
          rw [show π c₁ * X₀ * (π c₁)⁻¹ = cj π X₀ c₁ from rfl, h₁, mul_assoc, hT2, mul_one])
  have L2 : ∀ c : G, InCoset π X₀ T c → InCoset π X₀ T c⁻¹ := by
    intro c h
    unfold InCoset at h ⊢
    have e : cj π X₀ c⁻¹ = (π c)⁻¹ * X₀ * π c := by simp [cj]
    rw [e]
    have h1 := hback c
    rcases h with h | h
    · left
      rwa [h] at h1
    · right
      rw [h, hcjTi] at h1
      calc (π c)⁻¹ * X₀ * π c = (π c)⁻¹ * X₀ * π c * T * T := by rw [mul_assoc _ T T, hT2, mul_one]
        _ = X₀ * T := by rw [h1]
  have L3 : ∀ c₁ c₂ : G, ¬ InCoset π X₀ T c₁ → ¬ InCoset π X₀ T c₂ →
      InCoset π X₀ T (c₁⁻¹ * c₂) := by
    intro c₁ c₂ h₁ h₂
    have g₁ := (hFG c₁).resolve_left h₁
    have g₂ := (hFG c₂).resolve_left h₂
    unfold InCoset
    rw [cj_inv_mul]
    have key : cj π X₀ c₂ = cj π X₀ c₁ ∨ cj π X₀ c₂ = cj π X₀ c₁ * T := by
      rcases g₁ with g₁ | g₁ <;> rcases g₂ with g₂ | g₂ <;> rw [g₁, g₂]
      · exact Or.inl rfl
      · exact Or.inr rfl
      · right
        rw [mul_assoc (q * X₀) T T, hT2, mul_one]
      · exact Or.inl rfl
    rcases key with k | k <;> rw [k]
    · exact Or.inl (hback c₁)
    · rw [hcjTi, hback c₁]
      exact Or.inr rfl
  have L4 : ∀ c : G, ¬ InCoset π X₀ T c → ¬ InCoset π X₀ T c⁻¹ := fun c h h' =>
    h (by simpa using L2 _ h')
  have L5 : ∀ c₁ c₂ : G, InCoset π X₀ T c₁ → ¬ InCoset π X₀ T c₂ →
      ¬ InCoset π X₀ T (c₁ * c₂) := fun c₁ c₂ h₁ h₂ h => h₂ (by
    have h' := L1 _ _ (L2 _ h₁) h
    rwa [inv_mul_cancel_left] at h')
  have L6 : ∀ c₁ c₂ : G, ¬ InCoset π X₀ T c₁ → InCoset π X₀ T c₂ →
      ¬ InCoset π X₀ T (c₁ * c₂) := fun c₁ c₂ h₁ h₂ h => h₁ (by
    have h' := L1 _ _ h (L2 _ h₂)
    rwa [mul_inv_cancel_right] at h')
  have Fone : InCoset π X₀ T 1 := Or.inl (cj_one π X₀)
  have Fsq : ∀ c : G, InCoset π X₀ T (c * c) := by
    intro c
    by_cases h : InCoset π X₀ T c
    · exact L1 _ _ h h
    · have h' := L3 c⁻¹ c (L4 c h) h
      rwa [inv_inv] at h'
  have Fpow : ∀ (c : G) (j : ℕ), InCoset π X₀ T ((c * c) ^ j) := by
    intro c j
    induction j with
    | zero => simpa using Fone
    | succ j ih =>
      rw [pow_succ]
      exact L1 _ _ ih (Fsq c)
  have Fodd : ∀ (c : G) (j : ℕ), ¬ InCoset π X₀ T c → ¬ InCoset π X₀ T (c ^ (2 * j + 1)) := by
    intro c j h
    have e : c ^ (2 * j + 1) = (c * c) ^ j * c := by rw [pow_succ, pow_mul, sq]
    rw [e]
    exact L5 _ _ (Fpow c j) h
  have Fconj : ∀ b s : G, InCoset π X₀ T (b⁻¹ * s * b) → InCoset π X₀ T s := by
    intro b s h
    by_contra hs
    by_cases hb : InCoset π X₀ T b
    · apply hs
      have h' := L1 _ _ (L1 _ _ hb h) (L2 _ hb)
      have e : b * (b⁻¹ * s * b) * b⁻¹ = s := by group
      rwa [e] at h'
    · have h1 : InCoset π X₀ T (s * b) := by
        have h' := L3 s⁻¹ b (L4 s hs) hb
        rwa [inv_inv] at h'
      apply L6 b⁻¹ (s * b) (L4 b hb) h1
      rwa [mul_assoc] at h
  have hn : orderOf c₀ ≠ 0 := (orderOf_pos c₀).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  obtain ⟨j, rfl⟩ := hm
  have hpow : (c₀ ^ (2 * j + 1)) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hd2 : IsPGroup 2 (Subgroup.zpowers (c₀ ^ (2 * j + 1))) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  obtain ⟨P', hP'⟩ := hd2.exists_le_sylow
  obtain ⟨b, hb⟩ := exists_conjSub_eq_of_sylow P P'
  have hdP' : c₀ ^ (2 * j + 1) ∈ (P' : Subgroup G) := hP' (Subgroup.mem_zpowers _)
  rw [← hb, mem_conjSub_iff] at hdP'
  exact Fodd c₀ j hc₀ (Fconj b _ (hP _ hdP'))

end Gen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7O

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23


section E7O

variable {n : ℕ}

@[expose] def P23E7E8 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        (∀ a ∈ p23ABar t u e, a * a = 1) ∧ Nat.card ↥(p23ABar t u e) ≤ 8

theorem conj_u_cases {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) {s : Y}
    (hsN : s ∈ Subgroup.normalizer (W : Set Y)) (hst : s ∈ Subgroup.centralizer ({t} : Set Y)) :
    s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * t := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have htwK : ∀ M ∈ Om R, IsUniqueInvolution M t → M = tightCore R ∨ M = K' := by
    intro M hM htM
    by_cases hMK : M = tightCore R
    · exact Or.inl hMK
    have hMp : M ∈ KPerp (Om R) (tightCore R) :=
      Set.mem_insert_of_mem _ (Q3CL.T3.twin_mem_omegaNbr hΩ hK hM hMK hz htM)
    rw [hperp] at hMp
    simpa [hMK] using hMp
  have hst' : s * t * s⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hst]
    group
  have hKK : ∀ M, M = tightCore R ∨ M = K' → M ≤ tightCore R ⊔ K' := by
    rintro M (rfl | rfl)
    · exact le_sup_left
    · exact le_sup_right
  have hsK : conjSub s (tightCore R) ≤ tightCore R ⊔ K' := by
    refine hKK _ (htwK _ (hΩ.conjInvariant s _ hK) ?_)
    have := hz.conj s
    rwa [hst'] at this
  have hsK' : conjSub s K' ≤ tightCore R ⊔ K' := by
    refine hKK _ (htwK _ (hΩ.conjInvariant s _ hc.std.hK'.1) ?_)
    have := hz'.conj s
    rwa [hst'] at this
  have hsup : conjSub s (tightCore R ⊔ K') ≤ tightCore R ⊔ K' := by
    rw [Sec13.L94T.conjSub_sup_eq]
    exact sup_le hsK hsK'
  set w := s * u * s⁻¹ with hw
  have hwKK : w ∈ tightCore R ⊔ K' := hsup (conj_mem_conjSub hd.hu)
  have hwW : w ∈ W := (Subgroup.mem_normalizer_iff.mp hsN u).mp hd.huW
  have hw2 : w * w = 1 := by
    rw [hw]
    calc s * u * s⁻¹ * (s * u * s⁻¹) = s * (u * u) * s⁻¹ := by group
      _ = 1 := by rw [hd.hu2]; group
  have hwB := mem_B_of_involution hc hwW hw2
  have cue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have cte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have hne : ∀ y ∈ tightCore R ⊔ K', e = y⁻¹ * w → False := fun y hy h =>
    e_not_mem_sup hc (h ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hwKK)
  have htKK : t ∈ tightCore R ⊔ K' := Subgroup.mem_sup_left hz.mem
  have huKK : u ∈ tightCore R ⊔ K' := hd.hu
  rcases T7K.mem_cases_of_commuting_involutions hd.hu2 hz.sq hd.he2 (comm_ut hc) cue cte hwB with
    h | h | h | h | h | h | h | h
  · exact absurd (by
      calc u = s⁻¹ * w * s := by rw [hw]; group
        _ = 1 := by rw [h]; group) hd.hu1
  · exact absurd (by
      calc u = s⁻¹ * w * s := by rw [hw]; group
        _ = s⁻¹ * (s * t * s⁻¹) * s := by rw [h, hst']
        _ = t := by group) hd.huz
  · exact Or.inl h
  · exact Or.inr h
  · exact (hne 1 (Subgroup.one_mem _) (by rw [h]; group)).elim
  · exact (hne t htKK (by rw [h]; group)).elim
  · exact (hne u huKK (by rw [h]; group)).elim
  · exact (hne (u * t) (Subgroup.mul_mem _ huKK htKK) (by rw [h]; group)).elim

theorem p23E7Orb_of_e8 (hE8 : P23E7E8 n) : P23E7Orb n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hexp, hcard⟩ := hE8 hcit hP Y R S t K' W u e g hc hno hE hZ
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have htr : ∀ K₁ ∈ Om R, ∀ J ∈ Om R, ∃ a : Y, conjSub a K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hNe : Subgroup.normalizer (W : Set Y) ≤ Subgroup.centralizer ({e} : Set Y) :=
    normalizer_le_centralizer_e hd
  have hKt : tightCore R ⊔ K' ≤ Subgroup.centralizer ({t} : Set Y) :=
    sup_le (le_centralizer_of_unique hz) (le_centralizer_of_unique hz')
  obtain ⟨S₀, hWS₀, hwc, -⟩ := exists_weaklyClosed_conj_of_muIsoS4 hPG htr hd.hW hd.hS4
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hWt : W ≤ Subgroup.centralizer ({t} : Set Y) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  obtain ⟨S₂, hS₂, hWS₂⟩ := IsSylow2In.exists_ge hW2 hWt
  obtain ⟨S₁, hSS₁⟩ := hS₂.2.1.exists_le_sylow
  obtain ⟨a, ha⟩ := exists_conjSub_eq_of_sylow S₀ S₁
  have e2 : conjSub a⁻¹ W = W := hwc a⁻¹ (by
    rw [conjSub_le_iff, inv_inv, ha]
    exact hWS₂.trans hSS₁)
  have e3 : conjSub a W = W := by
    conv_lhs => rw [← e2]
    exact conjSub_conjSub_inv a W
  have hS₂N : S₂ ≤ Subgroup.normalizer (W : Set Y) := by
    intro s hs
    have hs₀ : a⁻¹ * s * a ∈ (S₀ : Subgroup Y) := by
      have := hSS₁ hs
      rw [← ha] at this
      exact mem_conjSub_iff.mp this
    have e4 : conjSub (a⁻¹ * s * a) W = W :=
      hwc _ ((conjSub_mono hWS₀).trans (conjSub_eq_self_of_mem hs₀).le)
    have e5 : conjSub s W = W := by
      have : s = a * (a⁻¹ * s * a) * a⁻¹ := by group
      conv_lhs => rw [this]
      rw [conjSub_mul, conjSub_mul, e2, e4, e3]
    exact mem_normalizer_iff_conjSub_eq.mpr e5
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hR₁D, -, hcomm, hb₁R, hb'R', ob₁, -, hub, hne_ue⟩ :=
    e_decomp hc
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hR₁D.2.trans hNe
  obtain ⟨φ⟩ := members_sylow_q8 hc.std.perp _ hK R₁ hR₁
  obtain ⟨y, hyR, hyb⟩ := F7O.q8_exists_inv_conj φ hb₁R (by rw [ob₁]; exact hz.ne_one)
  have hyt : y * t = t * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz (hR₁.1 hyR))
  have hye : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.mp (hR₁e hyR)
  have hyb' : y * b' = b' * y := hcomm y hyR b' hb'R'
  have hb't : b' * t = t * b' :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz' (hR₁'.1 hb'R'))
  have hinv : b₁⁻¹ = b₁ * t := by
    apply inv_eq_of_mul_eq_one_right
    calc b₁ * (b₁ * t) = (b₁ * b₁) * t := by group
      _ = t * t := by rw [ob₁]
      _ = 1 := hz.sq
  have hyue : y * (u * e) * y⁻¹ = u * e * t := by
    have hyu : y * u * y⁻¹ = u * t := by
      calc y * u * y⁻¹ = (y * b₁ * y⁻¹) * (y * b' * y⁻¹) := by rw [hub]; group
        _ = (b₁ * t) * (b' * y * y⁻¹) := by rw [hyb, hinv, hyb']
        _ = b₁ * (t * b') := by group
        _ = b₁ * (b' * t) := by rw [hb't]
        _ = u * t := by rw [hub]; group
    calc y * (u * e) * y⁻¹ = (y * u * y⁻¹) * (e * y * y⁻¹) := by rw [← hye]; group
      _ = u * t * e := by rw [hyu]; group
      _ = u * e * t := by rw [mul_assoc, hWab t hd.hzW e heW, ← mul_assoc]
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hueC : u * e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
    (hWab _ (W.mul_mem hd.huW heW) _ hd.hzW)
  have hyC : y ∈ C := hKt (Subgroup.mem_sup_left (hR₁.1 hyR))
  let π : ↥C →* ↥C ⧸ classicalInvolutionOddCore ↥C :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥C)
  have hπ : ∀ c : ↥C, π c = (c : ↥C ⧸ classicalInvolutionOddCore ↥C) := fun _ => rfl
  let τ : ↥C := ⟨t, htC⟩
  let x : ↥C := ⟨u * e, hueC⟩
  have hodd : Odd (Nat.card ↥(Asc77.oddCoreOf C)) := oddCoreOf_odd_natCard C
  have hinvol : ∀ c : ↥C, (c : Y) * c = 1 → (c : Y) ≠ 1 → π c ≠ 1 := by
    intro c hc2 hc1 h
    rw [hπ, QuotientGroup.eq_one_iff] at h
    exact hc1 (eq_one_of_isPGroup_of_mem_odd hodd ⟨c, h, rfl⟩
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2))
  have hue2 : (u * e) * (u * e) = 1 := by
    rw [← hd.hgt]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hue1 : u * e ≠ 1 := by
    rw [← hd.hgt]
    intro h
    apply hz.ne_one
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hcjx : ∀ c : ↥C, F7O.cj π (π x) c = π (c * x * c⁻¹) := fun c => by
    simp [F7O.cj, map_mul, map_inv]
  have hV : p23ABar t u e =
      Subgroup.closure {q | ∃ c : ↥C, q = F7O.cj π (π x) c} := by
    unfold p23ABar
    congr 1
    ext q
    constructor
    · rintro ⟨x', ⟨c, hc', hx'⟩, rfl⟩
      refine ⟨⟨c, hc'⟩, ?_⟩
      have e1 : x' = ⟨c, hc'⟩ * x * ⟨c, hc'⟩⁻¹ := Subtype.ext (by simp [hx', x])
      rw [hcjx, e1]
      rfl
    · rintro ⟨c, rfl⟩
      exact ⟨c * x * c⁻¹, ⟨c, c.2, by simp [x]⟩, (hcjx c).symm⟩
  have hTc : ∀ c : ↥C, π c * π τ = π τ * π c := fun c => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  have ha : F7O.cj π (π x) ⟨y, hyC⟩ = π x * π τ := by
    rw [hcjx, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa [x, τ] using hyue)
  have hT1 : π τ ≠ 1 := hinvol τ hz.sq hz.ne_one
  have hX1 : π x ≠ 1 := hinvol x hue2 hue1
  have hXT : π x ≠ π τ := by
    intro h
    rw [hπ, hπ, QuotientGroup.eq] at h
    have h2 : ((x⁻¹ * τ : ↥C) : Y) * ((x⁻¹ * τ : ↥C) : Y) = 1 := by
      have hxt : (u * e) * t = t * (u * e) := Subgroup.mem_centralizer_singleton_iff.mp hueC
      have hi : (u * e)⁻¹ = u * e := inv_eq_of_mul_eq_one_right hue2
      show (u * e)⁻¹ * t * ((u * e)⁻¹ * t) = 1
      rw [hi]
      calc u * e * t * (u * e * t) = u * e * (t * (u * e)) * t := by group
        _ = u * e * ((u * e) * t) * t := by rw [hxt]
        _ = (u * e * (u * e)) * (t * t) := by group
        _ = 1 := by rw [hue2, hz.sq, one_mul]
    have h1 := eq_one_of_isPGroup_of_mem_odd hodd ⟨_, h, rfl⟩
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h2)
    apply hne_ue
    have h3 : (u * e)⁻¹ * t = 1 := h1
    rw [← hd.hgt] at h3 ⊢
    exact inv_mul_eq_one.mp h3
  let P₂ : Sylow 2 ↥C := Asc77.AscP1Nine3.sylowOfIsSylow2In₉ hS₂
  have hPx : ∀ s ∈ (P₂ : Subgroup ↥C), F7O.InCoset π (π x) (π τ) s := by
    intro s hs
    have hsS : (s : Y) ∈ S₂ := Subgroup.mem_subgroupOf.mp (show s ∈ S₂.subgroupOf C from hs)
    have hsN := hS₂N hsS
    have hse : (s : Y) * e * (s : Y)⁻¹ = e := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hNe hsN)]
      group
    unfold F7O.InCoset
    rw [hcjx]
    rcases conj_u_cases hc hsN s.2 with h | h
    · left
      congr 1
      exact Subtype.ext (by
        show (s : Y) * (u * e) * (s : Y)⁻¹ = u * e
        calc (s : Y) * (u * e) * (s : Y)⁻¹ = ((s : Y) * u * (s : Y)⁻¹) * ((s : Y) * e * (s : Y)⁻¹) :=
              by group
          _ = u * e := by rw [h, hse])
    · right
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by
        show (s : Y) * (u * e) * (s : Y)⁻¹ = u * e * t
        calc (s : Y) * (u * e) * (s : Y)⁻¹ = ((s : Y) * u * (s : Y)⁻¹) * ((s : Y) * e * (s : Y)⁻¹) :=
              by group
          _ = u * t * e := by rw [h, hse]
          _ = u * e * t := by rw [mul_assoc, hWab t hd.hzW e heW, ← mul_assoc])
  have hX₀2 : π x * π x = 1 := by
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext hue2
    rw [this, map_one]
  refine ⟨?_, fun q hq hq1 => ?_⟩
  · have := F7O.T_mem_closure π hX₀2 ha
    rw [← hV] at this
    exact this
  · rcases F7O.orbit_cover π hV hexp hcard hTc ha hT1 hX1 hXT P₂ hPx q hq hq1 with
      h | ⟨c, hc'⟩
    · exact ⟨τ, ⟨1, by simp [τ]⟩, h⟩
    · refine ⟨c * x * c⁻¹, ⟨(c : Y) * g, ?_⟩, by rw [hc', hcjx]; rfl⟩
      show (c : Y) * (u * e) * (c : Y)⁻¹ = (c : Y) * g * t * ((c : Y) * g)⁻¹
      rw [← hd.hgt]
      group

end E7O

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
