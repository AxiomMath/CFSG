module

public import CFSG.CGT.PushingUpLit.BHS.FourOneB

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne
open FourOneTools

namespace Hyp41

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))}

theorem four_seven_not_normalizes (h : Hyp41 P D) {A₁ A₂ : Subgroup (MulAut V)} (h₁ : A₁ ∈ D)
    (h₂ : A₂ ∈ D) {a : MulAut V} (ha : a ∈ A₂) (hne : conjSub a A₁ ≠ A₁)
    (hc : ∀ x ∈ A₁, ∀ y ∈ conjSub a A₁, x * y = y * x)
    (hsm : A₁ ⊔ conjSub a A₁ ≠ A₁ ⊔ A₂) (hN : ∀ b ∈ A₁, conjSub b A₂ = A₂) : False := by
  obtain ⟨x, hx, hax⟩ : ∃ x ∈ A₁, a * x ≠ x * a := by
    by_contra hcon
    push Not at hcon
    exact hne (conjSub_eq_of_comm hcon)
  have hxa : x * a⁻¹ * x⁻¹ ∈ A₂ := by
    have := mem_conjSub_of_mem (g := x) (A₂.inv_mem ha)
    rwa [hN x hx] at this
  have hy₂ : a * x * a⁻¹ * x⁻¹ ∈ A₂ := by
    have : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
    rw [this]
    exact A₂.mul_mem ha hxa
  have hy₁ : a * x * a⁻¹ * x⁻¹ ∈ A₁ ⊔ conjSub a A₁ := by
    rw [sup_comm]
    exact Subgroup.mul_mem_sup (mem_conjSub_of_mem hx) (A₁.inv_mem hx)
  have hy1 : a * x * a⁻¹ * x⁻¹ ≠ 1 := by
    intro hy
    apply hax
    have h1 : a * x * a⁻¹ = x := mul_inv_eq_one.1 hy
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]
  have hle : fixV (A₁ ⊔ conjSub a A₁) ≤ fixV A₂ := by
    have h1 : Subgroup.zpowers (a * x * a⁻¹ * x⁻¹) ≤ A₁ ⊔ conjSub a A₁ :=
      (Subgroup.zpowers_le).2 hy₁
    rw [← h.fixV_eq A₂ h₂ _ hy₂ hy1]
    exact fixV_anti h1
  have hAA : Nat.card A₁ = Nat.card A₂ := (h.four_seven_count h₁ h₂ ha hne hc).2.2 hle
  have hB : conjSub a A₁ ∈ D := h.conj_mem A₁ h₁ a (h.le A₂ h₂ ha)
  have hbot : A₁ ⊓ conjSub a A₁ = ⊥ := (h.eq_or_inf_eq_bot h₁ hB).resolve_left hne.symm
  have hcardB : Nat.card ↥(conjSub a A₁) = Nat.card A₁ := Glauberman.card_map_conj a A₁
  have hsupcard : Nat.card ↥(A₁ ⊔ conjSub a A₁) = Nat.card A₁ * Nat.card A₁ := by
    have := card_sup_mul_card_inf' hc
    rwa [hbot, Subgroup.card_bot, mul_one, hcardB] at this
  have hup := card_sup_le_mul_of_le_normalizer
    (show A₁ ≤ Subgroup.normalizer (A₂ : Set (MulAut V)) from fun b hb =>
      mem_normalizer_of_conjSub_eq (hN b hb))
  have hle2 : A₁ ⊔ conjSub a A₁ ≤ A₁ ⊔ A₂ :=
    sup_le le_sup_left (Glauberman.map_conj_le (Subgroup.mem_sup_right ha) le_sup_left)
  refine hsm (Subgroup.eq_of_le_of_card_ge hle2 ?_)
  rw [hsupcard]
  calc Nat.card ↥(A₁ ⊔ A₂) ≤ Nat.card A₁ * Nat.card A₂ := hup
    _ = Nat.card A₁ * Nat.card A₁ := by rw [← hAA]

theorem four_seven_core_one (h : Hyp41 P D) {A₁ A₂ : Subgroup (MulAut V)} (h₁ : A₁ ∈ D)
    (h₂ : A₂ ∈ D)
    (hnc : ¬ ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    (hsm : ∀ a ∈ A₂, A₁ ⊔ conjSub a A₁ ≠ A₁ ⊔ A₂)
    (hc₁ : ∀ a ∈ A₂, ∀ x ∈ A₁, ∀ y ∈ conjSub a A₁, x * y = y * x)
    (hc₂ : ∀ b ∈ A₁, ∀ x ∈ A₂, ∀ y ∈ conjSub b A₂, x * y = y * x)
    {a : MulAut V} (ha : a ∈ A₂) (hne : conjSub a A₁ ≠ A₁) : False := by
  have hcnt₁ := h.four_seven_count h₁ h₂ ha hne (hc₁ a ha)
  obtain ⟨b, hb, hneb⟩ : ∃ b ∈ A₁, conjSub b A₂ ≠ A₂ := by
    by_contra hcon
    push Not at hcon
    exact h.four_seven_not_normalizes h₁ h₂ ha hne (hc₁ a ha) (hsm a ha) hcon
  have hcnt₂ := h.four_seven_count h₂ h₁ hb hneb (hc₂ b hb)
  exact hnc (commute_of_commV_le (hcnt₁.2.1 hcnt₂.1) (hcnt₂.2.1 hcnt₁.1))

theorem four_seven_core (h : Hyp41 P D) {A₁ A₂ : Subgroup (MulAut V)} (h₁ : A₁ ∈ D) (h₂ : A₂ ∈ D)
    (hnc : ¬ ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    (hsm₁ : ∀ a ∈ A₂, A₁ ⊔ conjSub a A₁ ≠ A₁ ⊔ A₂)
    (hsm₂ : ∀ b ∈ A₁, A₂ ⊔ conjSub b A₂ ≠ A₁ ⊔ A₂)
    (hc₁ : ∀ a ∈ A₂, ∀ x ∈ A₁, ∀ y ∈ conjSub a A₁, x * y = y * x)
    (hc₂ : ∀ b ∈ A₁, ∀ x ∈ A₂, ∀ y ∈ conjSub b A₂, x * y = y * x) : False := by
  by_cases hN₂ : ∃ a ∈ A₂, conjSub a A₁ ≠ A₁
  · obtain ⟨a, ha, hne⟩ := hN₂
    exact h.four_seven_core_one h₁ h₂ hnc hsm₁ hc₁ hc₂ ha hne
  by_cases hN₁ : ∃ b ∈ A₁, conjSub b A₂ ≠ A₂
  · obtain ⟨b, hb, hne⟩ := hN₁
    exact h.four_seven_core_one h₂ h₁ (fun H => hnc fun x hx y hy => (H y hy x hx).symm)
      (fun b hb heq => hsm₂ b hb (heq.trans (sup_comm A₂ A₁))) hc₂ hc₁ hb hne
  push Not at hN₁ hN₂
  apply hnc
  intro x hx y hy
  rcases h.eq_or_inf_eq_bot h₁ h₂ with heq | hbot
  · subst heq
    exact (h.elemAb _ h₁).1 x hx y hy
  · have hm₂ : x * y * x⁻¹ * y⁻¹ ∈ A₂ := by
      have h1 : x * y * x⁻¹ ∈ conjSub x A₂ := mem_conjSub_of_mem hy
      rw [hN₁ x hx] at h1
      exact A₂.mul_mem h1 (A₂.inv_mem hy)
    have hm₁ : x * y * x⁻¹ * y⁻¹ ∈ A₁ := by
      have h1 : y * x⁻¹ * y⁻¹ ∈ conjSub y A₁ := mem_conjSub_of_mem (A₁.inv_mem hx)
      rw [hN₂ y hy] at h1
      have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [this]
      exact A₁.mul_mem hx h1
    have h0 : x * y * x⁻¹ * y⁻¹ ∈ A₁ ⊓ A₂ := ⟨hm₁, hm₂⟩
    rw [hbot] at h0
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := h0
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]

theorem four_seven_pairs (h : Hyp41 P D) {T : Subgroup (MulAut V)} (hT : IsSylowOf 2 T P) :
    ∀ A₁ ∈ dInter D T, ∀ A₂ ∈ dInter D T, ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := by
  suffices H : ∀ n : ℕ, ∀ A₁ ∈ dInter D T, ∀ A₂ ∈ dInter D T, Nat.card ↥(A₁ ⊔ A₂) = n →
      ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x from
    fun A₁ h₁ A₂ h₂ => H _ A₁ h₁ A₂ h₂ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A₁ h₁ A₂ h₂ hn
  by_contra hnc
  obtain ⟨hD₁, hT₁⟩ := h₁
  obtain ⟨hD₂, hT₂⟩ := h₂
  have hLp : IsPGroup 2 ↥(A₁ ⊔ A₂) := hT.2.1.to_le (sup_le hT₁ hT₂)
  have hA₁L : A₁ ≠ A₁ ⊔ A₂ := by
    intro heq
    apply hnc
    intro x hx y hy
    have hy' : y ∈ A₁ := by rw [heq]; exact Subgroup.mem_sup_right hy
    exact (h.elemAb A₁ hD₁).1 x hx y hy'
  have hA₂L : A₂ ≠ A₁ ⊔ A₂ := by
    intro heq
    apply hnc
    intro x hx y hy
    have hx' : x ∈ A₂ := by rw [heq]; exact Subgroup.mem_sup_left hx
    exact (h.elemAb A₂ hD₂).1 x hx' y hy
  obtain ⟨M₁, hM₁A, hM₁L, hM₁ne, hM₁n⟩ := exists_normal_lt_of_isPGroup hLp le_sup_left hA₁L
  obtain ⟨M₂, hM₂A, hM₂L, hM₂ne, hM₂n⟩ := exists_normal_lt_of_isPGroup hLp le_sup_right hA₂L
  have hcj₁ : ∀ a ∈ A₂, conjSub a A₁ ≤ M₁ := by
    rintro a ha _ ⟨x, hx, rfl⟩
    exact hM₁n a (Subgroup.mem_sup_right ha) x (hM₁A hx)
  have hcj₂ : ∀ b ∈ A₁, conjSub b A₂ ≤ M₂ := by
    rintro b hb _ ⟨y, hy, rfl⟩
    exact hM₂n b (Subgroup.mem_sup_left hb) y (hM₂A hy)
  have hmem₁ : ∀ a ∈ A₂, conjSub a A₁ ∈ dInter D T := fun a ha =>
    ⟨h.conj_mem A₁ hD₁ a (h.le A₂ hD₂ ha), Glauberman.map_conj_le (hT₂ ha) hT₁⟩
  have hmem₂ : ∀ b ∈ A₁, conjSub b A₂ ∈ dInter D T := fun b hb =>
    ⟨h.conj_mem A₂ hD₂ b (h.le A₁ hD₁ hb), Glauberman.map_conj_le (hT₁ hb) hT₂⟩
  have hlt₁ : ∀ a ∈ A₂, Nat.card ↥(A₁ ⊔ conjSub a A₁) < n := fun a ha => by
    rw [← hn]
    exact lt_of_le_of_lt (Subgroup.card_le_of_le (sup_le hM₁A (hcj₁ a ha)))
      (card_lt_of_le_of_ne hM₁L hM₁ne)
  have hlt₂ : ∀ b ∈ A₁, Nat.card ↥(A₂ ⊔ conjSub b A₂) < n := fun b hb => by
    rw [← hn]
    exact lt_of_le_of_lt (Subgroup.card_le_of_le (sup_le hM₂A (hcj₂ b hb)))
      (card_lt_of_le_of_ne hM₂L hM₂ne)
  have hc₁ : ∀ a ∈ A₂, ∀ x ∈ A₁, ∀ y ∈ conjSub a A₁, x * y = y * x := fun a ha =>
    ih _ (hlt₁ a ha) A₁ ⟨hD₁, hT₁⟩ _ (hmem₁ a ha) rfl
  have hc₂ : ∀ b ∈ A₁, ∀ x ∈ A₂, ∀ y ∈ conjSub b A₂, x * y = y * x := fun b hb =>
    ih _ (hlt₂ b hb) A₂ ⟨hD₂, hT₂⟩ _ (hmem₂ b hb) rfl
  have hsm₁ : ∀ a ∈ A₂, A₁ ⊔ conjSub a A₁ ≠ A₁ ⊔ A₂ := fun a ha heq => by
    have : A₁ ⊔ A₂ ≤ M₁ := by rw [← heq]; exact sup_le hM₁A (hcj₁ a ha)
    exact hM₁ne (le_antisymm hM₁L this)
  have hsm₂ : ∀ b ∈ A₁, A₂ ⊔ conjSub b A₂ ≠ A₁ ⊔ A₂ := fun b hb heq => by
    have : A₁ ⊔ A₂ ≤ M₂ := by rw [← heq]; exact sup_le hM₂A (hcj₂ b hb)
    exact hM₂ne (le_antisymm hM₂L this)
  exact h.four_seven_core hD₁ hD₂ hnc hsm₁ hsm₂ hc₁ hc₂

theorem four_seven_isElemAbelian2 (h : Hyp41 P D) {T : Subgroup (MulAut V)}
    (hT : IsSylowOf 2 T P) : IsElemAbelian2 (⨆ A ∈ dInter D T, A) := by
  rw [← sSup_eq_iSup]
  have hcomm := comm_of_mem_sSup (F := dInter D T) (h.four_seven_pairs hT)
  exact ⟨hcomm, sq_eq_one_of_mem_sSup hcomm fun A hA x hx => (h.elemAb A hA.1).2 x hx⟩

theorem four_seven_isQuadratic (h : Hyp41 P D) {T : Subgroup (MulAut V)} (hT : IsSylowOf 2 T P) :
    IsQuadratic (⨆ A ∈ dInter D T, A) := by
  rw [← sSup_eq_iSup]
  have hpairs := h.four_seven_pairs hT
  have hcv : ∀ A ∈ dInter D T, ∀ B ∈ dInter D T, commV A ≤ fixV B := by
    intro A hA B hB
    by_cases hAB : A = B
    · subst hAB
      exact h.quad A hA.1
    · exact (h.commV_le_fixV_inf hA.1 hB.1 hAB (hpairs A hA B hB)).trans inf_le_right
  show commV (sSup (dInter D T)) ≤ fixV (sSup (dInter D T))
  rw [B19.commV_le_iff]
  refine sSup_le fun A hA => ?_
  rw [← B19.commV_le_iff]
  exact le_fixV_sSup fun B hB => hcv A hA B hB

end Hyp41

end CFSG.CGT.PushingUpLit.BHS
