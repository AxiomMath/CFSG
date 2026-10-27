module

public import CFSG.CGT.PushingUpLit.BHS.FourOneA

public section

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne
open FourOneTools

namespace Hyp41

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))}

theorem eq_or_inf_eq_bot (h : Hyp41 P D) {A B : Subgroup (MulAut V)} (hA : A ∈ D)
    (hB : B ∈ D) : A = B ∨ A ⊓ B = ⊥ := by
  by_cases hAB : A = B
  · exact Or.inl hAB
  refine Or.inr (Subgroup.eq_bot_iff_forall _ |>.2 fun x hx => ?_)
  by_contra hx1
  have hf : fixV A = fixV B :=
    (h.fixV_eq A hA x hx.1 hx1).symm.trans (h.fixV_eq B hB x hx.2 hx1)
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
    commute_of_commV_le ((h.quad A hA).trans hf.le) ((h.quad B hB).trans hf.ge)
  have hcard := h.card_prod A hA B hB (Ne.symm hAB) hcomm
  rw [fixV_sup, ← hf, inf_idem] at hcard
  have hAeq := h.card_eq A hA
  have hpos : 0 < Nat.card A * Nat.card (fixV A) := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hB1 : Nat.card B = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card A * Nat.card (fixV A) * Nat.card B
        = Nat.card A * Nat.card B * Nat.card (fixV A) := by ring
      _ = Nat.card V := hcard.symm
      _ = Nat.card A * Nat.card (fixV A) * 1 := by rw [hAeq]; ring
  exact h.ne_bot B hB (Subgroup.eq_bot_of_card_eq B hB1)

theorem sup_fixV_eq_top (h : Hyp41 P D) {A B : Subgroup (MulAut V)} (hA : A ∈ D) (hB : B ∈ D)
    (hne : A ≠ B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : fixV A ⊔ fixV B = ⊤ := by
  have hcard := h.card_prod A hA B hB (Ne.symm hne) hcomm
  rw [fixV_sup] at hcard
  have hAeq := h.card_eq A hA
  have hBeq := h.card_eq B hB
  have hprod := card_sup_mul_card_inf' (X := fixV A) (Y := fixV B) fun x _ y _ => mul_comm x y
  have hb : 0 < Nat.card B := Nat.card_pos
  have hi : 0 < Nat.card ↥(fixV A ⊓ fixV B) := Nat.card_pos
  have h1 : Nat.card (fixV B) = Nat.card A * Nat.card ↥(fixV A ⊓ fixV B) := by
    refine Nat.eq_of_mul_eq_mul_left hb ?_
    calc Nat.card B * Nat.card (fixV B) = Nat.card V := hBeq.symm
      _ = Nat.card A * Nat.card B * Nat.card ↥(fixV A ⊓ fixV B) := hcard
      _ = Nat.card B * (Nat.card A * Nat.card ↥(fixV A ⊓ fixV B)) := by ring
  refine Subgroup.eq_top_of_card_eq _ ?_
  refine Nat.eq_of_mul_eq_mul_right hi ?_
  calc Nat.card ↥(fixV A ⊔ fixV B) * Nat.card ↥(fixV A ⊓ fixV B)
      = Nat.card (fixV A) * Nat.card (fixV B) := hprod
    _ = Nat.card (fixV A) * (Nat.card A * Nat.card ↥(fixV A ⊓ fixV B)) := by rw [h1]
    _ = Nat.card V * Nat.card ↥(fixV A ⊓ fixV B) := by rw [hAeq]; ring

theorem commV_le_fixV_inf (h : Hyp41 P D) {A B : Subgroup (MulAut V)} (hA : A ∈ D)
    (hB : B ∈ D) (hne : A ≠ B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    commV A ≤ fixV A ⊓ fixV B :=
  le_inf (h.quad A hA)
    (commV_le_fixV_of_sup_eq_top hcomm (h.sup_fixV_eq_top hA hB hne hcomm))

theorem isQuadratic_sup (h : Hyp41 P D) {A B : Subgroup (MulAut V)} (hA : A ∈ D) (hB : B ∈ D)
    (hne : A ≠ B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsQuadratic (A ⊔ B) := by
  show commV (A ⊔ B) ≤ fixV (A ⊔ B)
  rw [B19.commV_sup, fixV_sup]
  refine sup_le (h.commV_le_fixV_inf hA hB hne hcomm) ?_
  rw [inf_comm]
  exact h.commV_le_fixV_inf hB hA hne.symm fun b hb a ha => (hcomm a ha b hb).symm

theorem card_mul_card_inf_fixV (h : Hyp41 P D) {A B : Subgroup (MulAut V)} (hB : B ∈ D)
    (hsup : fixV A ⊔ fixV B = ⊤) :
    Nat.card B * Nat.card ↥(fixV A ⊓ fixV B) = Nat.card (fixV A) := by
  have hprod := card_sup_mul_card_inf' (X := fixV A) (Y := fixV B) fun x _ y _ => mul_comm x y
  rw [hsup, Subgroup.card_top, h.card_eq B hB] at hprod
  have hc : 0 < Nat.card (fixV B) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hc ?_
  calc Nat.card B * Nat.card ↥(fixV A ⊓ fixV B) * Nat.card (fixV B)
      = Nat.card B * Nat.card (fixV B) * Nat.card ↥(fixV A ⊓ fixV B) := by ring
    _ = Nat.card (fixV A) * Nat.card (fixV B) := hprod

theorem four_seven_count (h : Hyp41 P D) {A₁ A₂ : Subgroup (MulAut V)} (h₁ : A₁ ∈ D)
    (h₂ : A₂ ∈ D) {a : MulAut V} (ha : a ∈ A₂) (hne : conjSub a A₁ ≠ A₁)
    (hc : ∀ x ∈ A₁, ∀ y ∈ conjSub a A₁, x * y = y * x) :
    Nat.card A₁ ≤ Nat.card A₂ ∧ (Nat.card A₂ ≤ Nat.card A₁ → commV A₁ ≤ fixV A₂) ∧
      (fixV (A₁ ⊔ conjSub a A₁) ≤ fixV A₂ → Nat.card A₁ = Nat.card A₂) := by
  have hB : conjSub a A₁ ∈ D := h.conj_mem A₁ h₁ a (h.le A₂ h₂ ha)
  have hsup : fixV A₁ ⊔ fixV (conjSub a A₁) = ⊤ := h.sup_fixV_eq_top h₁ hB hne.symm hc
  have hfixB : fixV (conjSub a A₁) = (fixV A₁).map a.toMonoidHom :=
    Glauberman.fixV_map_conj a A₁
  have hincl : fixV A₁ ⊓ fixV A₂ ≤ fixV A₁ ⊓ fixV (conjSub a A₁) := by
    rintro v ⟨hv₁, hv₂⟩
    refine ⟨hv₁, ?_⟩
    rw [hfixB]
    exact ⟨v, hv₁, hv₂ a ha⟩
  have hq₂ : commV A₂ ≤ fixV A₂ := h.quad A₂ h₂
  have hsup₂ : fixV A₁ ⊔ fixV A₂ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ fixV A₁ ⊔ fixV (conjSub a A₁) := by rw [hsup]; exact Subgroup.mem_top v
    obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [hfixB] at hq
    obtain ⟨c, hcmem, hcq⟩ := hq
    have hq' : q = a c := hcq.symm
    rw [hq']
    have e : p * a c = p * c * (a c * c⁻¹) := by comm_group
    rw [e]
    exact Subgroup.mul_mem_sup ((fixV A₁).mul_mem hp hcmem) (hq₂ (G6.mem_commV_of_mem ha c))
  have e₂ := h.card_mul_card_inf_fixV h₂ hsup₂
  have e₁ := h.card_mul_card_inf_fixV hB hsup
  rw [show Nat.card ↥(conjSub a A₁) = Nat.card A₁ from Glauberman.card_map_conj a A₁] at e₁
  have hpos₁ : 0 < Nat.card ↥(fixV A₁ ⊓ fixV (conjSub a A₁)) := Nat.card_pos
  have hposA : 0 < Nat.card A₁ := Nat.card_pos
  have hle₁ : Nat.card A₁ ≤ Nat.card A₂ := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos₁
    calc Nat.card A₁ * Nat.card ↥(fixV A₁ ⊓ fixV (conjSub a A₁))
        = Nat.card A₂ * Nat.card ↥(fixV A₁ ⊓ fixV A₂) := by rw [e₁, e₂]
      _ ≤ Nat.card A₂ * Nat.card ↥(fixV A₁ ⊓ fixV (conjSub a A₁)) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hincl)
  refine ⟨hle₁, fun hge => ?_, fun hle' => ?_⟩
  · have hAA : Nat.card A₂ = Nat.card A₁ := le_antisymm hge hle₁
    rw [hAA] at e₂
    have hii : Nat.card ↥(fixV A₁ ⊓ fixV (conjSub a A₁)) = Nat.card ↥(fixV A₁ ⊓ fixV A₂) :=
      Nat.eq_of_mul_eq_mul_left hposA (e₁.trans e₂.symm)
    have heq := Subgroup.eq_of_le_of_card_ge hincl hii.le
    exact (h.commV_le_fixV_inf h₁ hB hne.symm hc).trans (by rw [← heq]; exact inf_le_right)
  · rw [fixV_sup] at hle'
    have heq : fixV A₁ ⊓ fixV A₂ = fixV A₁ ⊓ fixV (conjSub a A₁) :=
      le_antisymm hincl (le_inf inf_le_left hle')
    have hii : Nat.card ↥(fixV A₁ ⊓ fixV A₂) = Nat.card ↥(fixV A₁ ⊓ fixV (conjSub a A₁)) := by
      rw [heq]
    rw [hii] at e₂
    exact Nat.eq_of_mul_eq_mul_right hpos₁ (e₁.trans e₂.symm)

end Hyp41

end CFSG.CGT.PushingUpLit.BHS
