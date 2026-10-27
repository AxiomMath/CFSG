module

public import CFSG.GH74.GLS.Stage2.Local.P27.L4Defs
public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Cls

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.S45

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_sup_two_invol {t w : G} (ht2 : t * t = 1) (hw2 : w * w = 1) (htw : t * w = w * t)
    {x : G} (hx : x ∈ zpowers t ⊔ zpowers w) : x = 1 ∨ x = t ∨ x = w ∨ x = t * w := by
  have hconj : ∀ k ∈ zpowers t, w * k * w⁻¹ ∈ zpowers t := by
    intro k hk
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
    have hc : Commute w t := htw.symm
    have : w * t ^ n * w⁻¹ = t ^ n := by
      rw [(hc.zpow_right n).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hk
  have hsq : w * w ∈ zpowers t := by rw [hw2]; exact one_mem _
  have hone : ∀ y ∈ zpowers t, y = 1 ∨ y = t := by
    intro y hy
    have hconj' : ∀ k ∈ (⊥ : Subgroup G), t * k * t⁻¹ ∈ (⊥ : Subgroup G) := by
      intro k hk; rw [mem_bot] at hk; subst hk; simp
    have hsq' : t * t ∈ (⊥ : Subgroup G) := by rw [ht2]; exact one_mem _
    have : y ∈ (⊥ : Subgroup G) ⊔ zpowers t := by rwa [bot_sup_eq]
    rcases (Psp4.mem_sup_zpowers_iff hconj' hsq').1 this with h | ⟨k, hk, rfl⟩
    · left; exact mem_bot.1 h
    · right; rw [mem_bot.1 hk, one_mul]
  rcases (Psp4.mem_sup_zpowers_iff hconj hsq).1 hx with h | ⟨k, hk, rfl⟩
  · rcases hone x h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases hone k hk with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (one_mul _)))
    · exact Or.inr (Or.inr (Or.inr rfl))

variable [Finite G]

theorem relIndex_ne_zero' {H K : Subgroup G} : H.relIndex K ≠ 0 := by
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem l4_S_structure {S R : Subgroup G} {t w : G}
    (hRS : R ≤ S) (hnorm : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) (ht : t ∈ S) (hw : w ∈ S)
    (ht2 : t * t = 1) (hw2 : w * w = 1) (htw : t * w = w * t) (htR : t ∉ R)
    (hwRt : w ∉ R ⊔ zpowers t) (hidx : R.relIndex S ≤ 4) :
    R.relIndex S = 4 ∧ R ⊓ (zpowers t ⊔ zpowers w) = ⊥ ∧ S = R ⊔ (zpowers t ⊔ zpowers w) := by
  have hconj_t : ∀ k ∈ R, t * k * t⁻¹ ∈ R := fun k hk => hnorm t ht k hk
  have hsq_t : t * t ∈ R := by rw [ht2]; exact one_mem _
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hwR : w ∉ R := fun h => hwRt (mem_sup_left h)
  have htwR : t * w ∉ R := by
    intro h
    apply hwRt
    have e : (t * (t * w) * t) * t = w := by
      calc (t * (t * w) * t) * t = (t * t) * w * (t * t) := by simp only [mul_assoc]
        _ = w := by rw [ht2, one_mul, mul_one]
    rw [← e]
    have := hconj_t _ h
    rw [hti] at this
    exact mul_mem (mem_sup_left this) (mem_sup_right (mem_zpowers t))
  have hNS : R ⊔ zpowers t ≤ S := sup_le hRS ((zpowers_le).2 ht)
  have hRN : R ≤ R ⊔ zpowers t := le_sup_left
  have h1 : R.relIndex (R ⊔ zpowers t) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨t, mem_sup_right (mem_zpowers t), fun b hb => ?_⟩
    rcases (Psp4.mem_sup_zpowers_iff hconj_t hsq_t).1 hb with hbR | ⟨k, hk, rfl⟩
    · refine Or.inr ⟨hbR, fun hbt => htR ?_⟩
      have := mul_mem (inv_mem hbR) hbt
      simpa using this
    · refine Or.inl ⟨?_, fun hkt => htR ?_⟩
      · rw [mul_assoc, ht2, mul_one]; exact hk
      · have := mul_mem (inv_mem hk) hkt
        simpa using this
  have h2 : (R ⊔ zpowers t).relIndex S ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hwRt (h hw)
  have hmul := Subgroup.relIndex_mul_relIndex R (R ⊔ zpowers t) S hRN hNS
  rw [h1] at hmul
  have hne0 : (R ⊔ zpowers t).relIndex S ≠ 0 := relIndex_ne_zero'
  have h4 : R.relIndex S = 4 := by omega
  have hN2 : (R ⊔ zpowers t).relIndex S = 2 := by omega
  have hNN' : R ⊔ zpowers t ≤ R ⊔ (zpowers t ⊔ zpowers w) :=
    sup_le le_sup_left (le_sup_of_le_right le_sup_left)
  have hN'S : R ⊔ (zpowers t ⊔ zpowers w) ≤ S :=
    sup_le hRS (sup_le ((zpowers_le).2 ht) ((zpowers_le).2 hw))
  have hmul2 := Subgroup.relIndex_mul_relIndex (R ⊔ zpowers t) (R ⊔ (zpowers t ⊔ zpowers w)) S
    hNN' hN'S
  have h5 : (R ⊔ zpowers t).relIndex (R ⊔ (zpowers t ⊔ zpowers w)) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hwRt (h (mem_sup_right (mem_sup_right (mem_zpowers w))))
  have h5' : (R ⊔ zpowers t).relIndex (R ⊔ (zpowers t ⊔ zpowers w)) ≠ 0 :=
    relIndex_ne_zero'
  have h6 : (R ⊔ (zpowers t ⊔ zpowers w)).relIndex S = 1 := by
    rw [hN2] at hmul2
    have hpos : 0 < (R ⊔ (zpowers t ⊔ zpowers w)).relIndex S :=
      Nat.pos_of_ne_zero relIndex_ne_zero'
    by_contra hne
    have : 2 ≤ (R ⊔ (zpowers t ⊔ zpowers w)).relIndex S := by omega
    have h7 : 2 ≤ (R ⊔ zpowers t).relIndex (R ⊔ (zpowers t ⊔ zpowers w)) := by omega
    nlinarith
  have hSeq : S = R ⊔ (zpowers t ⊔ zpowers w) :=
    le_antisymm (Subgroup.relIndex_eq_one.1 h6) hN'S
  refine ⟨h4, ?_, hSeq⟩
  rw [eq_bot_iff]
  rintro x ⟨hxR, hxV⟩
  rcases mem_sup_two_invol ht2 hw2 htw hxV with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact absurd hxR htR
  · exact absurd hxR hwR
  · exact absurd hxR htwR


section Classes

variable {z : G} {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
  {P₁ P₂ : Subgroup G} {a : ℕ} {t w x₀ : G}

theorem zcL_subset (d : L4.DataL4 S P₁ P₂ z t w a) (hP : P₁ ⊔ P₂ = RC S z) (htz : IsConj z t)
    (htw : IsConj z (t * w))
    (hcos : ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w) → IsConj z y) :
    ∀ y, y ∈ L4.ZcL (P₁ ⊔ P₂) z t w → IsConj z y := by
  rintro y (((hyz | ⟨r, -, rfl⟩) | ⟨⟨r, hr, rfl⟩, hy2⟩) | ⟨r, -, rfl⟩)
  · rw [Set.mem_singleton_iff.mp hyz]
  · exact htz.trans (isConj_iff.2 ⟨r, rfl⟩)
  · refine hcos _ (mul_mem (d.R_mem_S hr) d.w_mem) hy2 ?_ ⟨r, hP ▸ hr, rfl⟩
    intro h1
    apply d.w_not
    have : w = r⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact inv_mem hr
  · exact htw.trans (isConj_iff.2 ⟨r, rfl⟩)

theorem xcL_subset (d : L4.DataL4 S P₁ P₂ z t w a) (hP : P₁ ⊔ P₂ = RC S z)
    (hx : TwoClassData G z S L₁ L₂ q x₀) (htz : IsConj z t) (hsw : Swaps z t L₁ L₂)
    (htwx : IsConj x₀ (t * w * z)) :
    ∀ y, y ∈ L4.XcL (P₁ ⊔ P₂) z t w → IsConj x₀ y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro y ((⟨hyR, hy2, hy1, hyz⟩ | ⟨r, -, rfl⟩) | ⟨r, -, rfl⟩)
  · have hord : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
    have hyL : y ∈ LC z := by
      have : y ∈ RC S z := hP ▸ hyR
      exact this.2
    exact (hx.invol_L y hyL hord hyz).1
  · exact (hx.swap_conseq t d.t_mem htz hsw).1.trans (isConj_iff.2 ⟨r, rfl⟩)
  · exact htwx.trans (isConj_iff.2 ⟨r, rfl⟩)

theorem not_conj_both (hz : IsCentralInvolution z) (hx : TwoClassData G z S L₁ L₂ q x₀) {y : G}
    (h1 : IsConj z y) (h2 : IsConj x₀ y) : False :=
  hx.x_nonCentral (Psp4Stage1.isCentralInvolution_of_isConj hz (h1.trans h2.symm))

theorem isConj_iff_mem_traces_l4 (hz : IsCentralInvolution z) (d : L4.DataL4 S P₁ P₂ z t w a)
    (hP : P₁ ⊔ P₂ = RC S z) (hx : TwoClassData G z S L₁ L₂ q x₀) (htz : IsConj z t)
    (hsw : Swaps z t L₁ L₂) (_hwz : IsConj z w) (htw : IsConj z (t * w))
    (htwx : IsConj x₀ (t * w * z))
    (hcos : ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w) → IsConj z y)
    (hpart : ∀ y ∈ S, y * y = 1 → y ≠ 1 →
      (y ∈ L4.ZcL (P₁ ⊔ P₂) z t w ∨ y ∈ L4.XcL (P₁ ⊔ P₂) z t w) ∧
        ¬ (y ∈ L4.ZcL (P₁ ⊔ P₂) z t w ∧ y ∈ L4.XcL (P₁ ⊔ P₂) z t w)) :
    ∀ y ∈ S, y * y = 1 → y ≠ 1 →
      (IsConj z y ↔ y ∈ L4.ZcL (P₁ ⊔ P₂) z t w) ∧ (IsConj x₀ y ↔ y ∈ L4.XcL (P₁ ⊔ P₂) z t w) := by
  intro y hy hy2 hy1
  have hZ := zcL_subset d hP htz htw hcos y
  have hX := xcL_subset d hP hx htz hsw htwx y
  obtain ⟨hpart', -⟩ := hpart y hy hy2 hy1
  refine ⟨⟨fun hc => ?_, hZ⟩, ⟨fun hc => ?_, hX⟩⟩
  · rcases hpart' with h | h
    · exact h
    · exact absurd (not_conj_both hz hx hc (hX h)) id
  · rcases hpart' with h | h
    · exact absurd (not_conj_both hz hx (hZ h) hc) id
    · exact h

end Classes

end CFSG.GH74.GLS.Stage2.Local.P27.S45
