module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartSwap

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Equiv.Perm Subgroup

section Pointwise

variable {β : Type*} [DecidableEq β]

theorem eq_one_or_eq_of_fixes_compl {p q : β} (hpq : p ≠ q) {f : Perm β}
    (hf : ∀ x, x ≠ p → x ≠ q → f x = x) : f = 1 ∨ f = swap p q := by
  have hfp : f p = p ∨ f p = q := by
    by_contra hcon
    push Not at hcon
    exact hcon.1 (f.injective (hf (f p) hcon.1 hcon.2))
  have hfq : f q = p ∨ f q = q := by
    by_contra hcon
    push Not at hcon
    exact hcon.2 (f.injective (hf (f q) hcon.1 hcon.2))
  rcases hfp with h1 | h1
  · have h2 : f q = q := by
      rcases hfq with h2 | h2
      · exact absurd (f.injective (h2.trans h1.symm)) (Ne.symm hpq)
      · exact h2
    left
    ext x
    by_cases hxp : x = p
    · subst hxp; simpa using h1
    · by_cases hxq : x = q
      · subst hxq; simpa using h2
      · simpa using hf x hxp hxq
  · have h2 : f q = p := by
      rcases hfq with h2 | h2
      · exact h2
      · exact absurd (f.injective (h2.trans h1.symm)) (Ne.symm hpq)
    right
    ext x
    by_cases hxp : x = p
    · subst hxp; simpa using h1
    · by_cases hxq : x = q
      · subst hxq; simpa using h2
      · rw [swap_apply_of_ne_of_ne hxp hxq]
        exact hf x hxp hxq

theorem fixes_of_comm_swap {τ τ' : Perm β} (hτ : τ.IsSwap) (hτ' : τ'.IsSwap)
    (hc : τ' * τ = τ * τ') (hne : τ' ≠ τ) {x : β} (hx : τ x ≠ x) : τ' x = x := by
  obtain ⟨p, q, hpq, rfl⟩ := hτ
  obtain ⟨r, t, hrt, rfl⟩ := hτ'
  have hp := congrArg (fun g : Perm β => g p) hc
  have hq := congrArg (fun g : Perm β => g q) hc
  have hr := congrArg (fun g : Perm β => g r) hc
  have ht := congrArg (fun g : Perm β => g t) hc
  simp only [Perm.mul_apply] at hp hq hr ht
  by_contra hcon
  have hne' : swap r t ≠ swap p q := hne
  rw [swap_apply_def] at hx hcon
  rw [swap_apply_def] at hp hq hr ht
  simp only [swap_apply_def] at hp hq hr ht
  grind

end Pointwise

section Embedding

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype β] [DecidableEq β] in
theorem fix_iff_of_comm {τ f : Perm β} (hf : f * τ = τ * f) (x : β) :
    τ (f x) = f x ↔ τ x = x := by
  have h1 : τ (f x) = f (τ x) := by
    have := congrArg (fun g : Perm β => g x) hf
    simpa using this.symm
  rw [h1, f.injective.eq_iff]

@[expose] noncomputable def restrictFix (Ψ : Perm α →* Perm β) {τ : Perm β}
    (hcomm : ∀ π, Ψ π * τ = τ * Ψ π) : Perm α →* Perm {x // τ x = x} where
  toFun π := (Ψ π).subtypePerm (fun x => fix_iff_of_comm (hcomm π) x)
  map_one' := by
    ext x
    simp
  map_mul' π₁ π₂ := by
    ext x
    show Ψ (π₁ * π₂) (x : β) = Ψ π₁ (Ψ π₂ (x : β))
    rw [map_mul]
    rfl

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem restrictFix_apply (Ψ : Perm α →* Perm β) {τ : Perm β}
    (hcomm : ∀ π, Ψ π * τ = τ * Ψ π) (π : Perm α) (x : {x // τ x = x}) :
    ((restrictFix Ψ hcomm π x : {x // τ x = x}) : β) = Ψ π x := rfl

theorem card_fix_swap {τ : Perm β} (hτ : τ.IsSwap) :
    Fintype.card {x // τ x = x} = Fintype.card β - 2 := by
  have h1 := Equiv.Perm.card_fixedPoints τ
  rw [Equiv.Perm.isSwap_iff_cycleType.1 hτ] at h1
  have h2 : Fintype.card {x // τ x = x} = Fintype.card (Function.fixedPoints τ) :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  rw [h2, h1]
  simp

theorem restrictFix_bijective (hαβ : Fintype.card β = Fintype.card α + 2)
    (Ψ : Perm α →* Perm β) (hinj : Function.Injective Ψ) {τ : Perm β} (hτ : τ.IsSwap)
    (hcomm : ∀ π, Ψ π * τ = τ * Ψ π) (hne : ∀ π, Ψ π ≠ τ) :
    Function.Bijective (restrictFix Ψ hcomm) := by
  classical
  have hcard : Fintype.card {x // τ x = x} = Fintype.card α := by
    rw [card_fix_swap hτ]; omega
  have hPinj : Function.Injective (restrictFix Ψ hcomm) := by
    rw [injective_iff_map_eq_one]
    intro π hπ
    have hfix : ∀ x, τ x = x → Ψ π x = x := by
      intro x hx
      have := congrArg (fun g : Perm {x // τ x = x} => (g ⟨x, hx⟩ : β)) hπ
      simpa [restrictFix_apply] using this
    obtain ⟨a, b, hab, hτe⟩ := hτ
    have hfix' : ∀ x, x ≠ a → x ≠ b → Ψ π x = x := fun x hxa hxb =>
      hfix x (by rw [hτe]; exact swap_apply_of_ne_of_ne hxa hxb)
    rcases eq_one_or_eq_of_fixes_compl hab hfix' with h1 | h1
    · exact hinj (by rw [h1, map_one])
    · exact absurd (h1.trans hτe.symm) (hne π)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hPinj, ?_⟩
  rw [Fintype.card_perm, Fintype.card_perm, hcard]

theorem isSwap_of_embedding (hαβ : Fintype.card β = Fintype.card α + 2) (hα : 7 ≤ Fintype.card α)
    (Ψ : Perm α →* Perm β) (hinj : Function.Injective Ψ) {τ : Perm β} (hτ : τ.IsSwap)
    (hcomm : ∀ π, Ψ π * τ = τ * Ψ π) (hne : ∀ π, Ψ π ≠ τ) {τ' : Perm β} (hτ' : τ'.IsSwap)
    (hτ'c : τ' * τ = τ * τ') (hτ'ne : τ' ≠ τ) {σ : Perm α}
    (hσ : Ψ σ = τ' ∨ Ψ σ = τ * τ') : σ.IsSwap := by
  classical
  set P : Perm α →* Perm {x // τ x = x} := restrictFix Ψ hcomm with hP
  have hcard : Fintype.card {x // τ x = x} = Fintype.card α := by
    rw [card_fix_swap hτ]; omega
  have hPbij : Function.Bijective P := restrictFix_bijective hαβ Ψ hinj hτ hcomm hne
  let Pe : Perm α ≃* Perm {x // τ x = x} := MulEquiv.ofBijective P hPbij
  have hτ'fix : ∀ x, τ x ≠ x → τ' x = x := fun x hx => fixes_of_comm_swap hτ hτ' hτ'c hτ'ne hx
  have hswap : (P σ).IsSwap := by
    obtain ⟨r, t, hrt, hτ'e⟩ := hτ'
    have hr : τ r = r := by
      by_contra hcon
      have := hτ'fix r hcon
      rw [hτ'e, swap_apply_left] at this
      exact hrt this.symm
    have ht : τ t = t := by
      by_contra hcon
      have := hτ'fix t hcon
      rw [hτ'e, swap_apply_right] at this
      exact hrt this
    have hval : ∀ x : {x // τ x = x}, Ψ σ x = swap r t x := by
      intro x
      rcases hσ with h | h
      · rw [h, hτ'e]
      · rw [h, Perm.mul_apply, hτ'e]
        by_cases hxr : (x : β) = r
        · rw [hxr, swap_apply_left]; exact ht
        · by_cases hxt : (x : β) = t
          · rw [hxt, swap_apply_right]; exact hr
          · rw [swap_apply_of_ne_of_ne hxr hxt]; exact x.2
    refine ⟨⟨r, hr⟩, ⟨t, ht⟩, ?_, ?_⟩
    · intro h
      exact hrt (by simpa using congrArg Subtype.val h)
    · ext ⟨x, hx⟩
      show Ψ σ x = ((swap (⟨r, hr⟩ : {x // τ x = x}) ⟨t, ht⟩ ⟨x, hx⟩ : {x // τ x = x}) : β)
      rw [hval ⟨x, hx⟩]
      by_cases hxr : x = r
      · subst hxr
        simp
      · by_cases hxt : x = t
        · subst hxt
          simp
        · rw [swap_apply_of_ne_of_ne hxr hxt, swap_apply_of_ne_of_ne]
          · intro h; exact hxr (by simpa using congrArg Subtype.val h)
          · intro h; exact hxt (by simpa using congrArg Subtype.val h)
  have := isSwap_map_of_mulEquiv Pe.symm hcard (by omega) hswap
  have h2 : Pe.symm (P σ) = σ := Pe.symm_apply_apply σ
  rwa [h2] at this

theorem embedding_swap_cases (hαβ : Fintype.card β = Fintype.card α + 2)
    (hα : 7 ≤ Fintype.card α) (Ψ : Perm α →* Perm β) (hinj : Function.Injective Ψ) {τ : Perm β}
    (hτ : τ.IsSwap) (hcomm : ∀ π, Ψ π * τ = τ * Ψ π) (hne : ∀ π, Ψ π ≠ τ) {σ : Perm α}
    (hσ : σ.IsSwap) :
    ∃ τ' : Perm β, τ'.IsSwap ∧ τ' * τ = τ * τ' ∧ τ' ≠ τ ∧ (Ψ σ = τ' ∨ Ψ σ = τ * τ') := by
  classical
  set P : Perm α →* Perm {x // τ x = x} := restrictFix Ψ hcomm with hP
  have hcard : Fintype.card {x // τ x = x} = Fintype.card α := by
    rw [card_fix_swap hτ]; omega
  have hPbij : Function.Bijective P := restrictFix_bijective hαβ Ψ hinj hτ hcomm hne
  let Pe : Perm α ≃* Perm {x // τ x = x} := MulEquiv.ofBijective P hPbij
  have hPσ : (P σ).IsSwap := isSwap_map_of_mulEquiv Pe hcard.symm (by omega) hσ
  obtain ⟨r, t, hrt, hrte⟩ := hPσ
  obtain ⟨p, q, hpq, hτe⟩ := hτ
  have hr : τ r = r := r.2
  have ht : τ t = t := t.2
  have hrp : (r : β) ≠ p := fun h' => by rw [h', hτe, swap_apply_left] at hr; exact hpq hr.symm
  have hrq : (r : β) ≠ q := fun h' => by rw [h', hτe, swap_apply_right] at hr; exact hpq hr
  have htp : (t : β) ≠ p := fun h' => by rw [h', hτe, swap_apply_left] at ht; exact hpq ht.symm
  have htq : (t : β) ≠ q := fun h' => by rw [h', hτe, swap_apply_right] at ht; exact hpq ht
  have hrt' : (r : β) ≠ t := fun h' => hrt (Subtype.ext h')
  set τ' : Perm β := swap (r : β) (t : β) with hτ'
  have hfix : ∀ x : β, τ x = x → Ψ σ x = τ' x := by
    intro x hx
    have h1 := congrArg (fun g : Perm {x // τ x = x} => (g ⟨x, hx⟩ : β)) hrte
    simp only [hP, restrictFix_apply] at h1
    rw [h1, hτ']
    by_cases hxr : x = r
    · subst hxr
      simp
    · by_cases hxt : x = t
      · subst hxt
        simp
      · rw [swap_apply_of_ne_of_ne (fun h' => hxr (congrArg Subtype.val h'))
          (fun h' => hxt (congrArg Subtype.val h')), swap_apply_of_ne_of_ne hxr hxt]
  have hcσ := hcomm σ
  have hΨp : Ψ σ p = p ∨ Ψ σ p = q := by
    have h1 := congrArg (fun g : Perm β => g p) hcσ
    simp only [Perm.mul_apply, hτe, swap_apply_left] at h1
    by_contra hcon
    push Not at hcon
    rw [swap_apply_of_ne_of_ne hcon.1 hcon.2] at h1
    exact hpq ((Ψ σ).injective h1).symm
  have hτ'c : τ' * swap p q = swap p q * τ' :=
    Perm.Disjoint.commute (fun x => by
      by_cases hx : x = r ∨ x = t
      · right
        rcases hx with rfl | rfl
        · exact swap_apply_of_ne_of_ne hrp hrq
        · exact swap_apply_of_ne_of_ne htp htq
      · push Not at hx
        exact Or.inl (swap_apply_of_ne_of_ne hx.1 hx.2))
  refine ⟨τ', ⟨r, t, hrt', rfl⟩, by rw [hτe]; exact hτ'c, ?_, ?_⟩
  · intro h'
    have := congrArg (fun g : Perm β => g p) h'
    simp only [hτ', swap_apply_of_ne_of_ne hrp.symm htp.symm, hτe, swap_apply_left] at this
    exact hpq this
  · have hfixpq : ∀ x, x ≠ p → x ≠ q → τ x = x := fun x hxp hxq => by
      rw [hτe]; exact swap_apply_of_ne_of_ne hxp hxq
    have hqp : Ψ σ q = swap p q (Ψ σ p) := by
      have h2 := congrArg (fun g : Perm β => g p) hcσ
      simp only [Perm.mul_apply, hτe, swap_apply_left] at h2
      exact h2
    rcases hΨp with h1 | h1
    · left
      have hq : Ψ σ q = q := by rw [hqp, h1, swap_apply_left]
      ext x
      by_cases hxp : x = p
      · subst hxp; rw [h1, hτ', swap_apply_of_ne_of_ne hrp.symm htp.symm]
      · by_cases hxq : x = q
        · subst hxq; rw [hq, hτ', swap_apply_of_ne_of_ne hrq.symm htq.symm]
        · rw [hfix x (hfixpq x hxp hxq)]
    · right
      have hq : Ψ σ q = p := by rw [hqp, h1, swap_apply_right]
      ext x
      by_cases hxp : x = p
      · subst hxp
        rw [h1, Perm.mul_apply, hτ', swap_apply_of_ne_of_ne hrp.symm htp.symm, hτe,
          swap_apply_left]
      · by_cases hxq : x = q
        · subst hxq
          rw [hq, Perm.mul_apply, hτ', swap_apply_of_ne_of_ne hrq.symm htq.symm, hτe,
            swap_apply_right]
        · have hτ'x : τ' x ≠ p ∧ τ' x ≠ q := by
            by_cases hxr : x = r
            · subst hxr; rw [hτ', swap_apply_left]; exact ⟨htp, htq⟩
            · by_cases hxt : x = t
              · subst hxt; rw [hτ', swap_apply_right]; exact ⟨hrp, hrq⟩
              · rw [hτ', swap_apply_of_ne_of_ne hxr hxt]; exact ⟨hxp, hxq⟩
          rw [hfix x (hfixpq x hxp hxq), Perm.mul_apply, hfixpq _ hτ'x.1 hτ'x.2]

end Embedding

end CFSG.OddStandard.AltStdSec
