module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

section Pairs

variable {ν : ℕ}

@[expose] def framePairForm (a b c d : Fin ν) : ℤ :=
  (if a = c then 1 else 0) - (if a = d then 1 else 0) - (if b = c then 1 else 0) +
    (if b = d then 1 else 0)

theorem framePairForm_eq_one_iff {a b c d : Fin ν} (hab : a ≠ b) (hcd : c ≠ d) :
    framePairForm a b c d = 1 ↔ (a = c ∧ b ≠ d) ∨ (b = d ∧ a ≠ c) := by
  unfold framePairForm
  by_cases h1 : a = c <;> by_cases h2 : a = d <;> by_cases h3 : b = c <;> by_cases h4 : b = d <;>
    simp only [h1, h2, h3, h4, ite_true, ite_false] <;> first | omega | (subst_vars; simp_all)

theorem framePairForm_eq_two_iff {a b c d : Fin ν} (hab : a ≠ b) (hcd : c ≠ d) :
    framePairForm a b c d = 2 ↔ a = c ∧ b = d := by
  unfold framePairForm
  by_cases h1 : a = c <;> by_cases h2 : a = d <;> by_cases h3 : b = c <;> by_cases h4 : b = d <;>
    simp only [h1, h2, h3, h4, ite_true, ite_false] <;> first | omega | (subst_vars; simp_all)

theorem pair_aut_cases (hν : 3 ≤ ν) (F : Fin ν → Fin ν → Fin ν × Fin ν)
    (hne : ∀ a b, a ≠ b → (F a b).1 ≠ (F a b).2)
    (hswap : ∀ a b, a ≠ b → F b a = ((F a b).2, (F a b).1))
    (hform : ∀ a b c d, a ≠ b → c ≠ d →
      framePairForm (F a b).1 (F a b).2 (F c d).1 (F c d).2 = framePairForm a b c d) :
    (∃ π : Equiv.Perm (Fin ν), ∀ a b, a ≠ b → F a b = (π a, π b)) ∨
      (∃ π : Equiv.Perm (Fin ν), ∀ a b, a ≠ b → F a b = (π b, π a)) := by
  classical
  have share : ∀ a b c, b ≠ a → c ≠ a → b ≠ c →
      ((F a b).1 = (F a c).1 ∧ (F a b).2 ≠ (F a c).2) ∨
        ((F a b).2 = (F a c).2 ∧ (F a b).1 ≠ (F a c).1) := by
    intro a b c hba hca hbc
    have h1 : framePairForm a b a c = 1 := (framePairForm_eq_one_iff hba.symm hca.symm).2
      (Or.inl ⟨rfl, hbc⟩)
    rw [← hform a b a c hba.symm hca.symm] at h1
    exact (framePairForm_eq_one_iff (hne a b hba.symm) (hne a c hca.symm)).1 h1
  have star : ∀ a, (∀ b c, b ≠ a → c ≠ a → (F a b).1 = (F a c).1) ∨
      (∀ b c, b ≠ a → c ≠ a → (F a b).2 = (F a c).2) := by
    intro a
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨b₀, c₀, hb₀, hc₀, h₀⟩, ⟨b₁, c₁, hb₁, hc₁, h₁⟩⟩ := hcon
    have hbc₀ : b₀ ≠ c₀ := fun h => h₀ (by rw [h])
    have hsec : (F a b₀).2 = (F a c₀).2 := by
      rcases share a b₀ c₀ hb₀ hc₀ hbc₀ with h | h
      · exact absurd h.1 h₀
      · exact h.1
    have hall : ∀ d, d ≠ a → (F a d).2 = (F a b₀).2 := by
      intro d hd
      by_cases hdb : d = b₀
      · rw [hdb]
      by_cases hdc : d = c₀
      · rw [hdc, hsec]
      rcases share a b₀ d hb₀ hd (Ne.symm hdb) with h | h
      · exfalso
        rcases share a c₀ d hc₀ hd (Ne.symm hdc) with h' | h'
        · exact h₀ (h.1.trans h'.1.symm)
        · exact h.2 (hsec.trans h'.1)
      · exact h.1.symm
    exact h₁ ((hall b₁ hb₁).trans (hall c₁ hc₁).symm)
  have third : ∀ a b : Fin ν, ∃ e, e ≠ a ∧ e ≠ b := by
    intro a b
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin ν)) ⊆ {a, b} := fun e _ => by
      by_cases hea : e = a
      · simp [hea]
      · simp [h e hea]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_insert_le a ({b} : Finset (Fin ν))
    rw [Finset.card_singleton] at h2
    omega
  have const : ∀ a b, a ≠ b → (∀ c d, c ≠ a → d ≠ a → (F a c).1 = (F a d).1) →
      (∀ c d, c ≠ b → d ≠ b → (F b c).2 = (F b d).2) → False := by
    intro a b hab ha hb
    obtain ⟨e, hea, heb⟩ := third a b
    have hu : (F b a).2 = (F a b).1 := by rw [hswap a b hab]
    have h1 := hform a e b e (Ne.symm hea) (Ne.symm heb)
    have h2 : framePairForm a e b e = 1 :=
      (framePairForm_eq_one_iff (Ne.symm hea) (Ne.symm heb)).2 (Or.inr ⟨rfl, hab⟩)
    have hae : (F a e).1 = (F a b).1 := ha e b hea (Ne.symm hab)
    have hbe : (F b e).2 = (F a b).1 := (hb e a heb hab).trans hu
    rw [h2] at h1
    rw [framePairForm_eq_one_iff (hne a e (Ne.symm hea)) (hne b e (Ne.symm heb))] at h1
    rcases h1 with h | h
    · exact hne b e (Ne.symm heb) (by rw [← h.1, hae, hbe])
    · exact hne a e (Ne.symm hea) (by rw [h.1, hae, hbe])
  have other : ∀ a : Fin ν, ∃ b, b ≠ a := fun a => by
    obtain ⟨e, he, -⟩ := third a a
    exact ⟨e, he⟩
  choose o ho using other
  by_cases hfirst : ∀ a, ∀ b c, b ≠ a → c ≠ a → (F a b).1 = (F a c).1
  ·
    left
    let π₀ : Fin ν → Fin ν := fun a => (F a (o a)).1
    have hπ : ∀ a b, a ≠ b → F a b = (π₀ a, π₀ b) := by
      intro a b hab
      have h1 : (F a b).1 = π₀ a := hfirst a b (o a) (Ne.symm hab) (ho a)
      have h2 : (F a b).2 = π₀ b := by
        have := hswap b a (Ne.symm hab)
        rw [this]
        exact hfirst b a (o b) hab (ho b)
      exact Prod.ext h1 h2
    have hinj : Function.Injective π₀ := by
      intro a b h
      by_contra hab
      exact hne a b hab (by rw [hπ a b hab]; exact h)
    exact ⟨Equiv.ofBijective π₀ (Finite.injective_iff_bijective.1 hinj), hπ⟩
  ·
    right
    push Not at hfirst
    obtain ⟨a₀, b₀, c₀, hb₀, hc₀, h₀⟩ := hfirst
    have hsecond : ∀ a, ∀ b c, b ≠ a → c ≠ a → (F a b).2 = (F a c).2 := by
      intro a
      rcases star a with h | h
      · exfalso
        by_cases ha : a = a₀
        · subst ha
          exact h₀ (h b₀ c₀ hb₀ hc₀)
        · have h₀' : ∀ c d, c ≠ a₀ → d ≠ a₀ → (F a₀ c).2 = (F a₀ d).2 := by
            rcases star a₀ with h' | h'
            · exact absurd (h' b₀ c₀ hb₀ hc₀) h₀
            · exact h'
          exact const a a₀ ha h h₀'
      · exact h
    let π₀ : Fin ν → Fin ν := fun a => (F a (o a)).2
    have hπ : ∀ a b, a ≠ b → F a b = (π₀ b, π₀ a) := by
      intro a b hab
      have h2 : (F a b).2 = π₀ a := hsecond a b (o a) (Ne.symm hab) (ho a)
      have h1 : (F a b).1 = π₀ b := by
        have := hswap b a (Ne.symm hab)
        rw [this]
        exact hsecond b a (o b) hab (ho b)
      exact Prod.ext h1 h2
    have hinj : Function.Injective π₀ := by
      intro a b h
      by_contra hab
      exact hne a b hab (by rw [hπ a b hab]; exact h.symm)
    exact ⟨Equiv.ofBijective π₀ (Finite.injective_iff_bijective.1 hinj), hπ⟩

end Pairs

section Frame

variable {τ : Tag} {L : Type}
  [Field L] {ν : ℕ}

namespace IsSLFrame

variable {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem self_eq_zero (h : IsSLFrame ρ σ) (a : Fin ν) : σ a a = 0 := by
  have := h.add a a a
  exact add_eq_right.1 this

theorem iform_eq (h : IsSLFrame ρ σ) {κ : ℤ}
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) (a b c d : Fin ν) :
    iform (σ a b) (σ c d) = κ * framePairForm a b c d := by
  have hN : ∀ x y : Fin ν, iform (σ x y) (σ x y) = 2 * κ * (if x = y then 0 else 1) := by
    intro x y
    by_cases hxy : x = y
    · rw [hxy, h.self_eq_zero y, ite_eq_left (rfl : y = y)]
      simp [iform]
    · rw [hnorm x y hxy, ite_eq_right hxy, mul_one]
  have e1 : σ a d = σ a b + σ b c + σ c d := by rw [h.add a b c, h.add a c d]
  have e2 : σ a c = σ a b + σ b c := (h.add a b c).symm
  have e3 : σ b d = σ b c + σ c d := (h.add b c d).symm
  have key : 2 * iform (σ a b) (σ c d) = iform (σ a d) (σ a d) + iform (σ b c) (σ b c) -
      iform (σ a c) (σ a c) - iform (σ b d) (σ b d) := by
    rw [e1, e2, e3]
    simp only [iform_add_left, iform_add_right]
    rw [iform_comm (σ b c) (σ a b), iform_comm (σ c d) (σ a b), iform_comm (σ c d) (σ b c)]
    ring
  rw [hN, hN, hN, hN] at key
  have : 2 * iform (σ a b) (σ c d) = 2 * (κ * framePairForm a b c d) := by
    rw [key, framePairForm]
    split_ifs <;> ring
  omega

theorem eq_of_eq (h : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) {a b c d : Fin ν} (hab : a ≠ b)
    (hcd : c ≠ d) (he : σ a b = σ c d) : a = c ∧ b = d := by
  have h1 := h.iform_eq hnorm a b c d
  rw [← he, hnorm a b hab] at h1
  have h2 : framePairForm a b c d = 2 := by
    have : κ * framePairForm a b c d = κ * 2 := by rw [← h1]; ring
    exact mul_left_cancel₀ hκ this
  exact (framePairForm_eq_two_iff hab hcd).1 h2

theorem aut_cases (h : IsSLFrame ρ σ) (hν : 3 ≤ ν) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    (φ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (hmaps : ∀ a b, a ≠ b → φ (σ a b) ∈ frameRoots σ)
    (hneg : ∀ γ, φ (-γ) = -φ γ) (hform : ∀ γ δ, iform (φ γ) (φ δ) = iform γ δ) :
    (∃ π : Equiv.Perm (Fin ν), ∀ a b, a ≠ b → φ (σ a b) = σ (π a) (π b)) ∨
      (∃ π : Equiv.Perm (Fin ν), ∀ a b, a ≠ b → φ (σ a b) = σ (π b) (π a)) := by
  classical
  have hm : ∀ a b, ∃ x : Fin ν × Fin ν, a ≠ b → x.1 ≠ x.2 ∧ φ (σ a b) = σ x.1 x.2 := by
    intro a b
    by_cases hab : a = b
    · exact ⟨(a, b), fun h' => absurd hab h'⟩
    · obtain ⟨i, j, hij, hφ⟩ := hmaps a b hab
      exact ⟨(i, j), fun _ => ⟨hij, hφ⟩⟩
  choose F hF using hm
  have hne : ∀ a b, a ≠ b → (F a b).1 ≠ (F a b).2 := fun a b hab => (hF a b hab).1
  have hswap : ∀ a b, a ≠ b → F b a = ((F a b).2, (F a b).1) := by
    intro a b hab
    have h1 : φ (σ b a) = σ (F a b).2 (F a b).1 := by
      rw [h.neg a b, hneg, (hF a b hab).2, ← h.neg]
    have h2 := (hF b a (Ne.symm hab)).2
    obtain ⟨e1, e2⟩ := h.eq_of_eq hκ hnorm (hne b a (Ne.symm hab)) (Ne.symm (hne a b hab))
      (h2.symm.trans h1)
    exact Prod.ext e1 e2
  have hform' : ∀ a b c d, a ≠ b → c ≠ d →
      framePairForm (F a b).1 (F a b).2 (F c d).1 (F c d).2 = framePairForm a b c d := by
    intro a b c d hab hcd
    have h1 := hform (σ a b) (σ c d)
    rw [(hF a b hab).2, (hF c d hcd).2, h.iform_eq hnorm, h.iform_eq hnorm] at h1
    exact mul_left_cancel₀ hκ h1
  rcases pair_aut_cases hν F hne hswap hform' with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · left
    exact ⟨π, fun a b hab => by rw [(hF a b hab).2, hπ a b hab]⟩
  · right
    exact ⟨π, fun a b hab => by rw [(hF a b hab).2, hπ a b hab]⟩

theorem rootReflection_smul (h : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) {x y : Fin ν} (hxy : x ≠ y)
    (c d : Fin ν) :
    rootReflection (σ x y) • σ c d = σ (Equiv.swap x y c) (Equiv.swap x y d) := by
  have hcp : corootPair (σ x y) (σ c d) = framePairForm x y c d := by
    rw [corootPair, h.iform_eq hnorm, hnorm x y hxy]
    rw [show 2 * (κ * framePairForm x y c d) = (2 * κ) * framePairForm x y c d by ring]
    exact Int.mul_ediv_cancel_left _ (by omega)
  rw [CFSG.LieType.Chevalley.rootReflection_smul (h.isRoot x y hxy), hcp]
  have hsw : ∀ i : Fin ν, σ (Equiv.swap x y i) x =
      σ i x - ((if x = i then (1 : ℤ) else 0) - (if y = i then 1 else 0)) • σ x y := by
    intro i
    by_cases hi : i = x
    · rw [hi, Equiv.swap_apply_left, h.self_eq_zero x, h.neg x y,
        ite_eq_left (rfl : x = x), ite_eq_right (Ne.symm hxy : ¬ y = x)]
      module
    · by_cases hi' : i = y
      · rw [hi', Equiv.swap_apply_right, h.self_eq_zero x, h.neg x y,
          ite_eq_right hxy, ite_eq_left (rfl : y = y)]
        module
      · rw [Equiv.swap_apply_of_ne_of_ne hi hi', ite_eq_right (Ne.symm hi : ¬ x = i),
          ite_eq_right (Ne.symm hi' : ¬ y = i)]
        module
  have key : σ (Equiv.swap x y c) (Equiv.swap x y d) =
      σ (Equiv.swap x y c) x - σ (Equiv.swap x y d) x := h.eq_sub _ _ x
  have key2 : σ c d = σ c x - σ d x := h.eq_sub c d x
  rw [key, hsw c, hsw d, key2, framePairForm]
  module

theorem exists_weyl_perm (h : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) (π : Equiv.Perm (Fin ν)) :
    ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ frameRoots σ, s = rootReflection γ},
      ∀ a b, w • σ a b = σ (π a) (π b) := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, Subgroup.one_mem _, fun a b => by simp⟩
  | swap_mul π x y hxy ih =>
    obtain ⟨w, hw, hwσ⟩ := ih
    refine ⟨rootReflection (σ x y) * w, Subgroup.mul_mem _ (Subgroup.subset_closure
      ⟨σ x y, ⟨x, y, hxy, rfl⟩, rfl⟩) hw, fun a b => ?_⟩
    rw [mul_smul, hwσ, h.rootReflection_smul hκ hnorm hxy]
    rfl

end IsSLFrame

end Frame

end CFSG.HardMathSupport.Timmesfeld.CrossChar
