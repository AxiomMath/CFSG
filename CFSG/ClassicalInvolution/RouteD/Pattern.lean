module

public import CFSG.ClassicalInvolution.RouteD.PatternB
public import CFSG.ClassicalInvolution.RouteD.PatternD
public import CFSG.ClassicalInvolution.RouteD.PatternExc
public import CFSG.ClassicalInvolution.RouteD.Leaf

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

theorem CharReach.comp_equiv {ι κ : Type} (e : ι ≃ κ) {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ}
    (hMN : ∀ x y, M x y = N (e x) (e y)) {v w : κ → ZMod 2} (h : CharReach N v w) :
    CharReach M (v ∘ e) (w ∘ e) := by
  induction h with
  | refl => exact CharReach.refl' _ _
  | @tail b c _ hs ih =>
    obtain ⟨i, rfl⟩ := hs
    refine ih.trans' ?_
    have : (charRefl N i b) ∘ e = charRefl M (e.symm i) (b ∘ e) := by
      funext x
      simp [charRefl, hMN]
    rw [this]
    exact CharReach.single' _ _

theorem PatternLemma.of_equiv {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ} (hMN : ∀ x y, M x y = N (e x) (e y))
    (h : PatternLemma N) : PatternLemma M := by
  intro v hv
  have hv' : v ∘ e.symm ≠ 0 := by
    intro h0
    apply hv
    funext x
    have := congrFun h0 (e x)
    simpa using this
  obtain ⟨w, hw, j, rfl⟩ := h (v ∘ e.symm) hv'
  refine ⟨Pi.single j 1 ∘ e, ?_, e.symm j, ?_⟩
  · have := CharReach.comp_equiv e hMN hw
    simpa [Function.comp_def] using this
  · funext x
    simp [Pi.single_apply, Equiv.eq_symm_apply]

theorem patternLemma_std {t : DynkinType} (ht : t.Valid) : PatternLemma (stdCartan t) := by
  cases t with
  | A n =>
    rw [stdCartan_A_eq, CartanMatrix.A_transpose]
    exact patternLemma_A n
  | B n =>
    rw [stdCartan_B_eq, CartanMatrix.B_transpose]
    exact patternLemma_B n
  | C n =>
    rw [stdCartan_C_eq, CartanMatrix.C_transpose]
    exact patternLemma_C n
  | D n =>
    rw [stdCartan_D_eq, CartanMatrix.D_transpose]
    exact patternLemma_D (by simpa using ht)
  | E6 =>
    rw [stdCartan_E6_eq]
    exact patternLemma_E6
  | E7 =>
    rw [stdCartan_E7_eq]
    exact patternLemma_E7
  | E8 =>
    rw [stdCartan_E8_eq]
    exact patternLemma_E8
  | F4 =>
    rw [stdCartan_F4_eq]
    exact patternLemma_F4
  | G2 =>
    rw [stdCartan_G2_eq]
    exact patternLemma_G2

theorem patternLemma_of_finiteType {B : Type} [Fintype B] [DecidableEq B] {Γ : Matrix B B ℤ}
    (hΓ : IsFiniteType Γ) (hc : (diagramGraph Γ).Connected) : PatternLemma Γ := by
  obtain ⟨t, ht, e, he⟩ := classify hΓ hc
  exact PatternLemma.of_equiv e he (patternLemma_std ht)

section Sum

variable {ι κ : Type} {M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ}

theorem CharReach.lift_inl {A : Matrix ι ι ℤ} (hA : ∀ i j, M (Sum.inl i) (Sum.inl j) = A i j)
    (h1 : ∀ i j, M (Sum.inl i) (Sum.inr j) = 0) {v₁ w₁ : ι → ZMod 2} (h : CharReach A v₁ w₁) :
    ∀ v : ι ⊕ κ → ZMod 2, (fun i => v (Sum.inl i)) = v₁ →
      ∃ w, CharReach M v w ∧ (fun i => w (Sum.inl i)) = w₁ ∧
        (fun j => w (Sum.inr j)) = fun j => v (Sum.inr j) := by
  induction h with
  | refl => exact fun v hv => ⟨v, CharReach.refl' _ _, hv, rfl⟩
  | @tail b c _ hs ih =>
    intro v hv
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨u, hu, hu1, hu2⟩ := ih v hv
    refine ⟨charRefl M (Sum.inl i) u, hu.trans' (CharReach.single' _ _), ?_, ?_⟩
    · funext x
      simp only [charRefl, hA, ← hu1]
    · funext x
      simp only [charRefl, h1, Int.cast_zero, zero_mul, add_zero]
      exact congrFun hu2 x

theorem CharReach.lift_inr {A : Matrix κ κ ℤ} (hA : ∀ i j, M (Sum.inr i) (Sum.inr j) = A i j)
    (h2 : ∀ i j, M (Sum.inr j) (Sum.inl i) = 0) {v₁ w₁ : κ → ZMod 2} (h : CharReach A v₁ w₁) :
    ∀ v : ι ⊕ κ → ZMod 2, (fun j => v (Sum.inr j)) = v₁ →
      ∃ w, CharReach M v w ∧ (fun j => w (Sum.inr j)) = w₁ ∧
        (fun i => w (Sum.inl i)) = fun i => v (Sum.inl i) := by
  induction h with
  | refl => exact fun v hv => ⟨v, CharReach.refl' _ _, hv, rfl⟩
  | @tail b c _ hs ih =>
    intro v hv
    obtain ⟨j, rfl⟩ := hs
    obtain ⟨u, hu, hu1, hu2⟩ := ih v hv
    refine ⟨charRefl M (Sum.inr j) u, hu.trans' (CharReach.single' _ _), ?_, ?_⟩
    · funext x
      simp only [charRefl, hA, ← hu1]
    · funext x
      simp only [charRefl, h2, Int.cast_zero, zero_mul, add_zero]
      exact congrFun hu2 x

theorem patternLemma_sum [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι ℤ} {A' : Matrix κ κ ℤ}
    (hA : ∀ i j, M (Sum.inl i) (Sum.inl j) = A i j)
    (hA' : ∀ i j, M (Sum.inr i) (Sum.inr j) = A' i j)
    (h1 : ∀ i j, M (Sum.inl i) (Sum.inr j) = 0) (h2 : ∀ i j, M (Sum.inr j) (Sum.inl i) = 0)
    (hP : PatternLemma A) (hP' : PatternLemma A') (v : ι ⊕ κ → ZMod 2) :
    ∃ w, CharReach M v w ∧
      ((∀ i, w (Sum.inl i) = 0) ∨ SupportOne (fun i => w (Sum.inl i))) ∧
      ((∀ j, w (Sum.inr j) = 0) ∨ SupportOne (fun j => w (Sum.inr j))) ∧
      ((∀ i, v (Sum.inl i) = 0) → ∀ i, w (Sum.inl i) = 0) ∧
      ((∀ j, v (Sum.inr j) = 0) → ∀ j, w (Sum.inr j) = 0) := by
  classical
  obtain ⟨w₁, hw₁, hw₁'⟩ : ∃ w₁ : ι → ZMod 2, CharReach A (fun i => v (Sum.inl i)) w₁ ∧
      (w₁ = 0 ∨ SupportOne w₁) ∧ ((fun i => v (Sum.inl i)) = 0 → w₁ = 0) := by
    by_cases h : (fun i => v (Sum.inl i)) = 0
    · exact ⟨0, by rw [h]; exact CharReach.refl' _ _, Or.inl rfl, fun _ => rfl⟩
    · obtain ⟨w, hw, hs⟩ := hP _ h
      exact ⟨w, hw, Or.inr hs, fun h' => absurd h' h⟩
  obtain ⟨u, hu, hu1, hu2⟩ := CharReach.lift_inl hA h1 hw₁ v rfl
  obtain ⟨w₂, hw₂, hw₂'⟩ : ∃ w₂ : κ → ZMod 2, CharReach A' (fun j => u (Sum.inr j)) w₂ ∧
      (w₂ = 0 ∨ SupportOne w₂) ∧ ((fun j => u (Sum.inr j)) = 0 → w₂ = 0) := by
    by_cases h : (fun j => u (Sum.inr j)) = 0
    · exact ⟨0, by rw [h]; exact CharReach.refl' _ _, Or.inl rfl, fun _ => rfl⟩
    · obtain ⟨w, hw, hs⟩ := hP' _ h
      exact ⟨w, hw, Or.inr hs, fun h' => absurd h' h⟩
  obtain ⟨w, hw, hw1, hw2⟩ := CharReach.lift_inr hA' h2 hw₂ u rfl
  have hwi : (fun i => w (Sum.inl i)) = w₁ := hw2.trans hu1
  have hwj : (fun j => w (Sum.inr j)) = w₂ := hw1
  refine ⟨w, hu.trans' hw, ?_, ?_, ?_, ?_⟩
  · rcases hw₁'.1 with h | h
    · left; intro i; have h3 : w (Sum.inl i) = w₁ i := congrFun hwi i; rw [h3, h]; rfl
    · right; rw [hwi]; exact h
  · rcases hw₂'.1 with h | h
    · left; intro j; have h3 : w (Sum.inr j) = w₂ j := congrFun hwj j; rw [h3, h]; rfl
    · right; rw [hwj]; exact h
  · intro h0 i
    have h4 := hw₁'.2 (funext h0)
    have h3 : w (Sum.inl i) = w₁ i := congrFun (hw2.trans hu1) i
    rw [h3, h4]; rfl
  · intro h0 j
    have hz : (fun j => u (Sum.inr j)) = 0 := by
      funext x
      have h5 : u (Sum.inr x) = v (Sum.inr x) := congrFun hu2 x
      rw [show (0 : κ → ZMod 2) x = 0 from rfl, h5]
      exact h0 x
    have h4 := hw₂'.2 hz
    have h3 : w (Sum.inr j) = w₂ j := congrFun hw1 j
    rw [h3, h4]; rfl

end Sum

end CFSG.ClassicalInvolution.RouteD
