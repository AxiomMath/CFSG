module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoFiveModelCheck
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoGammaThree

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def dFlipTw (σ : K ≃+* K) (x : Fin 3 ⊕ Fin 3 → K) : Fin 3 ⊕ Fin 3 → K :=
  Sum.elim ![σ (x (.inl 0)), σ (x (.inr 1)), σ (x (.inr 2))]
    ![σ (x (.inr 0)), σ (x (.inl 1)), σ (x (.inl 2))]

namespace QTwoFive

open QTwoGammaThree

private def lift4 (ω : K) (v : V4) : Fin 2 ⊕ Fin 2 → K :=
  Sum.elim ![ι ω v.x0, ι ω v.x1] ![ι ω v.y0, ι ω v.y1]

variable {ω : K}

private theorem q5_l4_x0 (v : V4) : lift4 ω v (Sum.inl 0) = ι ω v.x0 := rfl

private theorem q5_l4_x1 (v : V4) : lift4 ω v (Sum.inl 1) = ι ω v.x1 := rfl

private theorem q5_l4_y0 (v : V4) : lift4 ω v (Sum.inr 0) = ι ω v.y0 := rfl

private theorem q5_l4_y1 (v : V4) : lift4 ω v (Sum.inr 1) = ι ω v.y1 := rfl

private theorem q5_ι_zero : ι ω 0 = 0 := rfl

private theorem q5_ι_one : ι ω 1 = 1 := rfl

variable [CharP K 2]

private theorem q5_ι_eq_zero (hω : ω * ω = ω + 1) {a : Fin 4} : ι ω a = 0 ↔ a = 0 :=
  ⟨fun h => ι_injective hω (h.trans q5_ι_zero.symm), fun h => h ▸ q5_ι_zero⟩

private theorem q5_ι_eq_one (hω : ω * ω = ω + 1) {a : Fin 4} : ι ω a = 1 ↔ a = 1 :=
  ⟨fun h => ι_injective hω (h.trans q5_ι_one.symm), fun h => h ▸ q5_ι_one⟩

private theorem quadPlus_lift4 (hω : ω * ω = ω + 1) (v : V4) :
    quadPlus 2 K (lift4 ω v) = ι ω (q4 v) := by
  rw [quadPlus_apply, Fin.sum_univ_two]
  simp only [q5_l4_x0, q5_l4_x1, q5_l4_y0, q5_l4_y1, q4]
  simp only [← ι_fMul hω, ← ι_fAdd]

private theorem polar_lift4 (hω : ω * ω = ω + 1) (u v : V4) :
    polar (quadPlus 2 K) (lift4 ω u) (lift4 ω v) = ι ω (p4 u v) := by
  rw [polar_quadPlus, Fin.sum_univ_two]
  simp only [q5_l4_x0, q5_l4_x1, q5_l4_y0, q5_l4_y1, p4]
  simp only [← ι_fMul hω, ← ι_fAdd]

private theorem flipHerm_lift4 {σ : K ≃+* K} (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (u v : V4) :
    flipHerm σ (lift4 ω u) (lift4 ω v) = ι ω (h4 u v) := by
  rw [flipHerm_apply, Fin.sum_univ_two]
  simp only [q5_l4_x0, q5_l4_x1, q5_l4_y0, q5_l4_y1, h4, frobC, σ_ι hσω]
  simp only [← ι_fMul hω, ← ι_fAdd]

private theorem dFlip_lift4 {σ : K ≃+* K} (hσω : σ ω = ω + 1) (v : V4) :
    dFlip σ (lift4 ω v) = lift4 ω (flip4 v) := by
  funext x
  cases x with
  | inl i =>
    fin_cases i <;> simp [q5_l4_x0, q5_l4_x1, q5_l4_y0, q5_l4_y1, flip4, frobC, σ_ι hσω]
  | inr i =>
    fin_cases i <;> simp [q5_l4_x0, q5_l4_x1, q5_l4_y0, q5_l4_y1, flip4, frobC, σ_ι hσω]

private theorem exists_lift4 [Finite K] (hK : Nat.card K = 4) (hω : ω * ω = ω + 1)
    (x : Fin 2 ⊕ Fin 2 → K) : ∃ v, lift4 ω v = x := by
  have hsurj := ι_surjective (w := ω) hK hω
  refine ⟨⟨Function.surjInv hsurj (x (Sum.inl 0)), Function.surjInv hsurj (x (Sum.inl 1)),
    Function.surjInv hsurj (x (Sum.inr 0)), Function.surjInv hsurj (x (Sum.inr 1))⟩, ?_⟩
  funext y
  cases y with
  | inl i => fin_cases i <;> simp [q5_l4_x0, q5_l4_x1, Function.surjInv_eq]
  | inr i => fin_cases i <;> simp [q5_l4_y0, q5_l4_y1, Function.surjInv_eq]

private theorem dFlipTw_lift {σ : K ≃+* K} (hσω : σ ω = ω + 1) (z : V6) :
    dFlipTw σ (lift ω z) = lift ω (twC z) := by
  funext x
  cases x with
  | inl i => fin_cases i <;> simp [dFlipTw, lift, twC, frobC, σ_ι hσω]
  | inr i => fin_cases i <;> simp [dFlipTw, lift, twC, frobC, σ_ι hσω]

end QTwoFive

open QTwoGammaThree QTwoFive

theorem isFlipflopPt_vec_block_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) {g : Fin 2 ⊕ Fin 2 → K}
    (hg : quadPlus 2 K g = 0) (hgg : flipHerm σ g g ≠ 0) :
    (g (.inl 1) = 0 ∧ g (.inr 1) = 0) ∨ (g (.inl 0) = 0 ∧ g (.inr 0) = 0) := by
  obtain ⟨ω, hσω, hω⟩ := exists_sigma_eq_add_one hσ hK
  obtain ⟨G, rfl⟩ := exists_lift4 hK hω g
  rw [quadPlus_lift4 hω, q5_ι_eq_zero hω] at hg
  rw [flipHerm_lift4 hω hσω, Ne, q5_ι_eq_zero hω] at hgg
  rcases block_spec G hg hgg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [q5_l4_x1, h1, q5_ι_zero], by rw [q5_l4_y1, h2, q5_ι_zero]⟩
  · exact Or.inr ⟨by rw [q5_l4_x0, h1, q5_ι_zero], by rw [q5_l4_y0, h2, q5_ι_zero]⟩

theorem singular_or_exists_fixed_hyperbolic_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ≠ 0)
    (hrow : (quadPlus 2 K v = 0 ∧ flipHerm σ v v = 0) ∨
      (quadPlus 2 K v ≠ 0 ∧ flipHerm σ v v = 1)) :
    (∀ x, polar (quadPlus 2 K) x v = 0 → flipHerm σ x v = 0 → quadPlus 2 K x = 0) ∨
    ∃ u w : Fin 2 ⊕ Fin 2 → K, dFlip σ u = u ∧ dFlip σ w = w ∧
      quadPlus 2 K u = 0 ∧ quadPlus 2 K w = 0 ∧ polar (quadPlus 2 K) u w = 1 ∧
      polar (quadPlus 2 K) u v = 0 ∧ flipHerm σ u v = 0 ∧
      polar (quadPlus 2 K) w v = 0 ∧ flipHerm σ w v = 0 ∧
      ∀ x, polar (quadPlus 2 K) x v = 0 → flipHerm σ x v = 0 →
        polar (quadPlus 2 K) x u = 0 → polar (quadPlus 2 K) x w = 0 →
        quadPlus 2 K x = 0 := by
  obtain ⟨ω, hσω, hω⟩ := exists_sigma_eq_add_one hσ hK
  obtain ⟨V, rfl⟩ := exists_lift4 hK hω v
  have hV : V ≠ zero4 := by
    rintro rfl
    refine hv (funext fun x => ?_)
    cases x with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl
  have hrow' : (q4 V = 0 ∧ h4 V V = 0) ∨ (q4 V ≠ 0 ∧ h4 V V = 1) := by
    simpa only [quadPlus_lift4 hω, flipHerm_lift4 hω hσω, ne_eq, q5_ι_eq_zero hω,
      q5_ι_eq_one hω] using hrow
  have hall : ∀ {P : (Fin 2 ⊕ Fin 2 → K) → Prop}, (∀ X, P (lift4 ω X)) → ∀ x, P x := by
    intro P h x
    obtain ⟨X, rfl⟩ := exists_lift4 hK hω x
    exact h X
  rcases hyp_spec V hV hrow' with h | ⟨U, W, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · refine Or.inl (hall fun X hx hx' => ?_)
    rw [polar_lift4 hω, q5_ι_eq_zero hω] at hx
    rw [flipHerm_lift4 hω hσω, q5_ι_eq_zero hω] at hx'
    rw [quadPlus_lift4 hω, h X hx hx', q5_ι_zero]
  · refine Or.inr ⟨lift4 ω U, lift4 ω W, by rw [dFlip_lift4 hσω, h1],
      by rw [dFlip_lift4 hσω, h2], by rw [quadPlus_lift4 hω, h3, q5_ι_zero],
      by rw [quadPlus_lift4 hω, h4, q5_ι_zero], by rw [polar_lift4 hω, h5, q5_ι_one],
      by rw [polar_lift4 hω, h6, q5_ι_zero], by rw [flipHerm_lift4 hω hσω, h7, q5_ι_zero],
      by rw [polar_lift4 hω, h8, q5_ι_zero], by rw [flipHerm_lift4 hω hσω, h9, q5_ι_zero],
      hall fun X hx hx' hxu hxw => ?_⟩
    rw [polar_lift4 hω, q5_ι_eq_zero hω] at hx hxu hxw
    rw [flipHerm_lift4 hω hσω, q5_ι_eq_zero hω] at hx'
    rw [quadPlus_lift4 hω, h10 X hx hx' hxu hxw, q5_ι_zero]

theorem exists_orth_dFlipTw_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) {x : Fin 3 ⊕ Fin 3 → K}
    (hx : quadPlus 3 K x = 0) (hxx : polar (quadPlus 3 K) x (dFlipTw σ x) ≠ 0) :
    ∃ z, quadPlus 3 K z = 0 ∧ polar (quadPlus 3 K) z (dFlipTw σ z) ≠ 0 ∧
      polar (quadPlus 3 K) x z = 0 ∧ polar (quadPlus 3 K) x (dFlipTw σ z) = 0 ∧
      ((z (.inl 2) = 0 ∧ z (.inr 2) = 0) ∨ (z (.inl 1) = 0 ∧ z (.inr 1) = 0)) := by
  obtain ⟨ω, hσω, hω⟩ := exists_sigma_eq_add_one hσ hK
  obtain ⟨X, rfl⟩ := exists_lift hK hω x
  rw [quadPlus_lift hω, q5_ι_eq_zero hω] at hx
  rw [dFlipTw_lift hσω, polar_lift hω, Ne, q5_ι_eq_zero hω] at hxx
  obtain ⟨Z, hz1, hz2, hz3, hz4, hz5⟩ := tw_spec X hx hxx
  refine ⟨lift ω Z, by rw [quadPlus_lift hω, hz1, q5_ι_zero],
    by rw [dFlipTw_lift hσω, polar_lift hω, Ne, q5_ι_eq_zero hω]; exact hz2,
    by rw [polar_lift hω, hz3, q5_ι_zero], by rw [dFlipTw_lift hσω, polar_lift hω, hz4, q5_ι_zero],
    ?_⟩
  rcases hz5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨show ι ω Z.x2 = 0 by rw [h1, q5_ι_zero],
      show ι ω Z.y2 = 0 by rw [h2, q5_ι_zero]⟩
  · exact Or.inr ⟨show ι ω Z.x1 = 0 by rw [h1, q5_ι_zero],
      show ι ω Z.y1 = 0 by rw [h2, q5_ι_zero]⟩

end CFSG.ClassicalInvolution.PhanDn
