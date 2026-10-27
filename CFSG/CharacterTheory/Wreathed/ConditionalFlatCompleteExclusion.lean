module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteCases
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteGeneric

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

open CFSG.Wreathed.ConditionalGeneralBase

theorem ne_core_of_notMem {I : Type*} [DecidableEq I] {i₀ i₁ i₂ i₃ i₄ x : I}
    (h : x ∉ ({i₀, i₁, i₂, i₃, i₄} : Finset I)) :
    x ≠ i₀ ∧ x ≠ i₁ ∧ x ≠ i₂ ∧ x ≠ i₃ ∧ x ≠ i₄ := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact h

namespace Frame

variable {I H K : Type*} [Fintype I] [DecidableEq I]
  {d : I → ℤ} {A : H → I → ℤ} {E : K → I → ℤ} {Ys : I → ℤ} {Y : K → I → ℤ} {C : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : H → I} {q : K → Fin 4 → I} {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ}
  {η : K → Fin 4 → ℤ} {D : ℤ}

omit [Fintype I] in
theorem frame_vanish (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
    {x : I} (hx : x ∉ ({i₀, i₁, i₂, i₃, i₄} : Finset I)) (hxp : ∀ h, p h ≠ x)
    (hxq : ∀ k l, q k l ≠ x) :
    (∀ h, A h x = 0) ∧ (∀ k, E k x = 0) ∧ C x = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := ne_core_of_notMem hx
  refine ⟨fun h => ?_, fun k => ?_, ?_⟩
  · rw [F.formA h]
    simp [h0, h1, h2, h3, (hxp h).symm]
  · rw [F.formE k]
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [sum_single_q_of_ne k (hxq k)]
    simp [h0, h1, h2, h3]
  · rw [F.formC]
    simp [h0, h1, h2, h3, h4]

end Frame

namespace ColumnData

variable {I : Type*} [Fintype I] [DecidableEq I] {m M : ℕ} [NeZero m] {d : I → ℤ}
  {X : ZMod m → I → ℤ} {Y : ℕ → I → ℤ} {c : ZMod m → ZMod m → I → ℤ}
  {V : Finset (ZMod m × ZMod m)} {Ys : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : oddIdx m → I} {q : Finset.Ico 1 M → Fin 4 → I}
  {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ} {η : Finset.Ico 1 M → Fin 4 → ℤ} {D : ℤ}

theorem X_row_vanish (hD : ColumnData m M d X Y c V)
    (G : FlatFrame m M d X Y c Ys i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D) {x : I}
    (hx : x ∉ ({i₀, i₁, i₂, i₃, i₄} : Finset I)) (hxp : ∀ h, p h ≠ x)
    (hxq : ∀ k l, q k l ≠ x) : ∀ j : ZMod m, j ≠ 0 → X j x = 0 := by
  obtain ⟨hA, hE, -⟩ := G.frame.frame_vanish hx hxp hxq
  intro j hj
  rcases index_cases hD.hm hj with ⟨h, hh, rfl⟩ | ⟨r, hr, rfl⟩
  · exact hA ⟨h, hh⟩
  · exact hE ⟨r, hr⟩

theorem not_caseA (hD : ColumnData m M d X Y c V)
    (G : FlatFrame m M d X Y c Ys i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
    (k₀ : Finset.Ico 1 M) (h0 : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 0 (c k₀.1 k₀.1)) : False := by
  have F := G.frame
  choose a e σ σ' ξ x hσ hσ' hx hoff hpair hoff' hpair' using fun k => hD.diag_data G k
  have ha0 : a k₀ = 0 := CoreAt.unique F.sδ₀ F.sδ₂ (hoff k₀).1 h0
  have hx1 : x k₀ * x k₀ = 1 := by
    rw [hx k₀, ha0]
    simp [caseNorm]
  have hx0 : x k₀ ≠ 0 := by
    intro h
    rw [h] at hx1
    norm_num at hx1
  have hϑ : x k₀ = 1 ∨ x k₀ = -1 := by
    have hb : -1 ≤ x k₀ ∧ x k₀ ≤ 1 := by constructor <;> nlinarith
    omega
  have hall : ∀ k, a k = 0 ∧ ξ k = ξ k₀ ∧ x k = x k₀ := by
    intro k
    obtain ⟨haa, hxx⟩ := hD.case_uniform G (hx k₀) (hx k) (hoff k₀) (hoff k)
    obtain ⟨h1, h2⟩ := hxx hx0
    exact ⟨haa ▸ ha0, h1.symm, h2.symm⟩
  obtain ⟨hξout, hξq⟩ := (hoff k₀).2.2.2 hx0
  have hξcore := (mem_outK.mp hξout).1
  have hξp := (mem_outK.mp hξout).2.1
  have hξoutk : ∀ k : Finset.Ico 1 M, ξ k₀ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k) := fun k =>
    mem_outK.mpr ⟨hξcore, hξp, fun l => hξq k l⟩
  have hdiagξ : ∀ k : Finset.Ico 1 M,
      c k.1 k.1 (ξ k₀) = x k₀ ∧ c (k.1 + M) (k.1 + M) (ξ k₀) = x k₀ := by
    intro k
    obtain ⟨-, hξk, hxk⟩ := hall k
    have h1 := (hoff k).2.2.1 (ξ k₀) (hξoutk k)
    have h2 := (hoff' k).2.2.1 (ξ k₀) (hξoutk k)
    rw [hξk, ite_eq_left rfl, hxk] at h1 h2
    exact ⟨h1, h2⟩
  have hoffA : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k₀ (c k₀.1 k₀.1) 0 (ξ k₀) (x k₀) := by
    rw [← ha0]
    exact hoff k₀
  have hoffA' : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k₀ (c (k₀.1 + M) (k₀.1 + M)) 0
      (ξ k₀) (x k₀) := by
    rw [← ha0]
    exact hoff' k₀
  have hgenξ : ∀ J ∈ V, c J.1 J.2 (ξ k₀) = x k₀ := by
    intro J hJ
    obtain ⟨oA, oYs, oE, oY⟩ := hD.frame_orth G.hYs J.1 J.2
    have hJC : c J.1 J.2 ⬝ᵥ c M M = 6 := by
      rw [dotProduct_comm]
      exact hD.hcrV _ hD.M_ne_zero J hJ
    have hJc : c J.1 J.2 ⬝ᵥ c k₀.1 k₀.1 = 6 := by
      rw [dotProduct_comm]
      exact hD.hcrV _ (hD.r_ne_zero k₀.2) J hJ
    have hJc' : c J.1 J.2 ⬝ᵥ c (k₀.1 + M) (k₀.1 + M) = 6 := by
      rw [dotProduct_comm]
      exact hD.hcrV _ (hD.rM_ne_zero k₀.2) J hJ
    exact F.generic_caseA hD.two_le_card_oddIdx k₀ hϑ (hσ k₀) (hσ' k₀) hoffA (hpair k₀) hoffA'
      (hpair' k₀) (hD.hcV J hJ) oA oYs hJC (oE k₀) (oY k₀) hJc hJc'
  have hXξ := hD.X_row_vanish G hξcore hξp hξq
  have hCξ := (F.frame_vanish hξcore hξp hξq).2.2
  have hcξ : ∀ a b, c a b (ξ k₀) =
      if (a = 0 ∨ a = M) ∧ (b = 0 ∨ b = M) then 0 else x k₀ := by
    intro a b
    rcases orbit_reduction hD.hm c hD.hcsymm V hD.hVrep a b with ⟨rfl, rfl⟩ |
      ⟨ρ, hρ, hab, hexc⟩ | ⟨J, hJ, hab, hexc⟩
    · rw [hD.hc00]
      simp
    · rw [hab]
      by_cases hρM : ρ = M
      · rw [ite_eq_left (hexc.mpr hρM), hρM]
        exact hCξ
      · rw [ite_eq_right (fun h => hρM (hexc.mp h))]
        obtain ⟨r, hr, hρr | hρr⟩ := diag_index hD.hm hρ hρM
        · rw [hρr]
          exact (hdiagξ ⟨r, hr⟩).1
        · rw [hρr]
          exact (hdiagξ ⟨r, hr⟩).2
    · rw [hab, ite_eq_right hexc]
      exact hgenξ J hJ
  exact hD.hnv (ξ k₀) (x k₀) hXξ hcξ

end ColumnData

end CFSG.Wreathed.FlatComplete
