module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteOrbits
public import CFSG.CharacterTheory.Wreathed.WreathColumnRigidity
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteFrame
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootAlgebra

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.WreathColumn

@[expose] def oddIdx (m : ℕ) : Finset ℕ := (Finset.Ico 1 m).filter Odd

structure ColumnData {I : Type*} [Fintype I] [DecidableEq I] (m M : ℕ) [NeZero m] (d : I → ℤ)
    (X : ZMod m → I → ℤ) (Y : ℕ → I → ℤ) (c : ZMod m → ZMod m → I → ℤ)
    (V : Finset (ZMod m × ZMod m)) : Prop where
  pow : ∃ n, 2 ≤ n ∧ m = 2 ^ n
  hm : m = 2 * M
  hd : ∀ i, 0 < d i
  hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6
  hVrep : ∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
    ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup m) I
  hXX : ∀ j j' : ZMod m, j ≠ 0 → j' ≠ 0 → X j ⬝ᵥ X j' = if j = j' then 8 else 4
  hXd : ∀ j : ZMod m, j ≠ 0 → X j ⬝ᵥ d = 0
  hYY : ∀ r t, r < M → t < M → Y r ⬝ᵥ Y t = if r = t then 4 else 0
  hYd : ∀ r < M, Y r ⬝ᵥ d = 0
  hYX : ∀ r < M, ∀ j : ZMod m, j ≠ 0 → Y r ⬝ᵥ X j = 0
  hc00 : c 0 0 = 0
  hcsymm : ∀ i j, c i j = c j i ∧ c i j = c j (-i - j)
  hcd : ∀ i j, c i j ⬝ᵥ d = 0
  hcX : ∀ i j j', j' ≠ 0 → c i j ⬝ᵥ X j' = 0
  hcY : ∀ i j, ∀ r < M, c i j ⬝ᵥ Y r = 0
  hcrr : ∀ r : ZMod m, r ≠ 0 → c r r ⬝ᵥ c r r = 8
  hcV : ∀ I ∈ V, c I.1 I.2 ⬝ᵥ c I.1 I.2 = 7
  hcrr' : ∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' → c r r ⬝ᵥ c r' r' = 6
  hcrV : ∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V, c r r ⬝ᵥ c I.1 I.2 = 6
  hcVV : ∀ I ∈ V, ∀ J ∈ V, I ≠ J → c I.1 I.2 ⬝ᵥ c J.1 J.2 = 6
  hpodd : ∀ j ∈ Finset.Ico 1 m, Odd j → ∀ i, X (j : ZMod m) i ≡ c M M i [ZMOD 2]
  hpeven : ∀ r ∈ Finset.Ico 1 M, ∀ i, X (-(2 * (r : ZMod m))) i ≡
    c M M i + c r r i + c ((r : ZMod m) + M) ((r : ZMod m) + M) i [ZMOD 2]
  hpY : ∀ i, c M M i ≡ Y 0 i [ZMOD 2]
  hpXY : ∀ r ∈ Finset.Ico 1 M, ∀ i, X (-(2 * (r : ZMod m))) i ≡ Y 0 i + Y r i [ZMOD 2]
  hnv : ∀ i κ, (∀ j : ZMod m, j ≠ 0 → X j i = 0) →
    (∀ a b, c a b i = if (a = 0 ∨ a = M) ∧ (b = 0 ∨ b = M) then 0 else κ) → False

namespace ColumnData

variable {I : Type*} [Fintype I] [DecidableEq I] {m M : ℕ} [NeZero m] {d : I → ℤ}
  {X : ZMod m → I → ℤ} {Y : ℕ → I → ℤ} {c : ZMod m → ZMod m → I → ℤ}
  {V : Finset (ZMod m × ZMod m)}

section Basic

variable (hD : ColumnData m M d X Y c V)
include hD

theorem two_le_M : 2 ≤ M := by
  obtain ⟨n, hn, hpow⟩ := hD.pow
  have h4 : 4 ≤ m := by
    rw [hpow]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := hD.hm
  omega

theorem card_oddIdx : (oddIdx m).card = M := by
  rw [oddIdx, hD.hm]
  exact CFSG.Wreathed.ConditionalSquareRoot.card_filter_odd_Ico M

omit [Fintype I] [DecidableEq I] [NeZero m] hD in
theorem oddIdx_ne_zero {h : ℕ} (hh : h ∈ oddIdx m) : (h : ZMod m) ≠ 0 := by
  rw [oddIdx, Finset.mem_filter, Finset.mem_Ico] at hh
  exact natCast_ne_zero_of_lt (by omega) hh.1.2

theorem M_ne_zero : (M : ZMod m) ≠ 0 := by
  have := hD.hm
  have := hD.two_le_M
  exact natCast_ne_zero_of_lt (by omega) (by omega)

theorem r_ne_zero {r : ℕ} (hr : r ∈ Finset.Ico 1 M) : (r : ZMod m) ≠ 0 := by
  rw [Finset.mem_Ico] at hr
  have := hD.hm
  exact natCast_ne_zero_of_lt (by omega) (by omega)

theorem rM_ne_zero {r : ℕ} (hr : r ∈ Finset.Ico 1 M) : (r : ZMod m) + M ≠ 0 := by
  rw [Finset.mem_Ico] at hr
  have := hD.hm
  have h := natCast_ne_zero_of_lt (m := m) (j := r + M) (by omega) (by omega)
  push_cast at h
  exact h

theorem r_ne_M {r : ℕ} (hr : r ∈ Finset.Ico 1 M) : (r : ZMod m) ≠ M := by
  rw [Finset.mem_Ico] at hr
  have := hD.hm
  intro h
  have := natCast_inj_of_lt (m := m) (by omega) (by omega) h
  omega

theorem rM_ne_M {r : ℕ} (hr : r ∈ Finset.Ico 1 M) : (r : ZMod m) + M ≠ M := by
  intro h
  exact hD.r_ne_zero hr (by linear_combination h)

theorem r_ne_rM (r : ℕ) : (r : ZMod m) ≠ (r : ZMod m) + M := by
  intro h
  exact hD.M_ne_zero (by linear_combination -h)

theorem diag_ne {r r' : ℕ} (hr : r ∈ Finset.Ico 1 M) (hr' : r' ∈ Finset.Ico 1 M) (hne : r ≠ r') :
    (r : ZMod m) ≠ r' ∧ (r : ZMod m) ≠ (r' : ZMod m) + M ∧ (r : ZMod m) + M ≠ r' ∧
      (r : ZMod m) + M ≠ (r' : ZMod m) + M := by
  rw [Finset.mem_Ico] at hr hr'
  have hm := hD.hm
  refine ⟨fun h => hne (natCast_inj_of_lt (by omega) (by omega) h), fun h => ?_, fun h => ?_,
    fun h => hne (natCast_inj_of_lt (m := m) (by omega) (by omega) (by linear_combination h))⟩
  · have h' : (r : ZMod m) = ((r' + M : ℕ) : ZMod m) := by push_cast; exact h
    have := natCast_inj_of_lt (by omega) (by omega) h'
    omega
  · have h' : ((r + M : ℕ) : ZMod m) = (r' : ZMod m) := by push_cast; exact h
    have := natCast_inj_of_lt (by omega) (by omega) h'
    omega

end Basic

theorem exists_frame (hD : ColumnData m M d X Y c V) :
    ∃ (i₀ i₁ i₂ i₃ i₄ : I) (p : oddIdx m → I) (q : Finset.Ico 1 M → Fin 4 → I)
      (δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ) (η : Finset.Ico 1 M → Fin 4 → ℤ) (D : ℤ),
      Frame d (fun h : oddIdx m => X (h.1 : ZMod m))
        (fun k : Finset.Ico 1 M => X (-(2 * (k.1 : ZMod m)))) (Y 0)
        (fun k : Finset.Ico 1 M => Y k.1) (c M M) i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D := by
  have hM2 := hD.two_le_M
  have hm := hD.hm
  have hH : 2 ≤ Fintype.card (oddIdx m) := by
    rw [Fintype.card_coe, hD.card_oddIdx]
    exact hM2
  have hK : 1 ≤ Fintype.card (Finset.Ico 1 M) := by
    rw [Fintype.card_coe, Nat.card_Ico]
    omega
  have hcast : ∀ v : I → ℤ, v ⬝ᵥ d = 0 → ∑ i, (v i : ℝ) * (d i : ℝ) = 0 := by
    intro v hv
    have h : ((v ⬝ᵥ d : ℤ) : ℝ) = 0 := by rw [hv, Int.cast_zero]
    rw [dotProduct, Int.cast_sum] at h
    simpa only [Int.cast_mul] using h
  have hodd : ∀ h : oddIdx m, h.1 ∈ Finset.Ico 1 m ∧ Odd h.1 := fun h =>
    Finset.mem_filter.mp h.2
  have hoddlt : ∀ h : oddIdx m, h.1 < m := fun h => (Finset.mem_Ico.mp (hodd h).1).2
  have hEne : ∀ k : Finset.Ico 1 M, -(2 * (k.1 : ZMod m)) ≠ 0 := fun k =>
    neg_two_mul_ne_zero hm k.2
  have hAne : ∀ h : oddIdx m, (h.1 : ZMod m) ≠ 0 := fun h => oddIdx_ne_zero h.2
  have hM0 : 0 < M := by omega
  have hMne := hD.M_ne_zero
  obtain ⟨i₀, i₁, i₂, i₃, i₄, p, q, δ₀, δ₁, δ₂, δ₃, δ₄, α, η, hinj, hsign, hη, hA, hYs, hC, hE,
      hY, D, hD0, hdp, hdcore, hdpair⟩ :=
    positive_degree_integral_wreath_column_rigidity (I := I) hH hK (fun i => (d i : ℝ))
      (fun i => by exact_mod_cast hD.hd i) (fun h : oddIdx m => X (h.1 : ZMod m))
      (fun k : Finset.Ico 1 M => X (-(2 * (k.1 : ZMod m)))) (Y 0)
      (fun k : Finset.Ico 1 M => Y k.1) (c M M)
      (fun h => hcast _ (hD.hXd _ (hAne h))) (fun k => hcast _ (hD.hXd _ (hEne k)))
      (hcast _ (hD.hYd 0 hM0)) (fun k => hcast _ (hD.hYd _ (Finset.mem_Ico.mp k.2).2))
      (hcast _ (hD.hcd _ _))
      (fun h h' => by
        rw [hD.hXX _ _ (hAne h) (hAne h')]
        by_cases hh : h = h'
        · subst hh
          simp
        · have hne : (h.1 : ZMod m) ≠ (h'.1 : ZMod m) := fun he =>
            hh (Subtype.ext (natCast_inj_of_lt (hoddlt h) (hoddlt h') he))
          rw [ite_eq_right hne, ite_eq_right hh]
          norm_num)
      (fun k l => by
        rw [hD.hXX _ _ (hEne k) (hEne l)]
        by_cases hkl : k = l
        · subst hkl
          simp
        · have hne : -(2 * (k.1 : ZMod m)) ≠ -(2 * (l.1 : ZMod m)) := fun he =>
            hkl (Subtype.ext (neg_two_mul_inj hm k.2 l.2 he))
          rw [ite_eq_right hne, ite_eq_right hkl]
          norm_num)
      (fun h k => by
        rw [hD.hXX _ _ (hAne h) (hEne k),
          ite_eq_right (odd_ne_neg_two_mul hm (hoddlt h) (hodd h).2 k.2)])
      (by rw [hD.hYY 0 0 hM0 hM0, ite_eq_left rfl])
      (fun k => by
        rw [hD.hYY 0 k.1 hM0 (Finset.mem_Ico.mp k.2).2,
          ite_eq_right (by have := (Finset.mem_Ico.mp k.2).1; omega)])
      (fun k l => by
        rw [hD.hYY k.1 l.1 (Finset.mem_Ico.mp k.2).2 (Finset.mem_Ico.mp l.2).2]
        by_cases hkl : k = l
        · subst hkl
          simp
        · rw [ite_eq_right (fun he => hkl (Subtype.ext he)), ite_eq_right hkl]
          norm_num)
      (hD.hcrr _ hMne)
      (fun h => hD.hYX 0 hM0 _ (hAne h)) (fun k => hD.hYX 0 hM0 _ (hEne k))
      (by rw [dotProduct_comm]; exact hD.hcY _ _ 0 hM0)
      (fun k h => hD.hYX _ (Finset.mem_Ico.mp k.2).2 _ (hAne h))
      (fun k l => hD.hYX _ (Finset.mem_Ico.mp k.2).2 _ (hEne l))
      (fun k => by rw [dotProduct_comm]; exact hD.hcY _ _ _ (Finset.mem_Ico.mp k.2).2)
      (fun h => hD.hcX _ _ _ (hAne h)) (fun k => hD.hcX _ _ _ (hEne k))
      (fun h i => hD.hpodd h.1 (hodd h).1 (hodd h).2 i) hD.hpY
      (fun k i => hD.hpXY k.1 k.2 i)
  obtain ⟨h₀⟩ : Nonempty (oddIdx m) := Fintype.card_pos_iff.mp (by omega)
  have hDint : ((d (p h₀) : ℤ) : ℝ) = D := hdp h₀
  have hsδ : ∀ s ∈ [δ₀, δ₁, δ₂, δ₃, δ₄, α], s = 1 ∨ s = -1 := hsign
  refine ⟨i₀, i₁, i₂, i₃, i₄, p, q, δ₀, δ₁, δ₂, δ₃, δ₄, α, η, d (p h₀), ⟨hinj, hsδ δ₀ (by simp),
    hsδ δ₁ (by simp), hsδ δ₂ (by simp), hsδ δ₃ (by simp), hsδ δ₄ (by simp), hsδ α (by simp), hη,
    hA, hYs, hC, hE, hY, ?_, ?_, ?_, ?_⟩⟩
  · exact_mod_cast hDint.symm ▸ hD0
  · intro h
    have := (hdp h).trans hDint.symm
    exact_mod_cast this
  · rw [← hDint] at hdcore
    exact_mod_cast hdcore
  · intro k
    obtain ⟨h1, h2⟩ := hdpair k
    rw [← hDint] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end ColumnData

end CFSG.Wreathed.FlatComplete
