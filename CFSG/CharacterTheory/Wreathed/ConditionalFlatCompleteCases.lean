module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteData
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteCross

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

open CFSG.Wreathed.ConditionalGeneralBase

structure FlatFrame {I : Type*} [DecidableEq I] (m M : ℕ) (d : I → ℤ) (X : ZMod m → I → ℤ)
    (Y : ℕ → I → ℤ) (c : ZMod m → ZMod m → I → ℤ) (Ys : I → ℤ) (i₀ i₁ i₂ i₃ i₄ : I)
    (p : oddIdx m → I) (q : Finset.Ico 1 M → Fin 4 → I) (δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ)
    (η : Finset.Ico 1 M → Fin 4 → ℤ) (D : ℤ) : Prop where
  frame : Frame d (fun h : oddIdx m => X (h.1 : ZMod m))
    (fun k : Finset.Ico 1 M => X (-(2 * (k.1 : ZMod m)))) Ys
    (fun k : Finset.Ico 1 M => Y k.1) (c M M) i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D
  hYs : Ys = Y 0 ∨ Ys = -Y 0

namespace Frame

variable {I H K : Type*} [DecidableEq I]
  {d : I → ℤ} {A : H → I → ℤ} {E : K → I → ℤ} {Ys : I → ℤ} {Y : K → I → ℤ} {C : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : H → I} {q : K → Fin 4 → I} {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ}
  {η : K → Fin 4 → ℤ} {D : ℤ}

theorem swap (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D) :
    Frame d A E (-Ys) Y C i₂ i₃ i₀ i₁ i₄ p q δ₂ δ₃ δ₀ δ₁ δ₄ α η D := by
  obtain ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ := F.core_ne
  have hcore : Function.Injective ![i₂, i₃, i₀, i₁, i₄] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  refine ⟨?_, F.sδ₂, F.sδ₃, F.sδ₀, F.sδ₁, F.sδ₄, F.sα, F.sη, fun h => ?_, ?_, ?_, fun k => ?_,
    F.formY, F.Dpos, F.dp, by linarith [F.dcore], F.dpair⟩
  · intro a b hab
    rcases a with a | a | a <;> rcases b with b | b | b
    · exact congrArg Sum.inl (hcore hab)
    · exfalso
      fin_cases a
      · exact F.p_ne_core b 2 hab.symm
      · exact F.p_ne_core b 3 hab.symm
      · exact F.p_ne_core b 0 hab.symm
      · exact F.p_ne_core b 1 hab.symm
      · exact F.p_ne_core b 4 hab.symm
    · exfalso
      fin_cases a
      · exact F.q_ne_core b.1 b.2 2 hab.symm
      · exact F.q_ne_core b.1 b.2 3 hab.symm
      · exact F.q_ne_core b.1 b.2 0 hab.symm
      · exact F.q_ne_core b.1 b.2 1 hab.symm
      · exact F.q_ne_core b.1 b.2 4 hab.symm
    · exfalso
      fin_cases b
      · exact F.p_ne_core a 2 hab
      · exact F.p_ne_core a 3 hab
      · exact F.p_ne_core a 0 hab
      · exact F.p_ne_core a 1 hab
      · exact F.p_ne_core a 4 hab
    · exact congrArg (fun x => Sum.inr (Sum.inl x)) (F.p_inj hab)
    · exact absurd hab.symm (F.q_ne_p b.1 b.2 a)
    · exfalso
      fin_cases b
      · exact F.q_ne_core a.1 a.2 2 hab
      · exact F.q_ne_core a.1 a.2 3 hab
      · exact F.q_ne_core a.1 a.2 0 hab
      · exact F.q_ne_core a.1 a.2 1 hab
      · exact F.q_ne_core a.1 a.2 4 hab
    · exact absurd hab (F.q_ne_p a.1 a.2 b)
    · have := F.q_inj hab
      exact congrArg (fun x => Sum.inr (Sum.inr x)) (Prod.ext this.1 this.2)
  · rw [F.formA h]
    abel
  · rw [F.formYs]
    abel
  · rw [F.formC]
    abel
  · rw [F.formE k]
    abel

end Frame

theorem CoreAt.swap {I : Type*} {i₀ i₁ i₂ i₃ i₄ : I} {δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ} {v : I → ℤ}
    (h : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 2 v) :
    CoreAt i₂ i₃ i₀ i₁ i₄ δ₂ δ₃ δ₀ δ₁ δ₄ 1 v := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  simp only [caseZ0, caseZ2, caseW, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at h0 h1 h2 h3 h4 ⊢
  exact ⟨h2, h3, h0, h1, h4⟩

theorem FlatFrame.swap {I : Type*} [DecidableEq I] {m M : ℕ} {d : I → ℤ}
    {X : ZMod m → I → ℤ} {Y : ℕ → I → ℤ} {c : ZMod m → ZMod m → I → ℤ} {Ys : I → ℤ}
    {i₀ i₁ i₂ i₃ i₄ : I} {p : oddIdx m → I} {q : Finset.Ico 1 M → Fin 4 → I}
    {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ} {η : Finset.Ico 1 M → Fin 4 → ℤ} {D : ℤ}
    (G : FlatFrame m M d X Y c Ys i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D) :
    FlatFrame m M d X Y c (-Ys) i₂ i₃ i₀ i₁ i₄ p q δ₂ δ₃ δ₀ δ₁ δ₄ α η D :=
  ⟨G.frame.swap, by rcases G.hYs with h | h <;> rw [h] <;> simp⟩

namespace ColumnData

variable {I : Type*} [Fintype I] [DecidableEq I] {m M : ℕ} [NeZero m] {d : I → ℤ}
  {X : ZMod m → I → ℤ} {Y : ℕ → I → ℤ} {c : ZMod m → ZMod m → I → ℤ}
  {V : Finset (ZMod m × ZMod m)} {Ys : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : oddIdx m → I} {q : Finset.Ico 1 M → Fin 4 → I}
  {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ} {η : Finset.Ico 1 M → Fin 4 → ℤ} {D : ℤ}

theorem frame_orth (hD : ColumnData m M d X Y c V) (hYs : Ys = Y 0 ∨ Ys = -Y 0)
    (a b : ZMod m) :
    (∀ h : oddIdx m, c a b ⬝ᵥ X (h.1 : ZMod m) = 0) ∧ c a b ⬝ᵥ Ys = 0 ∧
      (∀ k : Finset.Ico 1 M, c a b ⬝ᵥ X (-(2 * (k.1 : ZMod m))) = 0) ∧
      ∀ k : Finset.Ico 1 M, c a b ⬝ᵥ Y k.1 = 0 := by
  have hM0 : 0 < M := by have := hD.two_le_M; omega
  refine ⟨fun h => hD.hcX _ _ _ (oddIdx_ne_zero h.2), ?_,
    fun k => hD.hcX _ _ _ (neg_two_mul_ne_zero hD.hm k.2),
    fun k => hD.hcY _ _ _ (Finset.mem_Ico.mp k.2).2⟩
  rcases hYs with rfl | rfl
  · exact hD.hcY _ _ 0 hM0
  · rw [dotProduct_neg, hD.hcY _ _ 0 hM0, neg_zero]

theorem two_le_card_oddIdx (hD : ColumnData m M d X Y c V) : 2 ≤ Fintype.card (oddIdx m) := by
  rw [Fintype.card_coe, hD.card_oddIdx]
  exact hD.two_le_M

theorem diag_data (hD : ColumnData m M d X Y c V)
    (G : FlatFrame m M d X Y c Ys i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
    (k : Finset.Ico 1 M) :
    ∃ (a : Fin 3) (e : Fin 2) (σ σ' : ℤ) (ξ : I) (x : ℤ), (σ = 1 ∨ σ = -1) ∧
      (σ' = 1 ∨ σ' = -1) ∧ x * x = 6 - caseNorm a ∧
      OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k (c k.1 k.1) a ξ x ∧
      PairAt (q k) (η k) (c k.1 k.1) e σ ∧
      OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k (c (k.1 + M) (k.1 + M)) a ξ x ∧
      PairAt (q k) (η k) (c (k.1 + M) (k.1 + M)) (1 - e) σ' := by
  have F := G.frame
  obtain ⟨oA, oYs, oE, oY⟩ := hD.frame_orth G.hYs k.1 k.1
  obtain ⟨oA', oYs', oE', oY'⟩ := hD.frame_orth G.hYs (k.1 + M) (k.1 + M)
  have hr0 := hD.r_ne_zero k.2
  have hrM0 := hD.rM_ne_zero k.2
  obtain ⟨a, e, σ, σ', hσ, hσ', hcore, hcore', hp, hpair, hpair', hagree, hR⟩ :=
    F.diag_pair hD.two_le_card_oddIdx k (hD.hcrr _ hr0) (hD.hcrr _ hrM0)
      (hD.hcrr' _ _ hr0 hrM0 (hD.r_ne_rM _)) oA oA' oYs oYs'
      (hD.hcrr' _ _ hr0 hD.M_ne_zero (hD.r_ne_M k.2))
      (hD.hcrr' _ _ hrM0 hD.M_ne_zero (hD.rM_ne_M k.2)) (oE k) (oE' k) (oY k) (oY' k)
      (fun i => hD.hpeven k.1 k.2 i)
  obtain ⟨ξ, x, hx, hoff⟩ := F.offPairs_of_shape hcore (fun h => (hp h).1) hR oY
  exact ⟨a, e, σ, σ', ξ, x, hσ, hσ', hx, hoff, hpair,
    Frame.offPairs_congr hoff hcore' (fun h => (hp h).2) hagree, hpair'⟩

theorem case_uniform (hD : ColumnData m M d X Y c V)
    (G : FlatFrame m M d X Y c Ys i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
    {k k' : Finset.Ico 1 M} {a a' : Fin 3} {ξ ξ' : I} {x x' : ℤ}
    (hx : x * x = 6 - caseNorm a) (hx' : x' * x' = 6 - caseNorm a')
    (hv : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k (c k.1 k.1) a ξ x)
    (hw : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k' (c k'.1 k'.1) a' ξ' x') :
    a = a' ∧ (x ≠ 0 → ξ = ξ' ∧ x = x') := by
  have F := G.frame
  by_cases hkk : k = k'
  · subst hkk
    have ha := CoreAt.unique F.sδ₀ F.sδ₂ hv.1 hw.1
    subst ha
    refine ⟨rfl, fun hx0 => ?_⟩
    have hξ := (hv.2.2.2 hx0).1
    have h1 := hv.2.2.1 ξ hξ
    have h2 := hw.2.2.1 ξ hξ
    rw [ite_eq_left rfl] at h1
    have hxx : x' * x' = x * x := by rw [hx, hx']
    by_cases hξξ : ξ = ξ'
    · subst hξξ
      rw [ite_eq_left rfl] at h2
      exact ⟨rfl, h1.symm.trans h2⟩
    · rw [ite_eq_right hξξ] at h2
      exact absurd (h1.symm.trans h2) hx0
  · have hne : k.1 ≠ k'.1 := fun h => hkk (Subtype.ext h)
    have hdot := F.dot_offPairs hkk hv hw
    rw [hD.hcrr' _ _ (hD.r_ne_zero k.2) (hD.r_ne_zero k'.2) (hD.diag_ne k.2 k'.2 hne).1]
      at hdot
    have hnorm : ∀ b : Fin 3, caseNorm b = 5 ∨ caseNorm b = 6 := fun b => by
      fin_cases b <;> simp [caseNorm]
    have bx : -1 ≤ x ∧ x ≤ 1 := by
      constructor <;> rcases hnorm a with h | h <;> rw [h] at hx <;> nlinarith
    have bx' : -1 ≤ x' ∧ x' ≤ 1 := by
      constructor <;> rcases hnorm a' with h | h <;> rw [h] at hx' <;> nlinarith
    have hT : -1 ≤ x * (if ξ = ξ' then x' else 0) ∧ x * (if ξ = ξ' then x' else 0) ≤ 1 := by
      split_ifs <;> constructor <;> nlinarith
    have haa : a = a' := by
      by_contra hne'
      rw [ite_eq_right hne'] at hdot
      linarith [hT.2]
    subst haa
    refine ⟨rfl, fun hx0 => ?_⟩
    rw [ite_eq_left rfl] at hdot
    rcases hnorm a with h5 | h6
    · have hT1 : x * (if ξ = ξ' then x' else 0) = 1 := by linarith
      by_cases hξξ : ξ = ξ'
      · rw [ite_eq_left hξξ] at hT1
        refine ⟨hξξ, ?_⟩
        have : x * x = 1 := by rw [hx, h5]; norm_num
        nlinarith
      · rw [ite_eq_right hξξ, mul_zero] at hT1
        exact absurd hT1 (by norm_num)
    · exfalso
      rw [h6] at hx
      exact hx0 (mul_self_eq_zero.mp (by linarith))

end ColumnData

end CFSG.Wreathed.FlatComplete
