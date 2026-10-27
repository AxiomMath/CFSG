module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapNH

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

namespace GapWC

theorem four_rel {a b c : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (ha : a = 1 ∨ a = -1 ∨ a = Dmat ∨ a = -Dmat) (hb : b = 1 ∨ b = -1 ∨ b = Dmat ∨ b = -Dmat)
    (hc : c = 1 ∨ c = -1 ∨ c = Dmat ∨ c = -Dmat) :
    a = 1 ∨ b = 1 ∨ c = 1 ∨ a * b = 1 ∨ a * c = 1 ∨ b * c = 1 ∨ a * b * c = 1 := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem two_rel {a b c : Matrix (Fin 3) (Fin 3) (ZMod 4)} (ha : a = 1 ∨ a = -Dmat)
    (hb : b = 1 ∨ b = -Dmat) (hc : c = 1 ∨ c = -Dmat) :
    (a = 1 ∧ b = 1) ∨ (a = 1 ∧ c = 1) ∨ (b = 1 ∧ c = 1) ∨ (a = 1 ∧ b * c = 1) ∨
      (b = 1 ∧ a * c = 1) ∨ (c = 1 ∧ a * b = 1) ∨ (a * b = 1 ∧ a * c = 1) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> decide

theorem sq_Umat_sub : (Umat - 1) * (Umat - 1) ≠ 0 := by decide

theorem sq_neg_Umat_sub : (-Umat - 1) * (-Umat - 1) ≠ 0 := by decide

theorem two_sub : ∀ a b : ZMod 4, 2 * a ≠ 0 → 2 * b ≠ 0 → 2 * (a - b) = 0 := by decide

theorem two_add : ∀ a b : ZMod 4, 2 * a ≠ 0 → 2 * b ≠ 0 → 2 * (a + b) = 0 := by decide

theorem D_mulVec (x : Fin 3 → ZMod 4) : (Dmat *ᵥ x) 2 = 3 * x 2 := by
  simp [Dmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem neg_D_mulVec (x : Fin 3 → ZMod 4) :
    (-Dmat *ᵥ x) 0 = -x 0 ∧ (-Dmat *ᵥ x) 1 = -x 1 := by
  simp [Dmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end GapWC

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

@[expose] noncomputable def conjΦ (g : X) (v : Fin 3 → ZMod 4) : X := g * A.Φ v * g⁻¹

theorem conjΦ_add (g : X) (v w : Fin 3 → ZMod 4) :
    A.conjΦ g (v + w) = A.conjΦ g v * A.conjΦ g w := by
  simp only [conjΦ, A.Φ_add]
  group

theorem conjΦ_zero (g : X) : A.conjΦ g 0 = 1 := by simp [conjΦ, A.Φ_zero]

theorem conjΦ_neg (g : X) (v : Fin 3 → ZMod 4) : A.conjΦ g (-v) = (A.conjΦ g v)⁻¹ := by
  simp only [conjΦ, A.Φ_neg]
  group

theorem conjΦ_injective (g : X) : Function.Injective (A.conjΦ g) := by
  intro v w h
  apply A.Φ_injective
  have := congrArg (fun x => g⁻¹ * x * g) h
  simpa [conjΦ, mul_assoc] using this

theorem conjΦ_pow_four (g : X) (v : Fin 3 → ZMod 4) : A.conjΦ g v ^ 4 = 1 := by
  rw [show A.conjΦ g v ^ 4 = A.conjΦ g (v + v + v + v) by
    rw [A.conjΦ_add, A.conjΦ_add, A.conjΦ_add]
    simp only [pow_succ, pow_zero, one_mul]]
  rw [show v + v + v + v = 0 by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize v i = a
    revert a
    decide, A.conjΦ_zero]

theorem conjΦ_comm (g : X) (v w : Fin 3 → ZMod 4) :
    A.conjΦ g v * A.conjΦ g w = A.conjΦ g w * A.conjΦ g v := by
  rw [← conjΦ_add, ← conjΦ_add, add_comm]

end BData

namespace BData.Syl

variable {A : BData S F T₁} (Y : A.Syl)

structure WCData (g : X) : Prop where
  mem : ∀ v, A.conjΦ g v ∈ Y.P
  norm_A : ∀ a ∈ A.AA, ∀ v, ∃ w, a * A.conjΦ g v * a⁻¹ = A.conjΦ g w
  norm_t : ∀ v, ∃ w, S.t * A.conjΦ g v * S.t⁻¹ = A.conjΦ g w

theorem InVQ2_of_two_mul {x : Fin 3 → ZMod 4} (hx : 2 * x 2 = 0) : Y.InVQ2 (A.Φ x) := by
  obtain ⟨s, hs⟩ := GapNH.exists_add_self _ hx
  refine ⟨A.Φ ![x 0, x 1, 0], ⟨_, rfl, rfl⟩, A.Φ ![0, 0, s], Y.AA_le_Q (A.Φ_mem _), ?_⟩
  rw [pow_two, ← A.Φ_add, ← A.Φ_add]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp
  · simp [hs]

namespace WCData

variable {Y} {g : X} (W : Y.WCData g)

noncomputable def M (v : Fin 3 → ZMod 4) : Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  A.mat ⟨A.conjΦ g v, Y.mem_NA (W.mem v)⟩

theorem M_add (v w : Fin 3 → ZMod 4) : W.M (v + w) = W.M v * W.M w := by
  rw [M, M, M, ← A.mat_mul]
  congr 1
  exact Subtype.ext (A.conjΦ_add g v w)

theorem mem_AA_iff (hnc : ¬ SubConj F.E₁ F.E₂) (v : Fin 3 → ZMod 4) :
    A.conjΦ g v ∈ A.AA ↔ W.M v = 1 := by
  constructor
  · intro h
    exact A.mat_of_AA h
  · intro h
    have hC := (A.mat_eq_one_iff _).mp h
    exact Y.mem_AA_of_pow_four hnc (mem_inf.mpr ⟨W.mem v, hC⟩) (A.conjΦ_pow_four g v)

theorem conj_Φ (v x : Fin 3 → ZMod 4) :
    A.conjΦ g v * A.Φ x * (A.conjΦ g v)⁻¹ = A.Φ (W.M v *ᵥ x) :=
  A.conj_Φ ⟨A.conjΦ g v, Y.mem_NA (W.mem v)⟩ x

theorem fix {u y : Fin 3 → ZMod 4} (hy : A.Φ y = A.conjΦ g u) (w : Fin 3 → ZMod 4) :
    W.M w *ᵥ y = y := by
  apply A.Φ_injective
  rw [← W.conj_Φ, hy, A.conjΦ_comm g w u, mul_inv_cancel_right]

theorem comm_mem (v x : Fin 3 → ZMod 4) : ∃ u, A.conjΦ g u = A.Φ (W.M v *ᵥ x - x) := by
  obtain ⟨w, hw⟩ := W.norm_A (A.Φ x) (A.Φ_mem x) (-v)
  refine ⟨v + w, ?_⟩
  rw [A.conjΦ_add, ← hw, A.Φ_sub, ← W.conj_Φ, A.conjΦ_neg]
  group

theorem F1 (v w : Fin 3 → ZMod 4) : (W.M w - 1) * (W.M v - 1) = 0 := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  obtain ⟨u, hu⟩ := W.comm_mem v x
  have h := W.fix hu.symm w
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]
  rw [h, sub_self]

include W in
theorem q_mem (v : Fin 3 → ZMod 4) : ∃ u, qxOf S (A.conjΦ g v) = A.conjΦ g u := by
  obtain ⟨w, hw⟩ := W.norm_t v
  refine ⟨w + -v, ?_⟩
  have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
  rw [A.conjΦ_add, A.conjΦ_neg, ← hw, qxOf, ht']

include W in
theorem q_AA (hnc : ¬ SubConj F.E₁ F.E₂) (v : Fin 3 → ZMod 4) :
    qxOf S (A.conjΦ g v) ∈ A.AA := by
  obtain ⟨u, hu⟩ := W.q_mem v
  have hQ := Y.qx_mem_Q (W.mem v)
  rw [hu] at hQ ⊢
  exact Y.mem_AA_of_pow_four hnc hQ (A.conjΦ_pow_four g u)

include W in
theorem q_add (v w : Fin 3 → ZMod 4) :
    qxOf S (A.conjΦ g (v + w)) = qxOf S (A.conjΦ g v) * qxOf S (A.conjΦ g w) := by
  rw [A.conjΦ_add, qxOf_mul]
  obtain ⟨u, hu⟩ := W.q_mem w
  rw [hu, A.conjΦ_comm g v u, mul_inv_cancel_right]

theorem L4 (hnc : ¬ SubConj F.E₁ F.E₂) (v : Fin 3 → ZMod 4)
    (h : Y.InVQ2 (qxOf S (A.conjΦ g v))) : W.M v ∈ BData.L4set := by
  obtain ⟨q, hq, hqp⟩ := Y.mem_QS₁_of_qx hnc (W.mem v) h
  have hqN : q ∈ A.NA := Y.mem_NA (mem_inf.mp hq).1
  have hN : q * A.conjΦ g v ∈ A.NA := mul_mem hqN (Y.mem_NA (W.mem v))
  have hm := A.mat_S₁ hqp hN
  rwa [show (⟨q * A.conjΦ g v, hN⟩ : A.NA) = ⟨q, hqN⟩ * ⟨A.conjΦ g v, Y.mem_NA (W.mem v)⟩
    from rfl, A.mat_mul, (A.mat_eq_one_iff _).mpr (mem_inf.mp hq).2, one_mul] at hm

theorem eq_one_of_even (hnc : ¬ SubConj F.E₁ F.E₂) (hneg : ∀ w, W.M w ≠ -1)
    {v x : Fin 3 → ZMod 4} (hx : A.Φ x = qxOf S (A.conjΦ g v)) (h2 : 2 * x 2 = 0) :
    W.M v = 1 := by
  have h := W.L4 hnc v (by rw [← hx]; exact Y.InVQ2_of_two_mul h2)
  simp only [BData.L4set, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have hsq := W.F1 v v
  rcases h with h | h | h | h
  · exact h
  · exact absurd h (hneg v)
  · rw [h] at hsq; exact absurd hsq GapWC.sq_Umat_sub
  · rw [h] at hsq; exact absurd hsq GapWC.sq_neg_Umat_sub

theorem redM_of_two {N : Matrix (Fin 3) (Fin 3) (ZMod 4)} (h : N + N = 0) : redM N = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.zero_apply] at this
  exact (r2_eq_zero_iff _).mpr (by rw [two_mul]; exact this)

theorem redM_of_sub {N : Matrix (Fin 3) (Fin 3) (ZMod 4)} (h : (N - 1) + (N - 1) = 0) :
    redM N = 1 := by
  have e := GapNH.redM_sub N 1
  rw [redM_of_two h, redM_one] at e
  exact (sub_eq_zero.mp e.symm)

theorem redM_of_neg {v₀ : Fin 3 → ZMod 4} (h : W.M v₀ = -1) (w : Fin 3 → ZMod 4) :
    redM (W.M w) = 1 := by
  have hF := W.F1 v₀ w
  rw [h] at hF
  refine redM_of_sub ?_
  have e : (W.M w - 1) * (-1 - 1) = -((W.M w - 1) + (W.M w - 1)) := by noncomm_ring
  rw [e, neg_eq_zero] at hF
  exact hF

theorem redM_of_sq {v : Fin 3 → ZMod 4} (h : W.M v * W.M v = 1) : redM (W.M v) = 1 := by
  have hF := W.F1 v v
  refine redM_of_sub ?_
  have e : (W.M v - 1) * (W.M v - 1) = -((W.M v - 1) + (W.M v - 1)) := by
    have : (W.M v - 1) * (W.M v - 1) = W.M v * W.M v - W.M v - W.M v + 1 := by noncomm_ring
    rw [this, h]
    abel
  rw [e, neg_eq_zero] at hF
  exact hF

theorem two_eq_zero_of_neg (hnc : ¬ SubConj F.E₁ F.E₂) {v₀ u : Fin 3 → ZMod 4}
    (h : W.M v₀ = -1) (hu : W.M u = 1) : u + u = 0 := by
  obtain ⟨y, hy⟩ := A.mem_AA.mp ((W.mem_AA_iff hnc u).mpr hu)
  have hf := W.fix hy v₀
  rw [h, Matrix.neg_mulVec, Matrix.one_mulVec] at hf
  apply A.conjΦ_injective g
  rw [A.conjΦ_add, ← hy, ← A.Φ_add, A.conjΦ_zero, ← A.Φ_zero]
  congr 1
  have e : y + y = -y + y := by rw [hf]
  rw [e, neg_add_cancel]

theorem two_sub_eq_zero (hnc : ¬ SubConj F.E₁ F.E₂) {v₁ u u' : Fin 3 → ZMod 4}
    (hD : W.M v₁ = -Dmat) (hu : W.M u = 1) (hu' : W.M u' = 1) (h2u : u + u ≠ 0)
    (h2u' : u' + u' ≠ 0) : (u - u') + (u - u') = 0 := by
  obtain ⟨y, hy⟩ := A.mem_AA.mp ((W.mem_AA_iff hnc u).mpr hu)
  obtain ⟨y', hy'⟩ := A.mem_AA.mp ((W.mem_AA_iff hnc u').mpr hu')
  have hf := W.fix hy v₁
  have hf' := W.fix hy' v₁
  rw [hD] at hf hf'
  obtain ⟨e0, e1⟩ := GapWC.neg_D_mulVec y
  obtain ⟨e0', e1'⟩ := GapWC.neg_D_mulVec y'
  rw [hf] at e0 e1
  rw [hf'] at e0' e1'
  have hc : ∀ {u y : Fin 3 → ZMod 4}, A.Φ y = A.conjΦ g u → u + u ≠ 0 → y 0 = -y 0 →
      y 1 = -y 1 → 2 * y 2 ≠ 0 := by
    intro u y hy h2 e0 e1 h22
    apply h2
    apply A.conjΦ_injective g
    rw [A.conjΦ_add, ← hy, ← A.Φ_add, A.conjΦ_zero, ← A.Φ_zero]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.zero_apply]
      linear_combination e0
    · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.zero_apply]
      linear_combination e1
    · simp only [Fin.reduceFinMk, Fin.isValue, Pi.add_apply, Pi.zero_apply]
      linear_combination h22
  have h2 := hc hy h2u e0 e1
  have h2' := hc hy' h2u' e0' e1'
  apply A.conjΦ_injective g
  have hsub : A.conjΦ g (u - u') = A.Φ (y - y') := by
    rw [sub_eq_add_neg, A.conjΦ_add, A.conjΦ_neg, ← hy, ← hy', A.Φ_sub]
  rw [A.conjΦ_add, hsub, ← A.Φ_add, A.conjΦ_zero, ← A.Φ_zero]
  congr 1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    linear_combination e0 - e0'
  · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    linear_combination e1 - e1'
  · simp only [Fin.reduceFinMk, Fin.isValue, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    linear_combination GapWC.two_sub _ _ h2 h2'

theorem M_eq_one (hnc : ¬ SubConj F.E₁ F.E₂) (v : Fin 3 → ZMod 4) : W.M v = 1 := by
  by_cases hA : ∃ v₀, W.M v₀ = -1
  · exfalso
    obtain ⟨v₀, h⟩ := hA
    have hm : ∀ w, W.M w = 1 ∨ W.M w = -1 ∨ W.M w = Dmat ∨ W.M w = -Dmat := fun w =>
      Y.mat_mem_of_redM hnc (W.mem w) (W.redM_of_neg h w)
    have key : ∀ u, W.M u = 1 → u + u ≠ 0 → False := fun u hu h2 =>
      h2 (W.two_eq_zero_of_neg hnc h hu)
    rcases GapWC.four_rel (hm ![1, 0, 0]) (hm ![0, 1, 0]) (hm ![0, 0, 1]) with
      h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact key _ h1 (by decide)
    · exact key _ h1 (by decide)
    · exact key _ h1 (by decide)
    · exact key (![1, 0, 0] + ![0, 1, 0]) (by rw [W.M_add]; exact h1) (by decide)
    · exact key (![1, 0, 0] + ![0, 0, 1]) (by rw [W.M_add]; exact h1) (by decide)
    · exact key (![0, 1, 0] + ![0, 0, 1]) (by rw [W.M_add]; exact h1) (by decide)
    · exact key (![1, 0, 0] + ![0, 1, 0] + ![0, 0, 1]) (by rw [W.M_add, W.M_add]; exact h1)
        (by decide)
  push Not at hA
  by_contra hv
  obtain ⟨x₁, hx₁⟩ := A.mem_AA.mp (W.q_AA hnc v)
  have hx₁2 : 2 * x₁ 2 ≠ 0 := fun h => hv (W.eq_one_of_even hnc hA hx₁ h)
  have hsq : W.M v * W.M v = 1 := by
    rw [← W.M_add]
    refine W.eq_one_of_even hnc hA (x := x₁ + x₁) ?_ ?_
    · rw [W.q_add, ← hx₁, A.Φ_add]
    · simp only [Pi.add_apply]
      exact four_mul_zmod4 (x₁ 2)
  obtain ⟨u₁, hu₁⟩ := W.q_mem v
  have hfix := W.fix (hx₁.trans hu₁) v
  rcases Y.mat_mem_of_redM hnc (W.mem v) (W.redM_of_sq hsq) with h | h | h | h
  · exact hv h
  · exact hA v h
  · have e := GapWC.D_mulVec x₁
    rw [show W.M v = Dmat from h] at hfix
    rw [hfix] at e
    exact hx₁2 (by linear_combination -e)
  · have hD : W.M v = -Dmat := h
    have hall : ∀ w, W.M w = 1 ∨ W.M w = -Dmat := by
      intro w
      by_cases hw : W.M w = 1
      · exact Or.inl hw
      · right
        obtain ⟨xw, hxw⟩ := A.mem_AA.mp (W.q_AA hnc w)
        have hxw2 : 2 * xw 2 ≠ 0 := fun h => hw (W.eq_one_of_even hnc hA hxw h)
        have h1 : W.M (w + v) = 1 := W.eq_one_of_even hnc hA (x := xw + x₁)
          (by rw [W.q_add, ← hxw, ← hx₁, A.Φ_add])
          (by simp only [Pi.add_apply]; exact GapWC.two_add _ _ hxw2 hx₁2)
        rw [W.M_add] at h1
        calc W.M w = W.M w * (W.M v * W.M v) := by rw [hsq, mul_one]
          _ = (W.M w * W.M v) * W.M v := by rw [mul_assoc]
          _ = -Dmat := by rw [h1, one_mul, hD]
    have key : ∀ u u', W.M u = 1 → W.M u' = 1 → u + u ≠ 0 → u' + u' ≠ 0 →
        (u - u') + (u - u') ≠ 0 → False := fun u u' hu hu' h1 h2 h3 =>
      h3 (W.two_sub_eq_zero hnc hD hu hu' h1 h2)
    rcases GapWC.two_rel (hall ![1, 0, 0]) (hall ![0, 1, 0]) (hall ![0, 0, 1]) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key _ _ h1 h2 (by decide) (by decide) (by decide)
    · exact key _ _ h1 h2 (by decide) (by decide) (by decide)
    · exact key _ _ h1 h2 (by decide) (by decide) (by decide)
    · exact key ![1, 0, 0] (![0, 1, 0] + ![0, 0, 1]) h1 (by rw [W.M_add]; exact h2)
        (by decide) (by decide) (by decide)
    · exact key ![0, 1, 0] (![1, 0, 0] + ![0, 0, 1]) h1 (by rw [W.M_add]; exact h2)
        (by decide) (by decide) (by decide)
    · exact key ![0, 0, 1] (![1, 0, 0] + ![0, 1, 0]) h1 (by rw [W.M_add]; exact h2)
        (by decide) (by decide) (by decide)
    · exact key (![1, 0, 0] + ![0, 1, 0]) (![1, 0, 0] + ![0, 0, 1])
        (by rw [W.M_add]; exact h1) (by rw [W.M_add]; exact h2) (by decide) (by decide)
        (by decide)

include W in
theorem conjΦ_mem_AA (hnc : ¬ SubConj F.E₁ F.E₂) (v : Fin 3 → ZMod 4) :
    A.conjΦ g v ∈ A.AA :=
  (W.mem_AA_iff hnc v).mpr (W.M_eq_one hnc v)

include W in
theorem mem_NA (hnc : ¬ SubConj F.E₁ F.E₂) : g ∈ A.NA := by
  have hle : A.AA.map (MulAut.conj g).toMonoidHom ≤ A.AA := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨v, rfl⟩ := A.mem_AA.mp ha
    exact W.conjΦ_mem_AA hnc v
  have heq : A.AA.map (MulAut.conj g).toMonoidHom = A.AA :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [BData.NA, mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hle ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨a, ha, hah⟩ := hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hah
    have : a = h := mul_left_cancel (mul_right_cancel hah)
    rwa [← this]

end WCData

end BData.Syl

end Sec8

end CFSG.ComponentClassification.HSFLit
