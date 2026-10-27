module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution

open QuaternionGroup

def q8Eval {H : Type*} [Group H] (u v : H) : QuaternionGroup 2 → H
  | .a k => u ^ k.val
  | .xa k => v * u ^ k.val

theorem q8Eval_eq {H : Type*} [Group H] (f : QuaternionGroup 2 →* H) (x : QuaternionGroup 2) :
    f x = q8Eval (f (a 1)) (f (xa 0)) x := by
  have ha : ∀ k : ZMod 4, (a k : QuaternionGroup 2) = (a 1) ^ k.val := fun k => by
    rw [a_one_pow, ZMod.natCast_zmod_val]
  cases x with
  | a k =>
    calc f (a k) = f ((a 1) ^ k.val) := by rw [ha k]
      _ = (f (a 1)) ^ k.val := map_pow _ _ _
  | xa k =>
    have h : (xa k : QuaternionGroup 2) = xa 0 * a k := by simp
    calc f (xa k) = f (xa 0) * f ((a 1) ^ k.val) := by rw [h, map_mul, ha k]
      _ = f (xa 0) * (f (a 1)) ^ k.val := by rw [map_pow]

private def Q8AutPair (u v : QuaternionGroup 2) : Prop :=
  (∀ x y, q8Eval u v (x * y) = q8Eval u v x * q8Eval u v y) ∧
    ∀ x y, q8Eval u v x = q8Eval u v y → x = y

private instance (u v : QuaternionGroup 2) : Decidable (Q8AutPair u v) := by
  unfold Q8AutPair; infer_instance

private theorem q8AutPair_of_mulEquiv (β : QuaternionGroup 2 ≃* QuaternionGroup 2) :
    Q8AutPair (β (a 1)) (β (xa 0)) := by
  have e : ∀ x, β x = q8Eval (β (a 1)) (β (xa 0)) x := fun x => q8Eval_eq β.toMonoidHom x
  refine ⟨fun x y => ?_, fun x y h => β.injective ?_⟩
  · rw [← e, ← e, ← e, map_mul]
  · rw [e x, e y]; exact h

private theorem q8_w_aux : ∀ u v : QuaternionGroup 2, Q8AutPair u v →
    (∀ x, q8Eval u v (q8Eval u v x) = x) → (∃ x, q8Eval u v x ≠ x) →
    ∃ w, q8Eval u v w = w * a 2 := by
  decide +kernel

theorem q8_w_lemma (β : QuaternionGroup 2 ≃* QuaternionGroup 2) (h2 : β * β = 1) (h1 : β ≠ 1) :
    ∃ w : QuaternionGroup 2, β w = w * a 2 := by
  have e : ∀ x, β x = q8Eval (β (a 1)) (β (xa 0)) x := fun x => q8Eval_eq β.toMonoidHom x
  have hinv : ∀ x, β (β x) = x := fun x => by
    simpa using congrArg (fun γ : QuaternionGroup 2 ≃* QuaternionGroup 2 => γ x) h2
  obtain ⟨w, hw⟩ := q8_w_aux _ _ (q8AutPair_of_mulEquiv β)
    (fun x => by rw [← e, ← e]; exact hinv x)
    (by
      by_contra hcon
      push Not at hcon
      exact h1 (MulEquiv.ext fun x => by rw [e]; exact hcon x))
  exact ⟨w, by rw [e]; exact hw⟩

private theorem q8_aut_aux : ∀ u₁ u₂ : QuaternionGroup 2, Q8AutPair u₁ u₂ →
    ∀ v₁ v₂ : QuaternionGroup 2, Q8AutPair v₁ v₂ →
    (∀ x, q8Eval u₁ u₂ (q8Eval u₁ u₂ x) = q8Eval v₁ v₂ (q8Eval v₁ v₂ x)) →
    (∃ x, q8Eval u₁ u₂ (q8Eval u₁ u₂ x) ≠ x) →
    ¬ ∀ x, q8Eval u₁ u₂ (q8Eval v₁ v₂ (q8Eval u₁ u₂ x)) = q8Eval v₁ v₂ x := by
  decide +kernel

theorem q8_not_faithful_on_aut
    (f : QuaternionGroup 2 →* (QuaternionGroup 2 ≃* QuaternionGroup 2)) :
    ¬ Function.Injective f := by
  intro hf
  have h2 : (a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have e1 : (a 1 : QuaternionGroup 2) * a 1 = a 2 := by decide
  have e2 : (xa 0 : QuaternionGroup 2) * xa 0 = a 2 := by decide
  have e3 : (a 1 : QuaternionGroup 2) * xa 0 * a 1 = xa 0 := by decide
  set u := f (a 1) with hu
  set v := f (xa 0) with hv
  have euu : u * u = v * v := by rw [hu, hv, ← map_mul, ← map_mul, e1, e2]
  have euu1 : u * u ≠ 1 := by
    rw [hu, ← map_mul, e1]
    intro h
    exact h2 (hf (by rw [map_one]; exact h))
  have euvu : u * v * u = v := by rw [hu, hv, ← map_mul, ← map_mul, e3]
  have eu : ∀ x, u x = q8Eval (u (a 1)) (u (xa 0)) x := fun x => q8Eval_eq u.toMonoidHom x
  have ev : ∀ x, v x = q8Eval (v (a 1)) (v (xa 0)) x := fun x => q8Eval_eq v.toMonoidHom x
  refine q8_aut_aux _ _ (q8AutPair_of_mulEquiv u) _ _ (q8AutPair_of_mulEquiv v) ?_ ?_ ?_
  · intro x
    rw [← eu, ← eu, ← ev, ← ev]
    simpa using congrArg (fun γ : QuaternionGroup 2 ≃* QuaternionGroup 2 => γ x) euu
  · by_contra hcon
    push Not at hcon
    refine euu1 (MulEquiv.ext fun x => ?_)
    have := hcon x
    rw [← eu, ← eu] at this
    simpa using this
  · intro x
    rw [← eu, ← eu, ← ev, ← ev]
    simpa using congrArg (fun γ : QuaternionGroup 2 ≃* QuaternionGroup 2 => γ x) euvu

private theorem q8_card_autPairs :
    Fintype.card {p : QuaternionGroup 2 × QuaternionGroup 2 // Q8AutPair p.1 p.2} = 24 := by
  decide +kernel

theorem q8_natCard_mulEquiv_le : Nat.card (QuaternionGroup 2 ≃* QuaternionGroup 2) ≤ 24 := by
  let f : (QuaternionGroup 2 ≃* QuaternionGroup 2) →
      {p : QuaternionGroup 2 × QuaternionGroup 2 // Q8AutPair p.1 p.2} :=
    fun β => ⟨(β (a 1), β (xa 0)), q8AutPair_of_mulEquiv β⟩
  have hf : Function.Injective f := by
    intro β γ h
    have h1 : β (a 1) = γ (a 1) := congrArg (fun p => p.1.1) h
    have h2 : β (xa 0) = γ (xa 0) := congrArg (fun p => p.1.2) h
    refine MulEquiv.ext fun x => ?_
    calc β x = q8Eval (β (a 1)) (β (xa 0)) x := q8Eval_eq β.toMonoidHom x
      _ = q8Eval (γ (a 1)) (γ (xa 0)) x := by rw [h1, h2]
      _ = γ x := (q8Eval_eq γ.toMonoidHom x).symm
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := {p : QuaternionGroup 2 × QuaternionGroup 2 //
    Q8AutPair p.1 p.2}), q8_card_autPairs] at this

theorem q8_center_mem_ker {M : Type*} [Group M] (f : QuaternionGroup 2 →* M)
    (hf : ¬ Function.Injective f) : f (a 2) = 1 := by
  have hq : ∀ g : QuaternionGroup 2, g ≠ 1 → g = a 2 ∨ g ^ 2 = a 2 := by decide
  unfold Function.Injective at hf
  push Not at hf
  obtain ⟨x, y, hxy, hne⟩ := hf
  have hg : f (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hne' : x⁻¹ * y ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  rcases hq _ hne' with h | h
  · rw [← h]; exact hg
  · rw [← h, map_pow, hg, one_pow]

theorem q8_normalizing_centralizes {G : Type*} [Group G] (A B : Subgroup G)
    (eA : QuaternionGroup 2 ≃* A) (eB : QuaternionGroup 2 ≃* B)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    ∀ b ∈ B, (eA (a 2) : G) * b = b * (eA (a 2) : G) := by
  let φ : QuaternionGroup 2 →* MulAut B :=
    (Subgroup.normalizerMonoidHom B).comp ((Subgroup.inclusion hAB).comp eA.toMonoidHom)
  let ψ : QuaternionGroup 2 →* (QuaternionGroup 2 ≃* QuaternionGroup 2) :=
    ((MulAut.congr eB.symm).toMonoidHom).comp φ
  have h1 : ψ (a 2) = 1 := q8_center_mem_ker ψ (q8_not_faithful_on_aut ψ)
  have h2 : φ (a 2) = 1 := by
    have : (MulAut.congr eB.symm) (φ (a 2)) = 1 := h1
    exact (MulAut.congr eB.symm).injective (this.trans (map_one _).symm)
  intro b hb
  have h3 := congrArg (fun m : MulAut B => ((m ⟨b, hb⟩ : B) : G)) h2
  have h4 : (eA (a 2) : G) * b * (eA (a 2) : G)⁻¹ = b := h3
  calc (eA (a 2) : G) * b
      = ((eA (a 2) : G) * b * (eA (a 2) : G)⁻¹) * (eA (a 2) : G) := by group
    _ = b * (eA (a 2) : G) := by rw [h4]

theorem q8_tight_pair_commute {G : Type*} [Group G] (A B : Subgroup G)
    (eA : QuaternionGroup 2 ≃* A) (eB : QuaternionGroup 2 ≃* B)
    (hA : ∀ g : G, g * (eA (a 2) : G) = (eA (a 2) : G) * g →
      g ∈ Subgroup.normalizer (A : Set G))
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hinter : A ⊓ B = ⊥) :
    ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
  intro x hx y hy
  have hbN : y ∈ Subgroup.normalizer (A : Set G) :=
    hA y (q8_normalizing_centralizes A B eA eB hAB y hy).symm
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ B :=
    B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB hx) y).mp hy) (B.inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ A := by
    have h := (Subgroup.mem_normalizer_iff.mp hbN x⁻¹).mp (A.inv_mem hx)
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact A.mul_mem hx h
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ A ⊓ B := ⟨h2, h1⟩
  rw [hinter, Subgroup.mem_bot] at h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem q8_line {G : Type*} [Group G] (A : Subgroup G) (eA : QuaternionGroup 2 ≃* A) (d : G)
    (hd2 : d * d = 1) (hdN : d ∈ Subgroup.normalizer (A : Set G))
    (hdC : ¬ ∀ x ∈ A, d * x = x * d) :
    ∃ w ∈ A, w⁻¹ * d * w = (eA (a 2) : G) * d := by
  let n : Subgroup.normalizer (A : Set G) := ⟨d, hdN⟩
  have hn2 : n * n = 1 := Subtype.ext hd2
  let m : MulAut A := Subgroup.normalizerMonoidHom A n
  let β : QuaternionGroup 2 ≃* QuaternionGroup 2 := (MulAut.congr eA.symm) m
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hβ2 : β * β = 1 := by
    have : m * m = 1 := by rw [← map_mul, hn2, map_one]
    show (MulAut.congr eA.symm) m * (MulAut.congr eA.symm) m = 1
    rw [← map_mul, this, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    have hm : m = 1 := by
      have : (MulAut.congr eA.symm) m = (MulAut.congr eA.symm) 1 := by rw [map_one]; exact h
      exact (MulAut.congr eA.symm).injective this
    apply hdC
    intro x hx
    have h3 := congrArg (fun m' : MulAut A => ((m' ⟨x, hx⟩ : A) : G)) hm
    have h4 : d * x * d⁻¹ = x := h3
    rw [hdinv] at h4
    calc d * x = d * x * (d * d) := by rw [hd2, mul_one]
      _ = (d * x * d) * d := by rw [mul_assoc (d * x) d d]
      _ = x * d := by rw [h4]
  obtain ⟨w', hw'⟩ := q8_w_lemma β hβ2 hβ1
  refine ⟨(eA w' : G), (eA w').2, ?_⟩
  have h6 : eA (β w') = m (eA w') := by simp [β, MulAut.congr_apply]
  have h7 : (m (eA w') : G) = d * (eA w' : G) * d⁻¹ := rfl
  have h8 : d * (eA w' : G) * d⁻¹ = (eA w' : G) * (eA (a 2) : G) := by
    rw [← h7, ← h6, hw', map_mul]; rfl
  rw [hdinv] at h8
  have h9 : d * (eA w' : G) = (eA w' : G) * (eA (a 2) : G) * d := by
    calc d * (eA w' : G) = d * (eA w' : G) * (d * d) := by rw [hd2, mul_one]
      _ = (d * (eA w' : G) * d) * d := by rw [mul_assoc (d * (eA w' : G)) d d]
      _ = (eA w' : G) * (eA (a 2) : G) * d := by rw [h8]
  calc (eA w' : G)⁻¹ * d * (eA w' : G) = (eA w' : G)⁻¹ * (d * (eA w' : G)) := by rw [mul_assoc]
    _ = (eA w' : G)⁻¹ * ((eA w' : G) * (eA (a 2) : G) * d) := by rw [h9]
    _ = (eA (a 2) : G) * d := by group

theorem q8_not_faithful_perm {n : ℕ} (hn : n < 8) (f : QuaternionGroup 2 →* Equiv.Perm (Fin n)) :
    ¬ Function.Injective f := by
  intro hf
  have h2 : (a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have hmove : ∃ p, f (a 2) p ≠ p := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    apply h2
    apply hf
    ext p
    simp [h p]
  obtain ⟨p, hp⟩ := hmove
  have hq : ∀ g : QuaternionGroup 2, g ≠ 1 → g = a 2 ∨ g ^ 2 = a 2 := by decide
  have hstab : ∀ g : QuaternionGroup 2, f g p = p → g = 1 := by
    intro g hg
    by_contra hne
    rcases hq g hne with h | h
    · subst h; exact hp hg
    · apply hp
      rw [← h, map_pow, pow_two, Equiv.Perm.mul_apply, hg, hg]
  have hinj : Function.Injective (fun g : QuaternionGroup 2 => f g p) := by
    intro g h hgh
    have h1 : f (h⁻¹ * g) p = p := by
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
      simp only at hgh
      rw [hgh]
      simp
    exact (inv_mul_eq_one.mp (hstab _ h1)).symm
  have hc := Fintype.card_le_of_injective _ hinj
  rw [QuaternionGroup.card] at hc
  simp at hc
  omega

end CFSG.ClassicalInvolution
