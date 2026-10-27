module

public import CFSG.Certificates.Kernel.Local.Core
public import CFSG.Certificates.Kernel.Spor.Loops
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.Fin76bOm

open Equiv Subgroup

variable {n k : ℕ}

@[expose] def restrSub (Ω : Fin k → Fin n) : Subgroup (Perm (Fin n)) where
  carrier := {σ | ∃ τ : Perm (Fin k), ∀ j, σ (Ω j) = Ω (τ j)}
  one_mem' := ⟨1, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨τa, ha⟩ ⟨τb, hb⟩
    exact ⟨τa * τb, fun j => by rw [Perm.mul_apply, hb, ha, Perm.mul_apply]⟩
  inv_mem' := by
    rintro a ⟨τ, ha⟩
    refine ⟨τ⁻¹, fun j => ?_⟩
    rw [Perm.inv_eq_iff_eq, ha]
    simp

variable {Ω : Fin k → Fin n}

theorem restr_unique (hΩ : Function.Injective Ω) {σ : Perm (Fin n)} {τ τ' : Perm (Fin k)}
    (h : ∀ j, σ (Ω j) = Ω (τ j)) (h' : ∀ j, σ (Ω j) = Ω (τ' j)) : τ = τ' :=
  Equiv.ext fun j => hΩ ((h j).symm.trans (h' j))

@[expose] noncomputable def restrHom (hΩ : Function.Injective Ω) : restrSub Ω →* Perm (Fin k) where
  toFun σ := Classical.choose σ.2
  map_one' := restr_unique hΩ (Classical.choose_spec (one_mem (restrSub Ω))) fun _ => rfl
  map_mul' σ₁ σ₂ := restr_unique hΩ (Classical.choose_spec (σ₁ * σ₂).2) fun j => by
    rw [Subgroup.coe_mul, Perm.mul_apply, Classical.choose_spec σ₂.2 j,
      Classical.choose_spec σ₁.2, Perm.mul_apply]

theorem restrHom_spec (hΩ : Function.Injective Ω) (σ : restrSub Ω) (j : Fin k) :
    (σ : Perm (Fin n)) (Ω j) = Ω (restrHom hΩ σ j) :=
  Classical.choose_spec σ.2 j

theorem restrHom_eq (hΩ : Function.Injective Ω) {σ : restrSub Ω} {τ : Perm (Fin k)}
    (h : ∀ j, (σ : Perm (Fin n)) (Ω j) = Ω (τ j)) : restrHom hΩ σ = τ :=
  restr_unique hΩ (restrHom_spec hΩ σ) h

variable {N : ℕ} {gs : ℕ → Perm (Fin n)} {rs : ℕ → Perm (Fin k)}

theorem closure_le_restrSub (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j)) :
    closure (gs '' {l | l < N}) ≤ restrSub Ω := by
  rw [closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨rs l, hc l hl⟩

@[expose] noncomputable def restrictHom (hΩ : Function.Injective Ω)
    (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j)) :
    closure (gs '' {l | l < N}) →* Perm (Fin k) :=
  (restrHom hΩ).comp (inclusion (closure_le_restrSub hc))

theorem restrictHom_gen (hΩ : Function.Injective Ω) (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    {l : ℕ} (hl : l < N) :
    restrictHom hΩ hc ⟨gs l, subset_closure ⟨l, hl, rfl⟩⟩ = rs l :=
  restrHom_eq hΩ (hc l hl)

theorem closure_le_range (hΩ : Function.Injective Ω) (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j)) :
    closure (rs '' {l | l < N}) ≤ (restrictHom hΩ hc).range := by
  rw [closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨_, restrictHom_gen hΩ hc hl⟩

theorem restrictHom_injective (hΩ : Function.Injective Ω)
    (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    (hcard : Nat.card (closure (gs '' {l | l < N})) = Nat.card (closure (rs '' {l | l < N}))) :
    Function.Injective (restrictHom hΩ hc) := by
  set φ := restrictHom hΩ hc
  have h1 : Nat.card (closure (gs '' {l | l < N})) = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have h2 : Nat.card (closure (rs '' {l | l < N})) ≤ Nat.card φ.range :=
    Subgroup.card_le_of_le (closure_le_range hΩ hc)
  have h3 : 0 < Nat.card φ.range := Nat.card_pos
  have h4 : Nat.card φ.ker ≤ 1 := by
    by_contra hk
    have : Nat.card φ.range * 2 ≤ Nat.card φ.range * Nat.card φ.ker :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  exact (MonoidHom.ker_eq_bot_iff φ).1 (Subgroup.eq_bot_of_card_le _ h4)

theorem restrictHom_range (hΩ : Function.Injective Ω)
    (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    (hcard : Nat.card (closure (gs '' {l | l < N})) = Nat.card (closure (rs '' {l | l < N}))) :
    (restrictHom hΩ hc).range = closure (rs '' {l | l < N}) := by
  refine (Subgroup.eq_of_le_of_card_ge (closure_le_range hΩ hc) ?_).symm
  rw [← hcard, ← Nat.card_congr (MonoidHom.ofInjective (restrictHom_injective hΩ hc hcard)).toEquiv]

@[expose] noncomputable def restrictEquiv (hΩ : Function.Injective Ω)
    (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    (hcard : Nat.card (closure (gs '' {l | l < N})) = Nat.card (closure (rs '' {l | l < N}))) :
    closure (gs '' {l | l < N}) ≃* closure (rs '' {l | l < N}) :=
  (MonoidHom.ofInjective (restrictHom_injective hΩ hc hcard)).trans
    (MulEquiv.subgroupCongr (restrictHom_range hΩ hc hcard))

open CFSG.KC.Enum CFSG.KC.Local

theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem blt_true {a b : ℕ} (h : Nat.blt a b = true) : a < b := by
  simpa using h

theorem strictB_eq' (y : ℕ) (f : ℕ → Bool) : strictB y f = f y := by
  cases y <;> rfl

theorem allL_spec {m : ℕ} {f : ℕ → Bool} (h : allL m f = true) : ∀ i < m, f i = true :=
  CFSG.KS.allN_spec (f := f) (n := m) h

theorem ptsOK_spec {PT pw pm : ℕ} (h : ptsOK n PT pw pm k = true) :
    (∀ a b, a < b → b < k → pg pw pm PT a < pg pw pm PT b) ∧
      ∀ j < k, pg pw pm PT j < n := by
  unfold ptsOK at h
  obtain ⟨h1, h2⟩ := bAnd_true h
  rw [show Nat.sub k 1 = k - 1 from rfl] at h1 h2
  have hstep := allL_spec h2
  have hmono : ∀ a b, a < b → b < k → pg pw pm PT a < pg pw pm PT b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hs := blt_true (hstep b (by omega))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
      · exact (ih hab (by omega)).trans hs
      · exact hs
  refine ⟨hmono, fun j hj => ?_⟩
  have hlast := blt_true h1
  rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt hj) with hj' | hj'
  · exact (hmono j (k - 1) hj' (by omega)).trans hlast
  · rw [hj']
    exact hlast

theorem restrOK_spec {w m p PT pw pm ρ rw rm : ℕ} (h : restrOK w m p PT pw pm k ρ rw rm = true) :
    ∀ j < k, pg rw rm ρ j < k ∧ pg pw pm PT (pg rw rm ρ j) = pg w m p (pg pw pm PT j) := by
  unfold restrOK at h
  obtain ⟨-, h2⟩ := bAnd_true h
  intro j hj
  have hj' := allL_spec h2 j hj
  rw [strictB_eq'] at hj'
  obtain ⟨h3, h4⟩ := bAnd_true hj'
  exact ⟨blt_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem restrData_of_checks {w m PT pw pm rw rm : ℕ} {P R : ℕ → ℕ}
    (hpts : ptsOK n PT pw pm k = true)
    (hres : ∀ l < N, restrOK w m (P l) PT pw pm k (R l) rw rm = true)
    (hg : ∀ l < N, ∀ i : Fin n, ((gs l i : Fin n) : ℕ) = pg w m (P l) i)
    (hr : ∀ l < N, ∀ j : Fin k, ((rs l j : Fin k) : ℕ) = pg rw rm (R l) j) :
    ∃ Ω : Fin k → Fin n, Function.Injective Ω ∧ ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j) := by
  obtain ⟨hmono, hlt⟩ := ptsOK_spec hpts
  refine ⟨fun j => ⟨pg pw pm PT j, hlt j j.2⟩, fun a b hab => ?_, fun l hl j => ?_⟩
  · have e : pg pw pm PT a = pg pw pm PT b := congrArg Fin.val hab
    rcases lt_trichotomy (a : ℕ) b with h | h | h
    · exact absurd e (hmono a b h b.2).ne
    · exact Fin.ext h
    · exact absurd e (hmono b a h a.2).ne'
  · apply Fin.ext
    rw [hg l hl]
    change pg w m (P l) (pg pw pm PT j) = pg pw pm PT (rs l j)
    rw [hr l hl]
    exact ((restrOK_spec (hres l hl) j j.2).2).symm

end CFSG.KC.Fin76bOm

end
