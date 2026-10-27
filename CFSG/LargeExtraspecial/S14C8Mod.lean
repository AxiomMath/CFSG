module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.LargeExtraspecial.S14

open Subgroup

variable {X : Type*} [Group X]

structure InvolSetup (N R : Subgroup X) (t τ : X) : Prop where
  t_mem : t ∈ N
  t_comm : ∀ n ∈ N, n * t = t * n
  comm_mem : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ zpowers t
  sq_mem : ∀ x ∈ N, x * x ∈ zpowers t
  conj_R : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N
  R_comm : ∀ r ∈ R, r * t = t * r
  conj_τ : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N
  τ_comm : τ * t = t * τ
  τ_sq : τ * τ = 1
  comm_τ : ∀ r ∈ R, r * τ * r⁻¹ * τ⁻¹ ∈ N

theorem conj_zpowers_eq {t n c : X} (hn : n * t = t * n) (hc : c ∈ zpowers t) :
    n * c * n⁻¹ = c := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  rw [(Commute.zpow_right hn k).eq, mul_inv_cancel_right]

@[expose] def commSpan (N : Subgroup X) (t τ : X) : Subgroup X :=
  closure (insert t {x | ∃ n ∈ N, x = n * τ * n⁻¹ * τ⁻¹})

@[expose] def centMod (N : Subgroup X) (t τ : X) (ht : ∀ n ∈ N, n * t = t * n) :
    Subgroup X where
  carrier := {n | n ∈ N ∧ n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : a * b * τ * (a * b)⁻¹ * τ⁻¹ =
        (a * (b * τ * b⁻¹ * τ⁻¹) * a⁻¹) * (a * τ * a⁻¹ * τ⁻¹) := by group
    rw [e, conj_zpowers_eq (ht a ha) hb']
    exact mul_mem hb' ha'
  one_mem' := ⟨one_mem _, by rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : a⁻¹ * τ * a⁻¹⁻¹ * τ⁻¹ = a⁻¹ * (a * τ * a⁻¹ * τ⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e, conj_zpowers_eq (ht _ (inv_mem ha)) (inv_mem ha')]
    exact inv_mem ha'

theorem comm_mem_commSpan {N : Subgroup X} {t τ n : X} (hn : n ∈ N) :
    n * τ * n⁻¹ * τ⁻¹ ∈ commSpan N t τ :=
  subset_closure (Set.mem_insert_of_mem _ ⟨n, hn, rfl⟩)

theorem zpowers_le_commSpan {N : Subgroup X} {t τ : X} : zpowers t ≤ commSpan N t τ :=
  zpowers_le.mpr (subset_closure (Set.mem_insert _ _))

namespace InvolSetup

variable {N R : Subgroup X} {t τ : X} (hs : InvolSetup N R t τ)
include hs

theorem inv_τ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hs.τ_sq

theorem comm_τ_mem {n : X} (hn : n ∈ N) : n * τ * n⁻¹ * τ⁻¹ ∈ N := by
  have e : n * τ * n⁻¹ * τ⁻¹ = n * (τ * n⁻¹ * τ⁻¹) := by group
  rw [e]
  exact mul_mem hn (hs.conj_τ _ (inv_mem hn))

theorem conj_mem_of_le {U : Subgroup X} (hU : zpowers t ≤ U) (hUN : U ≤ N) {m u : X}
    (hm : m ∈ N) (hu : u ∈ U) : m * u * m⁻¹ ∈ U := by
  have e : m * u * m⁻¹ = (m * u * m⁻¹ * u⁻¹) * u := by group
  rw [e]
  exact mul_mem (hU (hs.comm_mem _ hm _ (hUN hu))) hu

theorem commSpan_le : commSpan N t τ ≤ N := by
  refine (closure_le _).mpr ?_
  rintro x (rfl | ⟨n, hn, rfl⟩)
  · exact hs.t_mem
  · exact hs.comm_τ_mem hn

theorem comm_comm_eq (n : X) :
    (n * τ * n⁻¹ * τ⁻¹) * τ * (n * τ * n⁻¹ * τ⁻¹)⁻¹ * τ⁻¹ =
      (n * τ * n⁻¹ * τ⁻¹) * (n * τ * n⁻¹ * τ⁻¹) := by
  have h1 : ∀ y : X, τ * (τ * y) = y := fun y => by rw [← mul_assoc, hs.τ_sq, one_mul]
  simp only [mul_inv_rev, inv_inv, hs.inv_τ, mul_assoc, h1]

theorem commSpan_le_centMod : commSpan N t τ ≤ centMod N t τ hs.t_comm := by
  refine (closure_le _).mpr ?_
  rintro x (rfl | ⟨n, hn, rfl⟩)
  · refine ⟨hs.t_mem, ?_⟩
    rw [← hs.τ_comm, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · refine ⟨hs.comm_τ_mem hn, ?_⟩
    rw [hs.comm_comm_eq n]
    exact hs.sq_mem _ (hs.comm_τ_mem hn)

theorem comm_mem_of_mem_commSpan {d : X} (hd : d ∈ commSpan N t τ) :
    d * τ * d⁻¹ * τ⁻¹ ∈ zpowers t :=
  (hs.commSpan_le_centMod hd).2

theorem conj_mem_commSpan {r : X} (hr : r ∈ R) {d : X} (hd : d ∈ commSpan N t τ) :
    r * d * r⁻¹ ∈ commSpan N t τ := by
  induction hd using closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨n, hn, rfl⟩
    · rw [hs.R_comm r hr, mul_inv_cancel_right]
      exact subset_closure (Set.mem_insert _ _)
    · set a := r * n * r⁻¹ with ha
      set m := r * τ * r⁻¹ * τ⁻¹ with hm
      have haN : a ∈ N := hs.conj_R r hr n hn
      have hmN : m ∈ N := hs.comm_τ r hr
      have hcN := hs.comm_τ_mem haN
      have e : r * (n * τ * n⁻¹ * τ⁻¹) * r⁻¹ = (a * m * a⁻¹ * m⁻¹) * (a * τ * a⁻¹ * τ⁻¹) *
          ((a * τ * a⁻¹ * τ⁻¹)⁻¹ * m * (a * τ * a⁻¹ * τ⁻¹)⁻¹⁻¹ * m⁻¹) := by
        rw [ha, hm]; group
      rw [e]
      refine mul_mem (mul_mem (zpowers_le_commSpan (hs.comm_mem _ haN _ hmN))
        (comm_mem_commSpan haN)) (zpowers_le_commSpan (hs.comm_mem _ (inv_mem hcN) _ hmN))
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul x y _ _ hx hy =>
    have e : r * (x * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : r * x⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem comm_mem_of_irred
    (hirr : ∀ D : Subgroup X, zpowers t ≤ D → D ≤ N → (∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D) →
      D = zpowers t ∨ D = N) {n : X} (hn : n ∈ N) : n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t := by
  rcases hirr _ zpowers_le_commSpan hs.commSpan_le (fun r hr d hd => hs.conj_mem_commSpan hr hd)
    with h | h
  · rw [← h]
    exact comm_mem_commSpan hn
  · exact hs.comm_mem_of_mem_commSpan (by rw [h]; exact hn)

theorem comm_mem_of_two_aux {Ui Uj : Subgroup X} (hit : zpowers t ≤ Ui) (hiN : Ui ≤ N)
    (hiR : ∀ r ∈ R, ∀ u ∈ Ui, r * u * r⁻¹ ∈ Ui) (hjt : zpowers t ≤ Uj) (hjN : Uj ≤ N)
    (hjR : ∀ r ∈ R, ∀ u ∈ Uj, r * u * r⁻¹ ∈ Uj) (hinf : Ui ⊓ Uj = zpowers t)
    (hci : Nat.card Ui = 2 ^ 5) (hcj : Nat.card Uj = 2 ^ 5) (hct : Nat.card (zpowers t) = 2)
    (hcN : Nat.card N ≠ 2 ^ 5)
    (hlat : ∀ D : Subgroup X, zpowers t ≤ D → D ≤ N → (∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D) →
      D = zpowers t ∨ D = Ui ∨ D = Uj ∨ D = N)
    (hD : commSpan N t τ = Ui) {n : X} (hn : n ∈ N) : n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t := by
  have : Finite (zpowers t) := Nat.finite_of_card_ne_zero (by rw [hct]; norm_num)
  have hnot : ∀ U : Subgroup X, Nat.card U = 2 ^ 5 → ¬ U ≤ zpowers t := fun U hU hle => by
    have := Subgroup.card_le_of_le hle
    rw [hU, hct] at this
    norm_num at this
  have hτt' : τ⁻¹ * t = t * τ⁻¹ := by rw [hs.inv_τ]; exact hs.τ_comm
  have hτi : ∀ u ∈ Ui, τ⁻¹ * u * τ ∈ Ui := fun u hu => by
    have hc := hs.comm_mem_of_mem_commSpan (by rw [hD]; exact hu)
    have e : τ⁻¹ * u * τ = (τ⁻¹ * (u * τ * u⁻¹ * τ⁻¹) * τ⁻¹⁻¹) * u := by group
    rw [e, conj_zpowers_eq hτt' hc]
    exact mul_mem (hit hc) hu
  set E := Uj.map (MulAut.conj τ).toMonoidHom with hEdef
  have hEmem : ∀ w ∈ Uj, τ * w * τ⁻¹ ∈ E := fun w hw => ⟨w, hw, rfl⟩
  have hEt : zpowers t ≤ E := by
    rw [zpowers_le]
    have := hEmem t (hjt (mem_zpowers t))
    rwa [hs.τ_comm, mul_inv_cancel_right] at this
  have hEN : E ≤ N := by
    rintro _ ⟨w, hw, rfl⟩
    exact hs.conj_τ w (hjN hw)
  have hER : ∀ r ∈ R, ∀ e ∈ E, r * e * r⁻¹ ∈ E := by
    rintro r hr _ ⟨w, hw, rfl⟩
    have hmN : r⁻¹ * τ⁻¹ * r * τ ∈ N := by
      have := hs.comm_τ r⁻¹ (inv_mem hr)
      rw [inv_inv] at this
      rw [hs.inv_τ] at this ⊢
      exact this
    have hw' := hjR r hr _ (hs.conj_mem_of_le hjt hjN hmN hw)
    have e : r * ((MulAut.conj τ).toMonoidHom w) * r⁻¹ = τ * (r * ((r⁻¹ * τ⁻¹ * r * τ) * w *
        (r⁻¹ * τ⁻¹ * r * τ)⁻¹) * r⁻¹) * τ⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hEmem _ hw'
  have hcE : Nat.card E = 2 ^ 5 := by
    rw [hEdef, card_map_of_injective (MulAut.conj τ).injective]
    exact hcj
  rcases hlat E hEt hEN hER with hE | hE | hE | hE
  · rw [hE, hct] at hcE
    norm_num at hcE
  ·
    refine absurd ?_ (hnot Uj hcj)
    rw [← hinf]
    refine le_inf (fun w hw => ?_) le_rfl
    have := hτi _ (hE ▸ hEmem w hw)
    rwa [show τ⁻¹ * (τ * w * τ⁻¹) * τ = w by group] at this
  ·
    have hj : ∀ w ∈ Uj, w * τ * w⁻¹ * τ⁻¹ ∈ zpowers t := fun w hw => by
      have h1 : w * τ * w⁻¹ * τ⁻¹ ∈ Uj := by
        have e : w * τ * w⁻¹ * τ⁻¹ = w * (τ * w * τ⁻¹)⁻¹ := by group
        rw [e]
        exact mul_mem hw (inv_mem (hE ▸ hEmem w hw))
      have h2 : w * τ * w⁻¹ * τ⁻¹ ∈ Ui := hD ▸ comm_mem_commSpan (hjN hw)
      rw [← hinf]
      exact ⟨h2, h1⟩
    have hsupR : ∀ r ∈ R, ∀ d ∈ Ui ⊔ Uj, r * d * r⁻¹ ∈ Ui ⊔ Uj := by
      intro r hr d hd
      have hle : (Ui ⊔ Uj).map (MulAut.conj r).toMonoidHom ≤ Ui ⊔ Uj := by
        rw [Subgroup.map_sup]
        refine sup_le_sup ?_ ?_
        · rintro _ ⟨u, hu, rfl⟩
          exact hiR r hr u hu
        · rintro _ ⟨u, hu, rfl⟩
          exact hjR r hr u hu
      exact hle ⟨d, hd, rfl⟩
    have hjle : ¬ Uj ≤ Ui := fun h => hnot Uj hcj (hinf ▸ le_inf h le_rfl)
    rcases hlat (Ui ⊔ Uj) (hit.trans le_sup_left) (sup_le hiN hjN) hsupR with h | h | h | h
    · exact absurd (le_sup_left.trans h.le) (hnot Ui hci)
    · exact absurd (le_sup_right.trans h.le) hjle
    · exact absurd (hinf ▸ le_inf le_rfl (le_sup_left.trans h.le)) (hnot Ui hci)
    · have hle : Ui ⊔ Uj ≤ centMod N t τ hs.t_comm :=
        sup_le (hD ▸ hs.commSpan_le_centMod) fun w hw => ⟨hjN hw, hj w hw⟩
      exact (hle (by rw [h]; exact hn)).2
  · rw [hE] at hcE
    exact absurd hcE hcN

theorem comm_mem_of_two {U₁ U₂ : Subgroup X} (h1t : zpowers t ≤ U₁) (h1N : U₁ ≤ N)
    (h2t : zpowers t ≤ U₂) (h2N : U₂ ≤ N) (h1R : ∀ r ∈ R, ∀ u ∈ U₁, r * u * r⁻¹ ∈ U₁)
    (h2R : ∀ r ∈ R, ∀ u ∈ U₂, r * u * r⁻¹ ∈ U₂) (hinf : U₁ ⊓ U₂ = zpowers t)
    (hc1 : Nat.card U₁ = 2 ^ 5) (hc2 : Nat.card U₂ = 2 ^ 5) (hct : Nat.card (zpowers t) = 2)
    (hcN : Nat.card N ≠ 2 ^ 5)
    (hlat : ∀ D : Subgroup X, zpowers t ≤ D → D ≤ N → (∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D) →
      D = zpowers t ∨ D = U₁ ∨ D = U₂ ∨ D = N) {n : X} (hn : n ∈ N) :
    n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t := by
  rcases hlat _ zpowers_le_commSpan hs.commSpan_le (fun r hr d hd => hs.conj_mem_commSpan hr hd)
    with h | h | h | h
  · rw [← h]
    exact comm_mem_commSpan hn
  · exact hs.comm_mem_of_two_aux h1t h1N h1R h2t h2N h2R hinf hc1 hc2 hct hcN hlat h hn
  · refine hs.comm_mem_of_two_aux h2t h2N h2R h1t h1N h1R (by rw [inf_comm, hinf]) hc2 hc1 hct
      hcN (fun D hD1 hD2 hD3 => ?_) h hn
    rcases hlat D hD1 hD2 hD3 with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr h'))
  · exact hs.comm_mem_of_mem_commSpan (by rw [h]; exact hn)

end InvolSetup

end CFSG.LargeExtraspecial.S14
