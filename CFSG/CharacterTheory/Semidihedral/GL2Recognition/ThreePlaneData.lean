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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.Semidihedral.GL2Recognition

@[expose] def planeVec : Fin 13 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1],
    ![1, 2, 0], ![1, 0, 2], ![0, 1, 2], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2]]

@[expose] def planeDot (u v : Fin 3 → ZMod 3) : ZMod 3 := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

@[expose] def PlaneIncident (i j : Fin 13) : Prop := planeDot (planeVec j) (planeVec i) = 0

instance : DecidableRel PlaneIncident := fun _ _ => inferInstanceAs (Decidable (_ = _))

@[expose] def planeLine (j : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun i => PlaneIncident i j

@[expose] def planeDet (u v w : Fin 3 → ZMod 3) : ZMod 3 :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

@[expose] def PlaneCollinear (a b c : Fin 13) : Prop :=
  ∃ j, a ∈ planeLine j ∧ b ∈ planeLine j ∧ c ∈ planeLine j

instance (a b c : Fin 13) : Decidable (PlaneCollinear a b c) := by
  unfold PlaneCollinear; infer_instance

@[expose] def IsPlaneFrame (q : Fin 13 × Fin 13 × Fin 13 × Fin 13) : Prop :=
  planeDet (planeVec q.1) (planeVec q.2.1) (planeVec q.2.2.1) ≠ 0 ∧
  planeDet (planeVec q.1) (planeVec q.2.1) (planeVec q.2.2.2) ≠ 0 ∧
  planeDet (planeVec q.1) (planeVec q.2.2.1) (planeVec q.2.2.2) ≠ 0 ∧
  planeDet (planeVec q.2.1) (planeVec q.2.2.1) (planeVec q.2.2.2) ≠ 0

instance : DecidablePred IsPlaneFrame := fun q => by unfold IsPlaneFrame; infer_instance

theorem planeVec_ne_zero : ∀ i, planeVec i ≠ 0 := by decide

theorem eq_of_unit_smul_planeVec : ∀ i j (c : (ZMod 3)ˣ), c • planeVec i = planeVec j → i = j := by
  decide

theorem exists_unit_smul_planeVec : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    ∃ i, ∃ c : (ZMod 3)ˣ, c • planeVec i = v := by decide

theorem planeLine_injective : ∀ j j', planeLine j = planeLine j' → j = j' := by decide

theorem exists_planeLine_mem : ∀ a b, ∃ j, a ∈ planeLine j ∧ b ∈ planeLine j := by decide

theorem eq_of_mem_planeLine : ∀ a b, a ≠ b → ∀ j j', a ∈ planeLine j → b ∈ planeLine j →
    a ∈ planeLine j' → b ∈ planeLine j' → j = j' := by decide

theorem planeCollinear_iff : ∀ a b c, PlaneCollinear a b c ↔
    planeDet (planeVec a) (planeVec b) (planeVec c) = 0 := by decide

@[expose] def IsPlaneMeet (m a b c d : Fin 13) : Prop :=
  ∀ x, PlaneCollinear a b x ∧ PlaneCollinear c d x ↔ x = m

instance (m a b c d : Fin 13) : Decidable (IsPlaneMeet m a b c d) := by
  unfold IsPlaneMeet; infer_instance

theorem planeMeet_steps : IsPlaneMeet 4 0 1 2 3 ∧ IsPlaneMeet 5 0 2 1 3 ∧ IsPlaneMeet 6 0 3 1 2 ∧
    IsPlaneMeet 7 0 1 5 6 ∧ IsPlaneMeet 8 0 2 4 6 ∧ IsPlaneMeet 9 1 2 4 5 ∧
    IsPlaneMeet 10 2 3 5 6 ∧ IsPlaneMeet 11 1 3 4 6 ∧ IsPlaneMeet 12 0 3 4 5 := by decide

theorem card_planeFrame : Fintype.card {q // IsPlaneFrame q} = 5616 := by decide +kernel

theorem isPlaneFrame_standard : IsPlaneFrame (0, 1, 2, 3) := by decide

@[expose] def IsPlaneCollineation (σ : Equiv.Perm (Fin 13)) : Prop :=
  ∀ j, ∃ j', (planeLine j).map σ.toEmbedding = planeLine j'

theorem PlaneCollinear.map {σ : Equiv.Perm (Fin 13)} (hσ : IsPlaneCollineation σ) {a b c : Fin 13}
    (h : PlaneCollinear a b c) : PlaneCollinear (σ a) (σ b) (σ c) := by
  obtain ⟨j, ha, hb, hc⟩ := h
  obtain ⟨j', hj'⟩ := hσ j
  refine ⟨j', ?_, ?_, ?_⟩ <;> rw [← hj'] <;> exact Finset.mem_map_of_mem _ ‹_›

theorem fix_of_isPlaneMeet {σ : Equiv.Perm (Fin 13)} (hσ : IsPlaneCollineation σ)
    {m a b c d : Fin 13} (h : IsPlaneMeet m a b c d) (ha : σ a = a) (hb : σ b = b)
    (hc : σ c = c) (hd : σ d = d) : σ m = m := by
  have hm := (h m).mpr rfl
  apply (h (σ m)).mp
  constructor
  · have := hm.1.map hσ
    rwa [ha, hb] at this
  · have := hm.2.map hσ
    rwa [hc, hd] at this

theorem eq_one_of_isPlaneCollineation {σ : Equiv.Perm (Fin 13)} (hσ : IsPlaneCollineation σ)
    (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 2) (h3 : σ 3 = 3) : σ = 1 := by
  obtain ⟨s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ := planeMeet_steps
  have h4 := fix_of_isPlaneMeet hσ s4 h0 h1 h2 h3
  have h5 := fix_of_isPlaneMeet hσ s5 h0 h2 h1 h3
  have h6 := fix_of_isPlaneMeet hσ s6 h0 h3 h1 h2
  have h7 := fix_of_isPlaneMeet hσ s7 h0 h1 h5 h6
  have h8 := fix_of_isPlaneMeet hσ s8 h0 h2 h4 h6
  have h9 := fix_of_isPlaneMeet hσ s9 h1 h2 h4 h5
  have h10 := fix_of_isPlaneMeet hσ s10 h2 h3 h5 h6
  have h11 := fix_of_isPlaneMeet hσ s11 h1 h3 h4 h6
  have h12 := fix_of_isPlaneMeet hσ s12 h0 h3 h4 h5
  ext i
  fin_cases i <;> simp_all

theorem isPlaneFrame_map {σ : Equiv.Perm (Fin 13)} (hσ : IsPlaneCollineation σ⁻¹)
    {q : Fin 13 × Fin 13 × Fin 13 × Fin 13} (hq : IsPlaneFrame q) :
    IsPlaneFrame (σ q.1, σ q.2.1, σ q.2.2.1, σ q.2.2.2) := by
  have key : ∀ a b c : Fin 13, planeDet (planeVec a) (planeVec b) (planeVec c) ≠ 0 →
      planeDet (planeVec (σ a)) (planeVec (σ b)) (planeVec (σ c)) ≠ 0 := by
    intro a b c h h'
    apply h
    rw [← planeCollinear_iff] at h' ⊢
    have := h'.map hσ
    simpa using this
  obtain ⟨h1, h2, h3, h4⟩ := hq
  exact ⟨key _ _ _ h1, key _ _ _ h2, key _ _ _ h3, key _ _ _ h4⟩

theorem isPlaneFrame_map_standard {σ : Equiv.Perm (Fin 13)} (hσ : IsPlaneCollineation σ⁻¹) :
    IsPlaneFrame (σ 0, σ 1, σ 2, σ 3) :=
  isPlaneFrame_map (q := (0, 1, 2, 3)) hσ isPlaneFrame_standard

theorem card_le_of_forall_isPlaneCollineation (Γ : Subgroup (Equiv.Perm (Fin 13)))
    (hΓ : ∀ γ ∈ Γ, IsPlaneCollineation γ) : Nat.card Γ ≤ 5616 := by
  let f : Γ → {q // IsPlaneFrame q} := fun γ =>
    ⟨((γ : Equiv.Perm (Fin 13)) 0, (γ : Equiv.Perm (Fin 13)) 1, (γ : Equiv.Perm (Fin 13)) 2,
      (γ : Equiv.Perm (Fin 13)) 3), isPlaneFrame_map_standard (hΓ _ (Γ.inv_mem γ.2))⟩
  have hf : Function.Injective f := by
    intro γ γ' h
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    have hδ := hΓ _ (Γ.mul_mem (Γ.inv_mem γ'.2) γ.2)
    have he := eq_one_of_isPlaneCollineation hδ (by simp [Equiv.Perm.mul_apply, h0])
      (by simp [Equiv.Perm.mul_apply, h1]) (by simp [Equiv.Perm.mul_apply, h2])
      (by simp [Equiv.Perm.mul_apply, h3])
    exact Subtype.ext (inv_mul_eq_one.mp he).symm
  calc Nat.card Γ ≤ Nat.card {q // IsPlaneFrame q} := Nat.card_le_card_of_injective f hf
    _ = 5616 := by rw [Nat.card_eq_fintype_card, card_planeFrame]

end CFSG.Semidihedral.GL2Recognition
