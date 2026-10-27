module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem polar_self_zero (x : V) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_mul]

theorem add_self_eq_zero' (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_smul]

theorem add_self_eq_zero'' (c : ZMod 2) : c + c = 0 := by
  revert c
  decide

theorem eq_of_add_eq_zero'' {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b
  decide

theorem eq_of_add_eq_zero' {a b : V} (h : a + b = 0) : a = b := by
  rw [eq_neg_of_add_eq_zero_left h]
  exact neg_eq_of_add_eq_zero_right (add_self_eq_zero' b)

structure AnisoPair (Q : QuadraticForm (ZMod 2) V) where
  a : V
  b : V
  Q_a : Q a = 1
  Q_b : Q b = 1
  polar_ab : polar Q a b = 1

namespace AnisoPair

variable (P P' : AnisoPair Q)

theorem polar_ba : polar Q P.b P.a = 1 := by rw [polar_comm, P.polar_ab]

theorem polar_aa : polar Q P.a P.a = 0 := polar_self_zero _

theorem polar_bb : polar Q P.b P.b = 0 := polar_self_zero _

theorem a_ne_b : P.a ≠ P.b := by
  intro h
  have := P.polar_ab
  rw [← h, P.polar_aa] at this
  exact zero_ne_one this

structure Orth (P P' : AnisoPair Q) : Prop where
  aa : polar Q P.a P'.a = 0
  ab : polar Q P.a P'.b = 0
  ba : polar Q P.b P'.a = 0
  bb : polar Q P.b P'.b = 0

theorem Orth.symm {P P' : AnisoPair Q} (h : P.Orth P') : P'.Orth P where
  aa := by rw [polar_comm, h.aa]
  ab := by rw [polar_comm, h.ba]
  ba := by rw [polar_comm, h.ab]
  bb := by rw [polar_comm, h.bb]

def perp : Submodule (ZMod 2) V :=
  LinearMap.ker (polarBilin Q P.a) ⊓ LinearMap.ker (polarBilin Q P.b)

theorem mem_perp {u : V} : u ∈ P.perp ↔ polar Q P.a u = 0 ∧ polar Q P.b u = 0 := by
  simp [AnisoPair.perp]

def plane : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {P.a, P.b}

theorem a_mem_plane : P.a ∈ P.plane := Submodule.subset_span (by simp)

theorem b_mem_plane : P.b ∈ P.plane := Submodule.subset_span (by simp)

def proj (v : V) : V := polar Q v P.b • P.a + polar Q v P.a • P.b

theorem proj_mem_plane (v : V) : P.proj v ∈ P.plane :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ P.a_mem_plane) (Submodule.smul_mem _ _ P.b_mem_plane)

theorem add_proj_mem_perp (v : V) : v + P.proj v ∈ P.perp := by
  rw [mem_perp, proj]
  have h1 := P.polar_ab
  have h2 := P.polar_ba
  have h3 := P.polar_aa
  have h4 := P.polar_bb
  constructor
  · rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h3, h1,
      polar_comm Q P.a v]
    ring_nf
    rw [show (2 : ZMod 2) = 0 from rfl]
    ring
  · rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h2, h4,
      polar_comm Q P.b v]
    ring_nf
    rw [show (2 : ZMod 2) = 0 from rfl]
    ring

theorem plane_inf_perp : P.plane ⊓ P.perp = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.1 hu
  rw [AnisoPair.mem_perp] at hu2
  rw [AnisoPair.plane, Submodule.mem_span_pair] at hu1
  obtain ⟨s, t, rfl⟩ := hu1
  have h1 := hu2.1
  have h2 := hu2.2
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_aa, P.polar_ab] at h1
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ba, P.polar_bb] at h2
  simp only [mul_zero, mul_one, zero_add, add_zero] at h1 h2
  rw [h1, h2]
  simp

theorem linearIndependent_pair : LinearIndependent (ZMod 2) ![P.a, P.b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun v => polar Q v P.b) hst
  have h2 := congrArg (fun v => polar Q v P.a) hst
  simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, P.polar_ab, P.polar_bb,
    P.polar_ba, P.polar_aa, mul_one, mul_zero, add_zero, zero_add] at h1 h2
  exact ⟨h1, h2⟩

theorem finrank_plane : finrank (ZMod 2) P.plane = 2 := by
  rw [AnisoPair.plane, ← Matrix.range_cons_cons_empty P.a P.b ![],
    finrank_span_eq_card P.linearIndependent_pair, Fintype.card_fin]

end AnisoPair

variable {P P' : AnisoPair Q}

theorem PolarNondegOn.inf_perp_aniso {W : Submodule (ZMod 2) V} (hW : PolarNondegOn Q W)
    (P : AnisoPair Q) (ha : P.a ∈ W) (hb : P.b ∈ W) : PolarNondegOn Q (W ⊓ P.perp) := by
  intro u hu hu0
  rw [Submodule.mem_inf] at hu
  apply hW u hu.1
  intro w hw
  have hpw : w + P.proj w ∈ W ⊓ P.perp := by
    refine ⟨?_, P.add_proj_mem_perp w⟩
    exact W.add_mem hw (W.add_mem (W.smul_mem _ ha) (W.smul_mem _ hb))
  have hu2 := (AnisoPair.mem_perp P).1 hu.2
  have h1 := hu0 _ hpw
  have h2 : polar Q u (P.proj w) = 0 := by
    rw [AnisoPair.proj, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q u P.a, polar_comm Q u P.b, hu2.1, hu2.2]
    ring
  rw [polar_add_right, h2, add_zero] at h1
  exact h1

theorem finrank_inf_perp [FiniteDimensional (ZMod 2) V] {W : Submodule (ZMod 2) V}
    (P : AnisoPair Q) (ha : P.a ∈ W) (hb : P.b ∈ W) :
    finrank (ZMod 2) W = finrank (ZMod 2) ↥(W ⊓ P.perp) + 2 := by
  have hplane : P.plane ≤ W := by
    rw [AnisoPair.plane, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hb
  have hsup : P.plane ⊔ (W ⊓ P.perp) = W := by
    refine le_antisymm (sup_le hplane inf_le_left) ?_
    intro w hw
    have h1 : w + P.proj w ∈ W ⊓ P.perp := by
      refine ⟨?_, P.add_proj_mem_perp w⟩
      exact W.add_mem hw (W.add_mem (W.smul_mem _ ha) (W.smul_mem _ hb))
    have h2 : w = P.proj w + (w + P.proj w) := by
      rw [add_comm (P.proj w) (w + P.proj w), add_assoc, add_self_eq_zero', add_zero]
    rw [h2]
    exact Submodule.add_mem_sup (P.proj_mem_plane w) h1
  have hinf : P.plane ⊓ (W ⊓ P.perp) = ⊥ := by
    rw [eq_bot_iff, ← P.plane_inf_perp]
    exact inf_le_inf_left _ inf_le_right
  have := Submodule.finrank_sup_add_finrank_inf_eq P.plane (W ⊓ P.perp)
  rw [hsup, hinf, finrank_bot, P.finrank_plane] at this
  omega

end CFSG.AGLEmbedding.OmegaMinusCent
