module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankWitt
public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankSplit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4

open QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace EFrame

theorem polar_comb_comb_of_perp {F G : EFrame Q} (h : F.Perp G) (α β γ δ : K) :
    polar Q (α • F.b + β • F.b') (γ • G.b + δ • G.b') = 0 := by
  have h1 : polar Q F.b G.b = 0 := by rw [polar_comm]; exact h.1.1
  have h2 : polar Q F.b' G.b = 0 := by rw [polar_comm]; exact h.1.2
  have h3 : polar Q F.b G.b' = 0 := by rw [polar_comm]; exact h.2.1
  have h4 : polar Q F.b' G.b' = 0 := by rw [polar_comm]; exact h.2.2
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, h1, h2, h3, h4,
    smul_eq_mul]
  ring

theorem q_two {F G : EFrame Q} (h : F.Perp G) (α β γ δ : K) :
    Q ((α • F.b + β • F.b') + (γ • G.b + δ • G.b')) =
      F.c * (α ^ 2 - α * β + β ^ 2) + G.c * (γ ^ 2 - γ * δ + δ ^ 2) := by
  rw [q_add, F.q_comb, G.q_comb, polar_comb_comb_of_perp h, add_zero]

theorem polar_two {F G : EFrame Q} (h : F.Perp G) (α β γ δ α' β' γ' δ' : K) :
    polar Q ((α • F.b + β • F.b') + (γ • G.b + δ • G.b'))
        ((α' • F.b + β' • F.b') + (γ' • G.b + δ' • G.b')) =
      F.c * (2 * α * α' - α * β' - β * α' + 2 * β * β') +
        G.c * (2 * γ * γ' - γ * δ' - δ * γ' + 2 * δ * δ') := by
  have h1 : polar Q F.b G.b = 0 := by rw [polar_comm]; exact h.1.1
  have h2 : polar Q F.b' G.b = 0 := by rw [polar_comm]; exact h.1.2
  have h3 : polar Q F.b G.b' = 0 := by rw [polar_comm]; exact h.2.1
  have h4 : polar Q F.b' G.b' = 0 := by rw [polar_comm]; exact h.2.2
  have h1' : polar Q G.b F.b = 0 := h.1.1
  have h2' : polar Q G.b F.b' = 0 := h.1.2
  have h3' : polar Q G.b' F.b = 0 := h.2.1
  have h4' : polar Q G.b' F.b' = 0 := h.2.2
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, F.polar_bb,
    F.polar_bb', F.polar_b'b, F.polar_b'b', G.polar_bb, G.polar_bb', G.polar_b'b, G.polar_b'b',
    h1, h2, h3, h4, h1', h2', h3', h4', smul_eq_mul]
  ring

theorem proj_comb_self (h3 : (3 : K) ≠ 0) (F : EFrame Q) (α β : K) :
    F.proj (α • F.b + β • F.b') = α • F.b + β • F.b' := by
  rw [map_add, map_smul, map_smul, F.proj_b h3, F.proj_b' h3]

theorem proj_comb_of_perp {F G : EFrame Q} (h : G.Perp F) (α β : K) :
    G.proj (α • F.b + β • F.b') = 0 :=
  G.proj_of_orth ((h.1.smul α).add (h.2.smul β))

theorem polar_comb_of_orth (F : EFrame Q) {m : V} (hm : F.Orth m) (α β : K) :
    polar Q (α • F.b + β • F.b') m = 0 := by
  have h1 : polar Q F.b m = 0 := by rw [polar_comm]; exact hm.1
  have h2 : polar Q F.b' m = 0 := by rw [polar_comm]; exact hm.2
  rw [polar_add_left, polar_smul_left, polar_smul_left, h1, h2]
  simp

end EFrame

section Last

variable [FiniteDimensional K V] (h3 : (3 : K) ≠ 0) (F0 F1 F2 : EFrame Q) (h01 : F0.Perp F1)
  (h02 : F0.Perp F2) (h12 : F1.Perp F2)

@[expose] noncomputable def lastPlane : Submodule K V := F0.orthSub ⊓ F1.orthSub ⊓ F2.orthSub

omit [FiniteDimensional K V] in
theorem mem_lastPlane {v : V} : v ∈ lastPlane F0 F1 F2 ↔ F0.Orth v ∧ F1.Orth v ∧ F2.Orth v := by
  simp only [lastPlane, Submodule.mem_inf, EFrame.mem_orthSub, and_assoc]

omit [FiniteDimensional K V] in
include h3 h01 h02 h12 in
theorem sub_projs_mem_lastPlane (v : V) :
    v - F0.proj v - F1.proj v - F2.proj v ∈ lastPlane F0 F1 F2 := by
  rw [mem_lastPlane]
  refine ⟨?_, ?_, ?_⟩
  · exact ((F0.orth_sub_proj h3 v).sub (F0.orth_proj_of_perp h01 v)).sub
      (F0.orth_proj_of_perp h02 v)
  · have e : v - F0.proj v - F1.proj v - F2.proj v = v - F1.proj v - F0.proj v - F2.proj v := by
      abel
    rw [e]
    exact ((F1.orth_sub_proj h3 v).sub (F1.orth_proj_of_perp h01.symm v)).sub
      (F1.orth_proj_of_perp h12 v)
  · have e : v - F0.proj v - F1.proj v - F2.proj v = v - F2.proj v - F0.proj v - F1.proj v := by
      abel
    rw [e]
    exact ((F2.orth_sub_proj h3 v).sub (F2.orth_proj_of_perp h02.symm v)).sub
      (F2.orth_proj_of_perp h12.symm v)

omit [FiniteDimensional K V] in
theorem exists_hyperbolic_partner {R : Submodule K V} (hR : NDeg Q R) {r : V} (hrR : r ∈ R)
    (hr0 : r ≠ 0) (hQr : Q r = 0) : ∃ r₂ ∈ R, Q r₂ = 0 ∧ polar Q r r₂ = 1 := by
  obtain ⟨r', hr'R, hr'⟩ : ∃ r' ∈ R, polar Q r r' ≠ 0 := by
    by_contra h
    push Not at h
    exact hr0 (hR r hrR h)
  have h1 : polar Q r ((polar Q r r')⁻¹ • r') = 1 := by
    rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hr']
  have hr''R : (polar Q r r')⁻¹ • r' ∈ R := R.smul_mem _ hr'R
  generalize (polar Q r r')⁻¹ • r' = r'' at h1 hr''R
  refine ⟨r'' - Q r'' • r, R.sub_mem hr''R (R.smul_mem _ hrR), ?_, ?_⟩
  · rw [q_sub, q_smul, hQr, polar_smul_right, polar_comm _ r'' r, h1, smul_eq_mul]
    ring
  · rw [polar_sub_right, polar_smul_right, h1, polar_self_eq, hQr, smul_eq_mul]
    ring

omit [FiniteDimensional K V] in
theorem q_sub_three_eq_zero {x y₀ y₁ y₂ : V} (a b c : K) (hx : Q x = 0) (h0 : Q y₀ = 0)
    (h1 : Q y₁ = 0) (h2 : Q y₂ = 0) (hx0 : polar Q x y₀ = 0) (hx1 : polar Q x y₁ = 0)
    (hx2 : polar Q x y₂ = 0) (h01 : polar Q y₀ y₁ = 0) (h02 : polar Q y₀ y₂ = 0)
    (h12 : polar Q y₁ y₂ = 0) : Q (x - a • y₀ - b • y₁ - c • y₂) = 0 := by
  simp only [q_sub, q_smul, polar_sub_left, polar_smul_left, polar_smul_right, hx, h0, h1, h2,
    hx0, hx1, hx2, h01, h02, h12, smul_eq_mul]
  ring

include h3 h01 h02 h12 in
theorem exists_frame_last_split (hB : (polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = 4)
    (hω : ∃ ω : K, ω ^ 2 + ω + 1 = 0) (hR : NDeg Q (lastPlane F0 F1 F2)) :
    ∃ F : EFrame Q, F.b ∈ lastPlane F0 F1 F2 ∧ F.b' ∈ lastPlane F0 F1 F2 := by
  classical
  obtain ⟨ω, hω⟩ := hω
  have hQs : ∀ G : EFrame Q, Q ((-ω) • G.b + (1 : K) • G.b') = 0 := fun G => by
    rw [G.q_comb]
    linear_combination G.c * hω
  have hss : ∀ G : EFrame Q, polar Q ((-ω) • G.b + (1 : K) • G.b')
      ((-ω) • G.b + (1 : K) • G.b') = 0 := fun G => by
    rw [polar_self_eq, hQs, mul_zero]
  set s0 := (-ω) • F0.b + (1 : K) • F0.b'
  set s1 := (-ω) • F1.b + (1 : K) • F1.b'
  set s2 := (-ω) • F2.b + (1 : K) • F2.b'
  have p01 : polar Q s0 s1 = 0 := EFrame.polar_comb_comb_of_perp h01 _ _ _ _
  have p02 : polar Q s0 s2 = 0 := EFrame.polar_comb_comb_of_perp h02 _ _ _ _
  have p12 : polar Q s1 s2 = 0 := EFrame.polar_comb_comb_of_perp h12 _ _ _ _
  set U := Submodule.span K ((({s0, s1, s2} : Finset V)) : Set V)
  have hU : ∀ u ∈ U, Q u = 0 := by
    refine q_eq_zero_of_mem_span ?_ ?_
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> exact hQs _
    · intro x hx y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
        | exact hss _
        | exact p01
        | exact p02
        | exact p12
        | (rw [polar_comm]; exact p01)
        | (rw [polar_comm]; exact p02)
        | (rw [polar_comm]; exact p12)
  have hUdim : finrank K U < finrank K W := by
    have h1 : finrank K U ≤ ({s0, s1, s2} : Finset V).card := finrank_span_finset_le_card _
    have h2 := Finset.card_le_three (a := s0) (b := s1) (c := s2)
    omega
  obtain ⟨w, hwW, hwU, hwnU⟩ :=
    exists_mem_inf_orth_not_mem hB hW (by rw [hWdim, hdim]) hUdim
  have hmemU : ∀ x, x = s0 ∨ x = s1 ∨ x = s2 → x ∈ U := by
    intro x hx
    apply Submodule.subset_span
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hx
  have hws : ∀ x, x = s0 ∨ x = s1 ∨ x = s2 → polar Q w x = 0 := fun x hx => by
    rw [polar_comm]
    exact mem_orth.mp hwU _ (hmemU x hx)
  have hproj : ∀ G : EFrame Q, polar Q w ((-ω) • G.b + (1 : K) • G.b') = 0 →
      G.proj w = ((3 * G.c)⁻¹ * (polar Q w G.b + 2 * polar Q w G.b')) •
        ((-ω) • G.b + (1 : K) • G.b') := by
    intro G hG
    rw [polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul,
      one_mul] at hG
    have hcoef : (3 * G.c)⁻¹ * (2 * polar Q w G.b + polar Q w G.b') =
        (3 * G.c)⁻¹ * (polar Q w G.b + 2 * polar Q w G.b') * -ω := by
      linear_combination (3 * G.c)⁻¹ * ((1 + 2 * ω) * hG + 2 * polar Q w G.b * hω)
    rw [EFrame.proj_apply, hcoef]
    module
  have hp0 := hproj F0 (hws s0 (Or.inl rfl))
  have hp1 := hproj F1 (hws s1 (Or.inr (Or.inl rfl)))
  have hp2 := hproj F2 (hws s2 (Or.inr (Or.inr rfl)))
  set γ0 := (3 * F0.c)⁻¹ * (polar Q w F0.b + 2 * polar Q w F0.b')
  set γ1 := (3 * F1.c)⁻¹ * (polar Q w F1.b + 2 * polar Q w F1.b')
  set γ2 := (3 * F2.c)⁻¹ * (polar Q w F2.b + 2 * polar Q w F2.b')
  have hrR := sub_projs_mem_lastPlane h3 F0 F1 F2 h01 h02 h12 w
  rw [hp0, hp1, hp2] at hrR
  set r := w - γ0 • s0 - γ1 • s1 - γ2 • s2 with hr_def
  have hQr : Q r = 0 :=
    q_sub_three_eq_zero γ0 γ1 γ2 (hW w hwW) (hQs F0) (hQs F1) (hQs F2)
      (hws s0 (Or.inl rfl)) (hws s1 (Or.inr (Or.inl rfl))) (hws s2 (Or.inr (Or.inr rfl)))
      p01 p02 p12
  have hr0 : r ≠ 0 := by
    intro h0
    apply hwnU
    have hw : w = γ0 • s0 + γ1 • s1 + γ2 • s2 := by
      rw [hr_def] at h0
      rw [← sub_eq_zero, ← h0]
      abel
    rw [hw]
    exact U.add_mem (U.add_mem (U.smul_mem _ (hmemU s0 (Or.inl rfl)))
      (U.smul_mem _ (hmemU s1 (Or.inr (Or.inl rfl))))) (U.smul_mem _ (hmemU s2 (Or.inr (Or.inr rfl))))
  obtain ⟨r₂, hr₂R, hQr₂, hrr₂⟩ := exists_hyperbolic_partner hR hrR hr0 hQr
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hrr : polar Q r r = 0 := by rw [polar_self_eq, hQr, mul_zero]
  have hr₂r₂ : polar Q r₂ r₂ = 0 := by rw [polar_self_eq, hQr₂, mul_zero]
  have hr₂r : polar Q r₂ r = 1 := by rw [polar_comm, hrr₂]
  refine ⟨⟨r + r₂, ω • r + (ω ^ 2) • r₂, 1, one_ne_zero, ?_, ?_, ?_⟩,
    (lastPlane F0 F1 F2).add_mem hrR hr₂R,
    (lastPlane F0 F1 F2).add_mem ((lastPlane F0 F1 F2).smul_mem _ hrR)
      ((lastPlane F0 F1 F2).smul_mem _ hr₂R)⟩
  · rw [q_add, hQr, hQr₂, hrr₂]
    ring
  · rw [q_add, q_smul, q_smul, hQr, hQr₂, polar_smul_left, polar_smul_right, hrr₂, smul_eq_mul,
      smul_eq_mul]
    linear_combination hω3
  · simp only [polar_add_left, polar_add_right, polar_smul_right, hrr, hrr₂, hr₂r, hr₂r₂,
      smul_eq_mul]
    linear_combination hω

end Last

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4
