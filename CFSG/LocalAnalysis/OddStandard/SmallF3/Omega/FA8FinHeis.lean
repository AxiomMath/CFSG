module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
  {R : Type} [Group R]

theorem fa8fin_trace_eq_zero (ρ : R →* Module.End (ZMod 3) W) {s g h : R}
    (hs : ρ s = -1) (hh : h * g * h⁻¹ = s * g) :
    LinearMap.trace (ZMod 3) W (ρ g) = 0 := by
  have h1 : LinearMap.trace (ZMod 3) W (ρ g)
      = LinearMap.trace (ZMod 3) W (ρ h * ρ g * ρ (h⁻¹)) := by
    rw [LinearMap.trace_mul_comm (ZMod 3) (ρ h * ρ g) (ρ (h⁻¹))]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have h2 : LinearMap.trace (ZMod 3) W (ρ h * ρ g * ρ (h⁻¹))
      = -LinearMap.trace (ZMod 3) W (ρ g) := by
    have hmul : ρ h * ρ g * ρ (h⁻¹) = ρ (h * g * h⁻¹) := by
      rw [← map_mul, ← map_mul]
    rw [hmul, hh, map_mul, hs]
    simp
  have ht : LinearMap.trace (ZMod 3) W (ρ g)
      = -LinearMap.trace (ZMod 3) W (ρ g) := h1.trans h2
  have h2t : (2 : ZMod 3) * LinearMap.trace (ZMod 3) W (ρ g) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [ht]
    ring
  exact (mul_eq_zero.mp h2t).resolve_left (by decide)

theorem fa8fin_linearIndependent [Finite R] (hW : Module.finrank (ZMod 3) W = 4)
    (ρ : R →* Module.End (ZMod 3) W) (s : R) (hs : s * s = 1) (hρs : ρ s = -1)
    (hpartner : ∀ g : R, g ≠ 1 → g ≠ s → ∃ h : R, h * g * h⁻¹ = s * g) :
    LinearIndependent (ZMod 3) (fun t : R ⧸ Subgroup.zpowers s => ρ (Quotient.out t)) := by
  classical
  haveI : Fintype (R ⧸ Subgroup.zpowers s) := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hnotmem : ∀ i : R ⧸ Subgroup.zpowers s, i ≠ j →
      (Quotient.out j)⁻¹ * Quotient.out i ∉ Subgroup.zpowers s := by
    intro i hij hmem
    have hq : QuotientGroup.mk (Quotient.out j) = QuotientGroup.mk (Quotient.out i) :=
      QuotientGroup.eq.mpr hmem
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at hq
    exact hij hq.symm
  have htrace : ∀ i : R ⧸ Subgroup.zpowers s,
      LinearMap.trace (ZMod 3) W (ρ ((Quotient.out j)⁻¹ * Quotient.out i)) =
        if i = j then 1 else 0 := by
    intro i
    by_cases hij : i = j
    · rw [hij, if_pos rfl, inv_mul_cancel, map_one, LinearMap.trace_one, hW]
      decide
    · rw [if_neg hij]
      have hg1 : (Quotient.out j)⁻¹ * Quotient.out i ≠ 1 := by
        intro h
        have h1 : (1 : R) ∈ Subgroup.zpowers s := Subgroup.one_mem _
        exact hnotmem i hij (by simpa [h] using h1)
      have hgs : (Quotient.out j)⁻¹ * Quotient.out i ≠ s := by
        intro h
        have hs' : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
        exact hnotmem i hij (by simpa [h] using hs')
      obtain ⟨h, hh⟩ := hpartner _ hg1 hgs
      exact fa8fin_trace_eq_zero ρ hρs hh
  have hsum : ∑ i, c i * (if i = j then (1 : ZMod 3) else 0) = 0 := by
    have hzero : LinearMap.trace (ZMod 3) W
        (ρ ((Quotient.out j)⁻¹) * (∑ i, c i • ρ (Quotient.out i))) = 0 := by
      rw [hc, mul_zero, map_zero]
    calc
      ∑ i, c i * (if i = j then (1 : ZMod 3) else 0)
          = ∑ i, c i * LinearMap.trace (ZMod 3) W
              (ρ ((Quotient.out j)⁻¹ * Quotient.out i)) := by
            exact Finset.sum_congr rfl fun i _ => by rw [htrace i]
      _ = ∑ i, LinearMap.trace (ZMod 3) W
              (ρ ((Quotient.out j)⁻¹) * (c i • ρ (Quotient.out i))) := by
            exact Finset.sum_congr rfl fun i _ => by
              rw [mul_smul_comm, map_smul, ← map_mul, smul_eq_mul]
      _ = LinearMap.trace (ZMod 3) W
              (ρ ((Quotient.out j)⁻¹) * (∑ i, c i • ρ (Quotient.out i))) := by
            rw [Finset.mul_sum, map_sum]
      _ = 0 := hzero
  simpa using hsum

theorem fa8fin_span_top [Finite R] (hW : Module.finrank (ZMod 3) W = 4) (hcard : Nat.card R = 32)
    (ρ : R →* Module.End (ZMod 3) W) (s : R) (hs : s * s = 1) (hs1 : s ≠ 1) (hρs : ρ s = -1)
    (hpartner : ∀ g : R, g ≠ 1 → g ≠ s → ∃ h : R, h * g * h⁻¹ = s * g) :
    Submodule.span (ZMod 3) (Set.range (fun g : R => ρ g)) = ⊤ := by
  classical
  haveI : Fintype (R ⧸ Subgroup.zpowers s) := Fintype.ofFinite _
  have hpow : s ^ 2 = 1 := by
    rw [pow_two]
    exact hs
  have hz : Nat.card (Subgroup.zpowers s) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hpow hs1
  have hidx : (Subgroup.zpowers s).index = 16 := by
    have h := Subgroup.index_mul_card (Subgroup.zpowers s)
    rw [hz, hcard] at h
    omega
  have hcardT : Nat.card (R ⧸ Subgroup.zpowers s) = 16 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hcardFT : Fintype.card (R ⧸ Subgroup.zpowers s) = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardT
  have hfin : Module.finrank (ZMod 3) (Module.End (ZMod 3) W) = 16 := by
    rw [Module.finrank_linearMap, hW]
  have hLI := fa8fin_linearIndependent hW ρ s hs hρs hpartner
  have hspan := hLI.span_eq_top_of_card_eq_finrank' (by rw [hcardFT, hfin])
  have hle : Submodule.span (ZMod 3) (Set.range fun t : R ⧸ Subgroup.zpowers s =>
      ρ (Quotient.out t)) ≤
      Submodule.span (ZMod 3) (Set.range fun g : R => ρ g) := by
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨Quotient.out t, rfl⟩
  rw [hspan] at hle
  exact top_le_iff.mp hle

theorem fa8fin_commutant_scalar [Finite R] (hW : Module.finrank (ZMod 3) W = 4)
    (hcard : Nat.card R = 32) (ρ : R →* Module.End (ZMod 3) W) (s : R) (hs : s * s = 1)
    (hs1 : s ≠ 1) (hρs : ρ s = -1)
    (hpartner : ∀ g : R, g ≠ 1 → g ≠ s → ∃ h : R, h * g * h⁻¹ = s * g)
    (f : Module.End (ZMod 3) W) (hf : ∀ g : R, f * ρ g = ρ g * f) :
    ∃ c : ZMod 3, f = c • (1 : Module.End (ZMod 3) W) := by
  classical
  have hspan := fa8fin_span_top hW hcard ρ s hs hs1 hρs hpartner
  have hcomm : ∀ A : Module.End (ZMod 3) W, A * f = f * A := by
    intro A
    have hA : A ∈ Submodule.span (ZMod 3) (Set.range fun g : R => ρ g) := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun x _ => x * f = f * x) ?_ ?_ ?_ ?_ hA
    · rintro _ ⟨g, rfl⟩
      exact (hf g).symm
    · simp
    · intro x y _ _ hpx hpy
      rw [add_mul, mul_add, hpx, hpy]
    · intro a x _ hpx
      rw [smul_mul_assoc, mul_smul_comm, hpx]
  have hcenter : f ∈ Set.center (Module.End (ZMod 3) W) := by
    rw [Semigroup.mem_center_iff]
    exact hcomm
  obtain ⟨α, hα, hfα⟩ := Module.End.mem_center_iff.mp hcenter
  exact ⟨α, by rw [hfα, Module.End.smulLeft_eq, ← Module.End.one_eq_id]⟩

end CFSG.OddStandard.SmallF3.Omega
