module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Second

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2

variable {S : Subgroup GL12} {g : GL12}

theorem conj_mem_iff (hg : g ∈ normalizer (S : Set GL12)) (c : GL12) :
    g * c * g⁻¹ ∈ S ↔ c ∈ S := (mem_normalizer_iff.1 hg c).symm

theorem conj_commute_iff (g c s : GL12) :
    g * c * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * c * g⁻¹) ↔ c * s = s * c := by
  constructor
  · intro e
    have e' : g * (c * s) * g⁻¹ = g * (s * c) * g⁻¹ := by
      calc g * (c * s) * g⁻¹ = g * c * g⁻¹ * (g * s * g⁻¹) := by group
        _ = g * s * g⁻¹ * (g * c * g⁻¹) := e
        _ = g * (s * c) * g⁻¹ := by group
    simpa using e'
  · intro e
    calc g * c * g⁻¹ * (g * s * g⁻¹) = g * (c * s) * g⁻¹ := by group
      _ = g * (s * c) * g⁻¹ := by rw [e]
      _ = g * s * g⁻¹ * (g * c * g⁻¹) := by group

theorem conj_mulVec_iff (g c : GL12) (v : Vec12) :
    ((g * c * g⁻¹ : GL12) : Mat12) *ᵥ ((g : Mat12) *ᵥ v) = (g : Mat12) *ᵥ v ↔
      (c : Mat12) *ᵥ v = v := by
  rw [mulVec_units, show g * c * g⁻¹ * g = g * c by group, ← mulVec_units]
  constructor
  · intro e
    have e' := congrArg (fun w => ((g⁻¹ : GL12) : Mat12) *ᵥ w) e
    simpa [mulVec_units] using e'
  · intro e
    rw [e]

theorem card_inf_centralizer_conj (hg : g ∈ normalizer (S : Set GL12)) (s : GL12) :
    Nat.card ↥(S ⊓ centralizer ({g * s * g⁻¹} : Set GL12)) =
      Nat.card ↥(S ⊓ centralizer ({s} : Set GL12)) := by
  refine (Nat.card_congr
    { toFun := fun c => ⟨g⁻¹ * c.1 * g, ?_⟩
      invFun := fun c => ⟨g * c.1 * g⁻¹, ?_⟩
      left_inv := fun c => ?_
      right_inv := fun c => ?_ })
  · obtain ⟨hcS, hcs⟩ := c.2
    have e : c.1 = g * (g⁻¹ * c.1 * g) * g⁻¹ := by group
    rw [e] at hcS hcs
    refine ⟨(conj_mem_iff hg _).1 hcS, mem_centralizer_singleton_iff.2 ?_⟩
    exact (conj_commute_iff g _ s).1 (mem_centralizer_singleton_iff.1 hcs)
  · obtain ⟨hcS, hcs⟩ := c.2
    exact ⟨(conj_mem_iff hg _).2 hcS, mem_centralizer_singleton_iff.2
      ((conj_commute_iff g _ s).2 (mem_centralizer_singleton_iff.1 hcs))⟩
  · ext1; simp only; group
  · ext1; simp only; group

theorem card_kerSet_conj (hg : g ∈ normalizer (S : Set GL12)) (s : GL12) :
    Nat.card (kerSet S (g * s * g⁻¹)) = Nat.card (kerSet S s) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨g⁻¹ * c.1 * g, ?_⟩
      invFun := fun c => ⟨g * c.1 * g⁻¹, ?_⟩
      left_inv := fun c => ?_
      right_inv := fun c => ?_ }
  · obtain ⟨hcS, hcs, hfix⟩ := c.2
    have e : c.1 = g * (g⁻¹ * c.1 * g) * g⁻¹ := by group
    rw [e] at hcS hcs hfix
    refine ⟨(conj_mem_iff hg _).1 hcS, (conj_commute_iff g _ s).1 hcs, fun v hv => ?_⟩
    have := hfix ((g : Mat12) *ᵥ v) ((conj_mulVec_iff g s v).2 hv)
    exact (conj_mulVec_iff g _ v).1 this
  · obtain ⟨hcS, hcs, hfix⟩ := c.2
    refine ⟨(conj_mem_iff hg _).2 hcS, (conj_commute_iff g _ s).2 hcs, fun v hv => ?_⟩
    set w := ((g⁻¹ : GL12) : Mat12) *ᵥ v with hw
    have hvw : v = (g : Mat12) *ᵥ w := by rw [hw, mulVec_units, mul_inv_cancel, units_one_mulVec]
    rw [hvw] at hv ⊢
    exact (conj_mulVec_iff g _ w).2 (hfix w ((conj_mulVec_iff g s w).1 hv))
  · ext1; simp only; group
  · ext1; simp only; group

theorem card_burnSet_conj (hg : g ∈ normalizer (S : Set GL12)) (s : GL12) :
    Nat.card (burnSet S (g * s * g⁻¹)) = Nat.card (burnSet S s) := by
  refine Nat.card_congr
    { toFun := fun p => ⟨(g⁻¹ * p.1.1 * g, ((g⁻¹ : GL12) : Mat12) *ᵥ p.1.2), ?_⟩
      invFun := fun p => ⟨(g * p.1.1 * g⁻¹, (g : Mat12) *ᵥ p.1.2), ?_⟩
      left_inv := fun p => ?_
      right_inv := fun p => ?_ }
  · obtain ⟨hcS, hcs, hv, hcv⟩ := p.2
    set c := p.1.1
    set v := p.1.2
    set w := ((g⁻¹ : GL12) : Mat12) *ᵥ v with hw
    have hvw : v = (g : Mat12) *ᵥ w := by rw [hw, mulVec_units, mul_inv_cancel, units_one_mulVec]
    have e : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [e] at hcS hcs hcv
    rw [hvw] at hv hcv
    exact ⟨(conj_mem_iff hg _).1 hcS, (conj_commute_iff g _ s).1 hcs,
      (conj_mulVec_iff g s w).1 hv, (conj_mulVec_iff g _ w).1 hcv⟩
  · obtain ⟨hcS, hcs, hv, hcv⟩ := p.2
    exact ⟨(conj_mem_iff hg _).2 hcS, (conj_commute_iff g _ s).2 hcs,
      (conj_mulVec_iff g s _).2 hv, (conj_mulVec_iff g _ _).2 hcv⟩
  · ext1
    refine Prod.ext ?_ ?_
    · simp only; group
    · simp only [mulVec_units, mul_inv_cancel, units_one_mulVec]
  · ext1
    refine Prod.ext ?_ ?_
    · simp only; group
    · simp only [mulVec_units, inv_mul_cancel, units_one_mulVec]

theorem card_zfixSet_conj (hg : g ∈ normalizer (S : Set GL12)) (s : GL12) :
    Nat.card (zfixSet S (g * s * g⁻¹)) = Nat.card (zfixSet S s) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨((g⁻¹ : GL12) : Mat12) *ᵥ v.1, ?_⟩
      invFun := fun v => ⟨(g : Mat12) *ᵥ v.1, ?_⟩
      left_inv := fun v => ?_
      right_inv := fun v => ?_ }
  · obtain ⟨hv, hfix⟩ := v.2
    set w := ((g⁻¹ : GL12) : Mat12) *ᵥ v.1 with hw
    have hvw : v.1 = (g : Mat12) *ᵥ w := by
      rw [hw, mulVec_units, mul_inv_cancel, units_one_mulVec]
    rw [hvw] at hv hfix
    refine ⟨(conj_mulVec_iff g s w).1 hv, fun c hc hcs => ?_⟩
    have h1 := hfix (g * c * g⁻¹) ((conj_mem_iff hg c).2 hc) ((conj_commute_iff g c s).2 hcs)
    exact (conj_mulVec_iff g c w).1 h1
  · obtain ⟨hv, hfix⟩ := v.2
    refine ⟨(conj_mulVec_iff g s _).2 hv, fun c hc hcs => ?_⟩
    have hc' : g⁻¹ * c * g ∈ S := by
      have := (conj_mem_iff hg (g⁻¹ * c * g)).2
      rw [show g * (g⁻¹ * c * g) * g⁻¹ = c by group] at this
      exact (conj_mem_iff hg _).1 (by rw [show g * (g⁻¹ * c * g) * g⁻¹ = c by group]; exact hc)
    have hcs' : g⁻¹ * c * g * s = s * (g⁻¹ * c * g) := by
      have := (conj_commute_iff g (g⁻¹ * c * g) s).1
      rw [show g * (g⁻¹ * c * g) * g⁻¹ = c by group] at this
      exact this hcs
    have h1 := hfix _ hc' hcs'
    have h2 := (conj_mulVec_iff g (g⁻¹ * c * g) v.1).2 h1
    rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group] at h2
  · ext1
    show (g : Mat12) *ᵥ (((g⁻¹ : GL12) : Mat12) *ᵥ v.1) = v.1
    rw [mulVec_units, mul_inv_cancel, units_one_mulVec]
  · ext1
    show ((g⁻¹ : GL12) : Mat12) *ᵥ ((g : Mat12) *ᵥ v.1) = v.1
    rw [mulVec_units, inv_mul_cancel, units_one_mulVec]

theorem isCand_conj (hg : g ∈ normalizer (S : Set GL12)) {s : GL12} :
    IsCand S (g * s * g⁻¹) ↔ IsCand S s := by
  have hsq : g * s * g⁻¹ * (g * s * g⁻¹) = 1 ↔ s * s = 1 := by
    rw [show g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group]
    constructor
    · intro e
      have : s * s = g⁻¹ * (g * (s * s) * g⁻¹) * g := by group
      rw [this, e]
      group
    · intro e
      rw [e]
      group
  have hne : g * s * g⁻¹ ≠ 1 ↔ s ≠ 1 := by
    constructor
    · intro h e
      exact h (by rw [e]; group)
    · intro h e
      apply h
      have : s = g⁻¹ * (g * s * g⁻¹) * g := by group
      rw [this, e]
      group
  simp only [IsCand]
  rw [hsq, hne, card_fixM_conj, card_inf_centralizer_conj hg, card_zfixSet_conj hg]

end CFSG.EvenSmallLie.OmegaEight.N3Split
