module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma f3_conj_eq (s : Setting3 G L) (y : G) :
    y * s.t * y⁻¹ = f3phi s y * s.t := by
  unfold f3phi
  group

theorem f3_phi_mem {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ f3Y s, f3phi s y ∈ cen s.fr.B := by
  intro y hy
  obtain ⟨v, hv, hvy⟩ := f3_tX_sub hH y hy.1
  unfold f3phi
  rw [hvy, mul_assoc, mul_inv_cancel, mul_one]
  exact hv

theorem f3_phi_mul {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ f3Y s, ∀ y' ∈ f3Y s, f3phi s (y * y') = f3phi s y * f3phi s y' := by
  intro y hy y' hy'
  have hφy := f3_phi_mem hH y hy
  have hφy' := f3_phi_mem hH y' hy'
  have hcomm : y * f3phi s y' * y⁻¹ = f3phi s y' := by
    have hc := Subgroup.mem_centralizer_iff.mp hy.2 (f3phi s y') hφy'
    calc y * f3phi s y' * y⁻¹ = (f3phi s y' * y) * y⁻¹ := by rw [← hc]
      _ = f3phi s y' := by group
  have hab : f3phi s y' * f3phi s y = f3phi s y * f3phi s y' :=
    Subgroup.mem_centralizer_iff.mp hφy.2 (f3phi s y') hφy'.1
  calc f3phi s (y * y')
      = y * (y' * s.t * y'⁻¹) * y⁻¹ * s.t⁻¹ := by unfold f3phi; group
    _ = y * (f3phi s y' * s.t) * y⁻¹ * s.t⁻¹ := by rw [f3_conj_eq s y']
    _ = (y * f3phi s y' * y⁻¹) * (y * s.t * y⁻¹) * s.t⁻¹ := by group
    _ = (y * f3phi s y' * y⁻¹) * (f3phi s y * s.t) * s.t⁻¹ := by rw [f3_conj_eq s y]
    _ = f3phi s y' * f3phi s y := by rw [hcomm]; group
    _ = f3phi s y * f3phi s y' := hab

theorem f3_phi_eq_one {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ f3Y s, (f3phi s y = 1 ↔ y ∈ f3X0 s) := by
  intro y hy
  have h1 : f3phi s y = 1 ↔ y * s.t * y⁻¹ = s.t := by
    constructor
    · intro h
      have := congrArg (· * s.t) h
      simpa [f3phi, mul_assoc] using this
    · intro h; simp [f3phi, h]
  have h2 : y * s.t * y⁻¹ = s.t ↔ y * s.t = s.t * y := by
    constructor
    · intro h
      have := congrArg (· * y) h
      simpa [mul_assoc] using this
    · intro h; rw [h]; group
  have hHiff : y * s.t = s.t * y ↔ y ∈ s.H := by
    show y * s.t = s.t * y ↔ y ∈ centralizer ({s.t} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.symm
  rw [h1, h2, hHiff]
  constructor
  · intro hh
    rw [← f3_Y_inf_H hH]
    exact ⟨hy, hh⟩
  · intro hx
    rw [← f3_Y_inf_H hH] at hx
    exact hx.2

theorem f3_phi_surj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ v ∈ cen s.fr.B, ∃ y ∈ f3Y s, f3phi s y = v := by
  intro v hv
  obtain ⟨y, hy, hyv⟩ := f3_Y_orbit hH v hv
  refine ⟨y, hy, ?_⟩
  rw [f3_conj_eq s y] at hyv
  exact mul_right_cancel hyv

theorem f3_phi_conj (s : Setting3 G L) {n : G} (hn : n * s.t = s.t * n) (y : G) :
    f3phi s (n * y * n⁻¹) = n * f3phi s y * n⁻¹ := by
  have hn' : n * s.t * n⁻¹ = s.t := by rw [hn]; group
  have hn'' : n⁻¹ * s.t * n = s.t := by
    have h := congrArg (fun z => n⁻¹ * z * n) hn'
    simpa [mul_assoc] using h.symm
  have hninv : n⁻¹ * s.t⁻¹ = s.t⁻¹ * n⁻¹ := by
    have h := congrArg Inv.inv hn
    simpa [mul_inv_rev] using h.symm
  unfold f3phi
  calc n * y * n⁻¹ * s.t * (n * y * n⁻¹)⁻¹ * s.t⁻¹
      = n * y * (n⁻¹ * s.t * n) * y⁻¹ * n⁻¹ * s.t⁻¹ := by group
    _ = n * y * s.t * y⁻¹ * n⁻¹ * s.t⁻¹ := by rw [hn'']
    _ = n * y * s.t * y⁻¹ * s.t⁻¹ * n⁻¹ := by
        simp only [mul_assoc]
        rw [hninv]
    _ = n * (y * s.t * y⁻¹ * s.t⁻¹) * n⁻¹ := by group

end CFSG.OddStandard.HigherRank.YamadaG23
