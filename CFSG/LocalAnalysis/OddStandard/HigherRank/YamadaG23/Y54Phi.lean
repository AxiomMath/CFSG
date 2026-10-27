module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Phi
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Nrm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54D

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_conj_t (s : Setting3 G L) (y : G) : y * s.t * y⁻¹ = f3phi s y * s.t := by
  unfold f3phi
  group

theorem y54_phi_mem {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ f4Y s, f3phi s y ∈ s.fr.F := by
  intro y hy
  obtain ⟨v, hv, hvy⟩ := y54_tX_sub hH y hy.1
  unfold f3phi
  rw [hvy, mul_assoc, mul_inv_cancel, mul_one]
  exact hv

theorem y54_phi_mul {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ f4Y s, ∀ y' ∈ f4Y s, f3phi s (y * y') = f3phi s y * f3phi s y' := by
  intro y hy y' hy'
  have hφy := y54_phi_mem hH y hy
  have hφy' := y54_phi_mem hH y' hy'
  have hcomm : y * f3phi s y' * y⁻¹ = f3phi s y' := by
    have hc := Subgroup.mem_centralizer_iff.mp hy.2 (f3phi s y') hφy'
    calc y * f3phi s y' * y⁻¹ = (f3phi s y' * y) * y⁻¹ := by rw [← hc]
      _ = f3phi s y' := by group
  have hab : f3phi s y' * f3phi s y = f3phi s y * f3phi s y' :=
    (y54_F_comm hH (f3phi s y) hφy (f3phi s y') hφy').symm
  calc f3phi s (y * y')
      = y * (y' * s.t * y'⁻¹) * y⁻¹ * s.t⁻¹ := by unfold f3phi; group
    _ = y * (f3phi s y' * s.t) * y⁻¹ * s.t⁻¹ := by rw [y54_conj_t s y']
    _ = (y * f3phi s y' * y⁻¹) * (y * s.t * y⁻¹) * s.t⁻¹ := by group
    _ = (y * f3phi s y' * y⁻¹) * (f3phi s y * s.t) * s.t⁻¹ := by rw [y54_conj_t s y]
    _ = f3phi s y' * f3phi s y := by rw [hcomm]; group
    _ = f3phi s y * f3phi s y' := hab

theorem y54_phi_eq_one {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ f4Y s, (f3phi s y = 1 ↔ y ∈ f4X0 s) := by
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
  exact ⟨fun hh => ⟨hh, hy.2⟩, fun hx => hx.1⟩

theorem y54_phi_conj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ f4N s, ∀ y : G, f3phi s (n * y * n⁻¹) = n * f3phi s y * n⁻¹ := by
  intro n hn y
  have hnt : n * s.t = s.t * n := Subgroup.mem_centralizer_singleton_iff.mp hn.1
  exact f3_phi_conj s hnt y

theorem y54_phi_surj {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    ∀ f ∈ c.s.fr.F, ∃ y ∈ f4Y c.s, f3phi c.s y = f := by
  intro f hf
  by_cases hf1 : f = 1
  · rw [hf1]
    exact ⟨1, Subgroup.one_mem _, by unfold f3phi; group⟩
  · obtain ⟨n, hn, hnz⟩ :=
      y54_trans1 hH c.s.fr.z (y54_z_mem_F c.s) f hf (y54_z_ne_one (c := c) hH) hf1
    have hnN : n ∈ f4N c.s := y54_NL_le_N hH hn
    refine ⟨n * c.d * n⁻¹, y54_N_norm_Y hH n hnN c.d (y54_d_mem_Y hH), ?_⟩
    rw [y54_phi_conj hH n hnN, y54_phi_d hH]
    exact hnz

end CFSG.OddStandard.HigherRank.YamadaG23
