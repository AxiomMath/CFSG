module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Mb

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y56_X_eq_YN (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ e4X c.s, ∃ y ∈ e4Y c.s, ∃ n ∈ e4N c.s, x = y * n := by
  intro x hx
  obtain ⟨v, hvE, hxconj⟩ := y56_tX_sub hH x hx
  obtain ⟨y, hyY, hyphi⟩ := y56_phi_surj c hH v hvE
  have hyX : y ∈ e4X c.s := hyY.1
  have hy' : y * c.s.t * y⁻¹ = v * c.s.t := by rw [y56_conj_t c.s y, hyphi]
  have hn : (y⁻¹ * x) * c.s.t * (y⁻¹ * x)⁻¹ = c.s.t := by
    calc
      (y⁻¹ * x) * c.s.t * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * c.s.t * x⁻¹) * y := by group
      _ = y⁻¹ * (v * c.s.t) * y := by rw [hxconj]
      _ = y⁻¹ * (y * c.s.t * y⁻¹) * y := by rw [hy']
      _ = c.s.t := by group
  have hnH : y⁻¹ * x ∈ c.s.H := by
    change y⁻¹ * x ∈ centralizer ({c.s.t} : Set G)
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact ((mul_inv_eq_iff_eq_mul).mp hn).symm
  refine ⟨y, hyY, y⁻¹ * x, ?_, by group⟩
  rw [← y56_X_inf_H hH]
  have hyinv : y⁻¹ ∈ e4X c.s := inv_mem hyX
  exact ⟨mul_mem hyinv hx, hnH⟩

theorem y56_normalizer_Q (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normalizer ((c.s.fr.E ⊔ zpowers c.s.t : Subgroup G) : Set G) =
      normIn c.s.H c.s.fr.E ⊔ C4 c.s := by
  change e4X c.s = e4N c.s ⊔ C4 c.s
  have hM := y56_C4_cand c hH
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hyY, n, hnN, rfl⟩ := y56_X_eq_YN c hH x hx
    obtain ⟨m, hmM, x₀, hx₀X0, rfl⟩ := y56_Y_decomp hH hM y hyY
    have hx₀N : x₀ ∈ e4N c.s :=
      ⟨hx₀X0.1, Subgroup.centralizer_le_normalizer (c.s.fr.E : Set G) hx₀X0.2⟩
    have hmem : m * (x₀ * n) ∈ C4 c.s ⊔ e4N c.s :=
      Subgroup.mul_mem_sup hmM (mul_mem hx₀N hnN)
    simpa [mul_assoc, sup_comm] using hmem
  · exact sup_le (y56_N_le_X hH) (hM.2.1.trans inf_le_left)

theorem y56_H_inf_C4 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.H ⊓ C4 c.s = c.s.fr.E ⊔ zpowers c.s.t := by
  have hM := y56_C4_cand c hH
  apply le_antisymm
  · intro m hm
    obtain ⟨hmH, hmM⟩ := hm
    have hmC : m ∈ centralizer (c.s.fr.E : Set G) := (hM.2.1 hmM).2
    have hmX0 : m ∈ e4X0 c.s := ⟨hmH, hmC⟩
    change m ∈ e4Q c.s
    rw [← hM.2.2.2.1]
    exact ⟨hmM, hmX0⟩
  · intro q hq
    exact ⟨(y56_Q_le_X0 hH hq).1, hM.1 hq⟩

theorem y56_conjClass_C4 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    conjClass (C4 c.s) c.s.t = c.s.tCoset c.s.fr.E := by
  have hM := y56_C4_cand c hH
  ext w
  simp only [conjClass, Setting3.tCoset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, hmM, rfl⟩
    exact ⟨f3phi c.s m, y56_phi_mem hH m (hM.2.1 hmM), y56_conj_t c.s m⟩
  · rintro ⟨f, hfF, rfl⟩
    obtain ⟨m, hmM, hphi⟩ := y56_phi_M hH hM f hfF
    exact ⟨m, hmM, by rw [y56_conj_t c.s m, hphi]⟩

end CFSG.OddStandard.HigherRank.YamadaG23
