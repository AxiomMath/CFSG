module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54M3b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_X_eq_YN (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ f4X c.s, ∃ y ∈ f4Y c.s, ∃ n ∈ f4N c.s, x = y * n := by
  intro x hx
  obtain ⟨v, hvF, hxconj⟩ := y54_tX_sub hH x hx
  obtain ⟨y, hyY, hyphi⟩ := y54_phi_surj hH v hvF
  have hyX : y ∈ f4X c.s := hyY.1
  have hy' : y * c.s.t * y⁻¹ = v * c.s.t := by rw [y54_conj_t c.s y, hyphi]
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
  rw [← y54_X_inf_H hH]
  have hyinv : y⁻¹ ∈ f4X c.s := inv_mem hyX
  exact ⟨mul_mem hyinv hx, hnH⟩

theorem y54_normalizer_P (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normalizer ((c.s.fr.F ⊔ zpowers c.s.t : Subgroup G) : Set G) =
      normIn c.s.H c.s.fr.F ⊔ M3 c.s := by
  change f4X c.s = f4N c.s ⊔ M3 c.s
  have hM := y54_M3_cand c hH
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hyY, n, hnN, rfl⟩ := y54_X_eq_YN c hH x hx
    obtain ⟨m, hmM, x₀, hx₀X0, rfl⟩ := y54_Y_decomp hH hM y hyY
    have hx₀N : x₀ ∈ f4N c.s :=
      ⟨hx₀X0.1, Subgroup.centralizer_le_normalizer (c.s.fr.F : Set G) hx₀X0.2⟩
    have hmem : m * (x₀ * n) ∈ M3 c.s ⊔ f4N c.s :=
      Subgroup.mul_mem_sup hmM (mul_mem hx₀N hnN)
    simpa [mul_assoc, sup_comm] using hmem
  · exact sup_le (y54_N_le_X hH) (hM.2.1.trans inf_le_left)

theorem y54_H_inf_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.s.H ⊓ M3 c.s = c.s.fr.F := by
  have hM := y54_M3_cand c hH
  apply le_antisymm
  · intro m hm
    obtain ⟨hmH, hmM⟩ := hm
    have hmC : m ∈ centralizer (c.s.fr.F : Set G) := (hM.2.1 hmM).2
    have hmX0 : m ∈ f4X0 c.s := ⟨hmH, hmC⟩
    rw [← hM.2.2.2.1]
    exact ⟨hmM, hmX0⟩
  · intro f hf
    exact ⟨(y54_F_le_L c.s).trans (s3_L_le_H c.s hH.hS) hf, hM.1 hf⟩

theorem y54_conjClass_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    conjClass (M3 c.s) c.s.t = c.s.tCoset c.s.fr.F := by
  have hM := y54_M3_cand c hH
  ext w
  simp only [conjClass, Setting3.tCoset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, hmM, rfl⟩
    exact ⟨f3phi c.s m, y54_phi_mem hH m (hM.2.1 hmM), y54_conj_t c.s m⟩
  · rintro ⟨f, hfF, rfl⟩
    obtain ⟨m, hmM, hphi⟩ := y54_phi_M hH hM f hfF
    exact ⟨m, hmM, by rw [y54_conj_t c.s m, hphi]⟩

end CFSG.OddStandard.HigherRank.YamadaG23
