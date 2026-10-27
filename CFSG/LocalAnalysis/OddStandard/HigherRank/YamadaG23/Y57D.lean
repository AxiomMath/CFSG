module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57B

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma f3phi_inv {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {y : G}
    (hy : y ∈ f4Y c.s) : f3phi c.s y⁻¹ = (f3phi c.s y)⁻¹ := by
  have hmul := y54_phi_mul hH y hy y⁻¹ ((f4Y c.s).inv_mem hy)
  have h1 : f3phi c.s (1 : G) = f3phi c.s y * f3phi c.s y⁻¹ := by simpa using hmul
  have h0 : f3phi c.s (1 : G) = 1 := by simp [f3phi]
  rw [h0] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem y57_caseA (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hd : c.d ∈ M3 c.s) :
    IsElemAbelian 2 (M3 c.s) := by
  have hM : IsM3Cand c.s (M3 c.s) := y54_M3_cand c hH
  have hcommM : ∀ m ∈ M3 c.s, ∀ m' ∈ M3 c.s, m * m' = m' * m := y57_M3_comm c hH
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    exact Subtype.ext (hcommM (a : G) a.2 (b : G) b.2)
  · intro m hm
    have hmY : m ∈ f4Y c.s := hM.2.1 hm
    have hφmF : f3phi c.s m ∈ c.s.fr.F := y54_phi_mem hH m hmY
    rcases eq_or_ne (f3phi c.s m) 1 with hφ1 | hφ1
    · exact y54_F_sq hH m (y54_M_inf_ker hH hM m hm hφ1)
    · obtain ⟨n, hnNL, hnz⟩ :=
        y54_trans1 hH c.s.fr.z (y54_z_mem_F c.s) (f3phi c.s m) hφmF
          (y54_z_ne_one (c := c) hH) hφ1
      have hnN : n ∈ f4N c.s := y54_NL_le_N hH hnNL
      have hndM : n * c.d * n⁻¹ ∈ M3 c.s := hM.2.2.1 n hnNL c.d hd
      have hndY : n * c.d * n⁻¹ ∈ f4Y c.s := hM.2.1 hndM
      have hφnd : f3phi c.s (n * c.d * n⁻¹) = f3phi c.s m := by
        rw [y54_phi_conj hH n hnN c.d, y54_phi_d hH, hnz]
      have hxM : (n * c.d * n⁻¹)⁻¹ * m ∈ M3 c.s :=
        (M3 c.s).mul_mem ((M3 c.s).inv_mem hndM) hm
      have hxY : (n * c.d * n⁻¹)⁻¹ * m ∈ f4Y c.s := hM.2.1 hxM
      have hφx : f3phi c.s ((n * c.d * n⁻¹)⁻¹ * m) = 1 := by
        rw [y54_phi_mul hH ((n * c.d * n⁻¹)⁻¹) ((f4Y c.s).inv_mem hndY) m hmY,
          f3phi_inv hH hndY, hφnd, inv_mul_cancel]
      have hxF : (n * c.d * n⁻¹)⁻¹ * m ∈ c.s.fr.F :=
        y54_M_inf_ker hH hM _ hxM hφx
      have hx2 : ((n * c.d * n⁻¹)⁻¹ * m) ^ 2 = 1 := y54_F_sq hH _ hxF
      have hm'2 : (n * c.d * n⁻¹) ^ 2 = 1 := by
        have h : (n * c.d * n⁻¹) ^ 2 = n * c.d ^ 2 * n⁻¹ := by
          rw [pow_two, pow_two]
          group
        rw [h, y5_d_sq c]
        group
      have hm_eq : m = (n * c.d * n⁻¹) * ((n * c.d * n⁻¹)⁻¹ * m) := by group
      have hXY : ((n * c.d * n⁻¹) * ((n * c.d * n⁻¹)⁻¹ * m)) *
            ((n * c.d * n⁻¹) * ((n * c.d * n⁻¹)⁻¹ * m)) = 1 := by
        calc ((n * c.d * n⁻¹) * ((n * c.d * n⁻¹)⁻¹ * m)) *
              ((n * c.d * n⁻¹) * ((n * c.d * n⁻¹)⁻¹ * m))
            = (n * c.d * n⁻¹) *
                (((n * c.d * n⁻¹)⁻¹ * m) * (n * c.d * n⁻¹)) *
                ((n * c.d * n⁻¹)⁻¹ * m) := by group
          _ = (n * c.d * n⁻¹) *
                ((n * c.d * n⁻¹) * ((n * c.d * n⁻¹)⁻¹ * m)) *
                ((n * c.d * n⁻¹)⁻¹ * m) := by rw [hcommM _ hxM _ hndM]
          _ = ((n * c.d * n⁻¹) * (n * c.d * n⁻¹)) *
                (((n * c.d * n⁻¹)⁻¹ * m) * ((n * c.d * n⁻¹)⁻¹ * m)) := by group
          _ = 1 := by rw [← pow_two, ← pow_two, hm'2, hx2, mul_one]
      rw [hm_eq]
      simpa [pow_two] using hXY

end CFSG.OddStandard.HigherRank.YamadaG23
