module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54M3b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y57E_phi_inv {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {y : G}
    (hy : y ∈ f4Y s) : f3phi s y⁻¹ = (f3phi s y)⁻¹ := by
  have hmul := y54_phi_mul hH y hy y⁻¹ ((f4Y s).inv_mem hy)
  have hone : f3phi s (1 : G) = 1 := by simp [f3phi]
  have h : f3phi s y * f3phi s y⁻¹ = 1 := by
    rw [← hmul, mul_inv_cancel, hone]
  exact eq_inv_of_mul_eq_one_right h

theorem y57_caseB_inv (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (htd : c.s.t * c.d ∈ M3 c.s) :
    ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ = m⁻¹ := by
  intro m hm
  have ht2 : c.s.t * c.s.t = 1 := by
    have h := pow_orderOf_eq_one c.s.t
    rw [c.s.t_order] at h
    simpa [pow_two] using h
  have hd2 : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c
  have ht_inv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
  have hd_inv : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right hd2
  have hmY : m ∈ f4Y c.s := (y54_M3_cand c hH).2.1 hm
  have hfF : f3phi c.s m ∈ c.s.fr.F := y54_phi_mem hH m hmY
  by_cases hf1 : f3phi c.s m = 1
  · have hmF : m ∈ c.s.fr.F :=
      y54_M_inf_ker (c := c) hH (y54_M3_cand c hH) m hm hf1
    have hm2 : m * m = 1 := by
      have h := y54_F_sq hH m hmF
      rwa [pow_two] at h
    have hcomm : c.s.t * m = m * c.s.t := (y54_t_comm_F c.s m hmF).symm
    calc c.s.t * m * c.s.t⁻¹ = m := by rw [hcomm]; group
      _ = m⁻¹ := by rw [inv_eq_of_mul_eq_one_right hm2]
  · have htY : c.s.t ∈ f4Y c.s :=
      y54_X0_le_Y hH (y54_P_le_X0 hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)))
    have htphi : f3phi c.s c.s.t = 1 := by unfold f3phi; group
    have hphi_g : f3phi c.s (c.s.t * c.d) = c.s.fr.z := by
      rw [y54_phi_mul hH c.s.t htY c.d (y54_d_mem_Y (c := c) hH),
        y54_phi_d (c := c) hH, htphi, one_mul]
    obtain ⟨n, hnN, hnz⟩ :=
      y54_trans1 hH c.s.fr.z (y54_z_mem_F c.s) (f3phi c.s m) hfF (y54_z_ne_one hH) hf1
    have hnL : n ∈ L := (Subgroup.mem_inf.mp hnN).1
    set m' : G := n * (c.s.t * c.d) * n⁻¹ with hm'def
    have hm'M : m' ∈ M3 c.s := by
      rw [hm'def]
      exact (y54_M3_cand c hH).2.2.1 n hnN (c.s.t * c.d) htd
    have hm'Y : m' ∈ f4Y c.s := (y54_M3_cand c hH).2.1 hm'M
    have hm'phi : f3phi c.s m' = f3phi c.s m := by
      rw [hm'def, y54_phi_conj hH n (y54_NL_le_N hH hnN) (c.s.t * c.d), hphi_g, hnz]
    set x : G := m'⁻¹ * m with hxdef
    have hxM : x ∈ M3 c.s := by
      rw [hxdef]; exact (M3 c.s).mul_mem ((M3 c.s).inv_mem hm'M) hm
    have hxphi : f3phi c.s x = 1 := by
      rw [hxdef, y54_phi_mul hH m'⁻¹ ((f4Y c.s).inv_mem hm'Y) m hmY,
        y57E_phi_inv hH hm'Y, hm'phi]
      group
    have hxF : x ∈ c.s.fr.F :=
      y54_M_inf_ker (c := c) hH (y54_M3_cand c hH) x hxM hxphi
    have hx2 : x * x = 1 := by
      have h := y54_F_sq hH x hxF
      rwa [pow_two] at h
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have htx : c.s.t * x * c.s.t⁻¹ = x := by
      have hcomm : c.s.t * x = x * c.s.t := (y54_t_comm_F c.s x hxF).symm
      rw [hcomm]; group
    have hg_inv : c.s.t * (c.s.t * c.d) * c.s.t = (c.s.t * c.d)⁻¹ := by
      calc c.s.t * (c.s.t * c.d) * c.s.t = (c.s.t * c.s.t) * c.d * c.s.t := by group
        _ = c.d * c.s.t := by rw [ht2, one_mul]
        _ = (c.s.t * c.d)⁻¹ := by rw [mul_inv_rev, hd_inv, ht_inv]
    have htn : c.s.t * n = n * c.s.t := (s3_comm_t_of_mem_L c.s hnL).symm
    have htninv : n⁻¹ * c.s.t = c.s.t * n⁻¹ := s3_comm_t_of_mem_L c.s (L.inv_mem hnL)
    have hm'inv : c.s.t * m' * c.s.t⁻¹ = m'⁻¹ := by
      rw [ht_inv, hm'def]
      have hconj : c.s.t * (n * (c.s.t * c.d) * n⁻¹) * c.s.t
          = n * (c.s.t * (c.s.t * c.d) * c.s.t) * n⁻¹ := by
        calc c.s.t * (n * (c.s.t * c.d) * n⁻¹) * c.s.t
            = (c.s.t * n) * (c.s.t * c.d) * (n⁻¹ * c.s.t) := by group
          _ = (n * c.s.t) * (c.s.t * c.d) * (c.s.t * n⁻¹) := by rw [htn, htninv]
          _ = n * (c.s.t * (c.s.t * c.d) * c.s.t) * n⁻¹ := by group
      rw [hconj, hg_inv]
      group
    have hm_eq : m = m' * x := by rw [hxdef]; group
    calc c.s.t * m * c.s.t⁻¹
        = c.s.t * (m' * x) * c.s.t⁻¹ := by rw [hm_eq]
      _ = (c.s.t * m' * c.s.t⁻¹) * (c.s.t * x * c.s.t⁻¹) := by group
      _ = m'⁻¹ * x := by rw [hm'inv, htx]
      _ = x * m'⁻¹ := by
        have hm'c : m' ∈ Subgroup.centralizer (c.s.fr.F : Set G) :=
          (Subgroup.mem_inf.mp hm'Y).2
        exact ((Subgroup.mem_centralizer_iff.mp
          ((Subgroup.centralizer (c.s.fr.F : Set G)).inv_mem hm'c)) x hxF).symm
      _ = m⁻¹ := by
        have hminv : m⁻¹ = x * m'⁻¹ := by
          calc m⁻¹ = (m' * x)⁻¹ := by rw [hm_eq]
            _ = x⁻¹ * m'⁻¹ := by rw [mul_inv_rev]
            _ = x * m'⁻¹ := by rw [hxinv]
        exact hminv.symm

theorem y57_caseB_sq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (htd : c.s.t * c.d ∈ M3 c.s) :
    ∀ m ∈ M3 c.s, m ^ 2 = f3phi c.s m := by
  intro m hm
  have h : c.s.t * m⁻¹ * c.s.t⁻¹ = m := by
    have h := y57_caseB_inv c hH htd m⁻¹ ((M3 c.s).inv_mem hm)
    rwa [inv_inv] at h
  calc m ^ 2 = m * (c.s.t * m⁻¹ * c.s.t⁻¹) := by rw [h, pow_two]
    _ = f3phi c.s m := by unfold f3phi; group

end CFSG.OddStandard.HigherRank.YamadaG23
