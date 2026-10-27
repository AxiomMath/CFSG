module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Hyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Def

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y63_t_conj_npow {u t : G} (ht : orderOf t = 2)
    (hinv : t * u * t⁻¹ = u⁻¹) (i : ℕ) : t * u ^ i = (u ^ i)⁻¹ * t := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htu : t * u = u⁻¹ * t := by
    have h := congrArg (· * t) hinv
    rw [hti] at h
    simpa [mul_assoc, ht2, mul_one] using h
  induction i with
  | zero => simp
  | succ i ih =>
    calc t * u ^ (i + 1) = t * (u ^ i * u) := by rw [pow_succ]
      _ = (t * u ^ i) * u := by group
      _ = ((u ^ i)⁻¹ * t) * u := by rw [ih]
      _ = (u ^ i)⁻¹ * (t * u) := by group
      _ = (u ^ i)⁻¹ * (u⁻¹ * t) := by rw [htu]
      _ = ((u ^ i)⁻¹ * u⁻¹) * t := by group
      _ = (u ^ (i + 1))⁻¹ * t := by rw [← mul_inv_rev, ← pow_succ']

theorem y63_C1_le_Q (c : Ctx6 G L) (hH : F33Hyp c.s c.e) : C1 c.e ≤ y63Q c := by
  have cfg := c.y6cfg hH
  rw [y6_C1_eq c]
  apply sup_le
  · exact (s3_A_le_S c.s).trans (c.s.S_le_R.trans (c.s.R_le_T.trans le_sup_left))
  · rw [cfg.hC0]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have huV1 : c.d * c.s.t ∈ V1 c.e := by
        rw [c.hV]
        exact Subgroup.mem_zpowers _
      exact Subgroup.mem_sup_right ((inf_le_right : V1 c.e ≤ M3 c.s) huV1)
    · exact Subgroup.mem_sup_left (c.s.R_le_T (s3_t_mem_R c.s))

theorem y63_t_mem_C1 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) : c.s.t ∈ C1 c.e := by
  have cfg := c.y6cfg hH
  exact Subgroup.mem_sup_right (y6_t_mem_C0 cfg)

theorem y63_C1_ZE64 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    Y63ZE64 (zpowers c.s.fr.z) (C1 c.e) := by
  have cfg := c.y6cfg hH
  unfold Y63ZE64
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_left (s3_z_mem_A c.s)
  · rw [y6_C1_eq c, y6_card_C1 cfg]
    norm_num
  · intro x hx
    obtain ⟨a, ha, c0, hc0, rfl⟩ := y6_C1_elems cfg x hx
    have hcomm : a * c0 = c0 * a := y6_C0_comm cfg a ha c0 hc0
    have hsq : (a * c0) ^ 2 = a ^ 2 * c0 ^ 2 := by
      simp only [pow_two]
      calc (a * c0) * (a * c0) = a * (c0 * a) * c0 := by group
        _ = a * (a * c0) * c0 := by rw [hcomm.symm]
        _ = a * a * (c0 * c0) := by group
    rw [hsq]
    apply Subgroup.mul_mem
    · rcases y6q8_sq_cases cfg.rel a (cfg.hA ▸ ha) with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    · rcases y6_d8_elems cfg.u_ord cfg.t_ord cfg.t_inv c0 (cfg.hC0 ▸ hc0) with ⟨i, hi | hi⟩
      · rw [hi]
        have hsq_i : ((c.d * c.s.t) ^ i) ^ 2 = c.s.fr.z ^ i := by
          rw [← pow_mul, ← cfg.u_sq, ← pow_mul, show i * 2 = 2 * i by omega]
        rw [hsq_i]
        exact Subgroup.npow_mem_zpowers _ i
      · rw [hi]
        have ht2 : c.s.t * c.s.t = 1 := by
          have h := pow_orderOf_eq_one c.s.t
          rw [cfg.t_ord] at h
          simpa [pow_two] using h
        have hsq : ((c.d * c.s.t) ^ i * c.s.t) ^ 2 = 1 := by
          rw [pow_two]
          calc ((c.d * c.s.t) ^ i * c.s.t) * ((c.d * c.s.t) ^ i * c.s.t)
              = (c.d * c.s.t) ^ i * (c.s.t * (c.d * c.s.t) ^ i) * c.s.t := by group
            _ = (c.d * c.s.t) ^ i * (((c.d * c.s.t) ^ i)⁻¹ * c.s.t) * c.s.t := by
                  rw [y63_t_conj_npow cfg.t_ord cfg.t_inv i]
            _ = (((c.d * c.s.t) ^ i) * ((c.d * c.s.t) ^ i)⁻¹) * (c.s.t * c.s.t) := by group
            _ = 1 := by rw [mul_inv_cancel, one_mul, ht2]
        rw [hsq]
        exact Subgroup.one_mem _
  · exact Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => y6_comm_C1 cfg g₁ hg₁ g₂ hg₂

theorem y63_z_mem_cen_Q (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R = c.s.T) : c.s.fr.z ∈ cen (y63Q c) := by
  have hzcR : c.s.fr.z ∈ cen c.s.R := by
    rw [s3_cen_R_eq c.s hH.hS hH.hZ (s3_T_inf_centralizer c.s hH.h31)]
    exact Subgroup.subset_closure (by simp)
  have hT : c.s.T ≤ Subgroup.centralizer ({c.s.fr.z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyz : y = c.s.fr.z := Set.mem_singleton_iff.mp hy
    subst hyz
    exact (Subgroup.mem_centralizer_iff.mp hzcR.2 x (hRT.symm ▸ hx)).symm
  have hzM : c.s.fr.z ∈ M3 c.s := (le_sup_right : c.s.fr.F ≤ M3 c.s) (y54_z_mem_F c.s)
  have hM : M3 c.s ≤ Subgroup.centralizer ({c.s.fr.z} : Set G) := by
    haveI : IsMulCommutative ↥(M3 c.s) := y6e_M3_comm c.toCtx5 hF
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyz : y = c.s.fr.z := Set.mem_singleton_iff.mp hy
    subst hyz
    exact (Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) hx hzM).symm
  have hQle : y63Q c ≤ Subgroup.centralizer ({c.s.fr.z} : Set G) := sup_le hT hM
  refine ⟨Subgroup.mem_sup_left
    (c.s.R_le_T (c.s.S_le_R (s3_A_le_S c.s (s3_z_mem_A c.s)))), ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr
    (fun x hx => (Subgroup.mem_centralizer_iff.mp (hQle hx) c.s.fr.z (Set.mem_singleton _)).symm)

theorem y63_C1_inf_S3_le (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hY : Y63Hyps c) :
    C1 c.e ⊓ S3 c.s ≤ AV1 c.e := by
  have cfg := c.y6cfg hH
  intro x hx
  obtain ⟨hxC1, hxS3⟩ := hx
  obtain ⟨a, ha, c0, hc0, hxeq⟩ := y6_C1_elems cfg x hxC1
  have haS3 : a ∈ S3 c.s :=
    (le_sup_left : c.s.fr.S ≤ S3 c.s) (s3_A_le_S c.s ha)
  have hc0S3 : c0 ∈ S3 c.s := by
    have hc0eq : c0 = a⁻¹ * x := by rw [hxeq]; group
    rw [hc0eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haS3) hxS3
  have huS3 : c.d * c.s.t ∈ S3 c.s := by
    have huV1 : c.d * c.s.t ∈ V1 c.e := by
      rw [c.hV]
      exact Subgroup.mem_zpowers _
    exact (le_sup_right : M3 c.s ≤ S3 c.s)
      ((inf_le_right : V1 c.e ≤ M3 c.s) huV1)
  rcases y6_d8_elems cfg.u_ord cfg.t_ord cfg.t_inv c0 (cfg.hC0 ▸ hc0) with ⟨i, hi | hi⟩
  · rw [hxeq, hi]
    exact Subgroup.mul_mem_sup ha (by rw [c.hV]; exact Subgroup.npow_mem_zpowers _ i)
  · exfalso
    apply hY.t_not_mem
    have ht_eq : c.s.t = ((c.d * c.s.t) ^ i)⁻¹ * c0 := by rw [hi]; group
    rw [ht_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ huS3 i)) hc0S3

end CFSG.OddStandard.HigherRank.YamadaG23
