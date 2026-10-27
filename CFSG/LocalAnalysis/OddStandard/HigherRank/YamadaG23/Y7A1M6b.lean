module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1M6a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

section Config

variable {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_not_comm_d_t (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : d * t ≠ t * d := by
  intro hcomm
  have htdt : t * d * t⁻¹ = d := by
    rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right (y7a_t_sq h)]
    calc t * d * t = d * t * t := by rw [hcomm]
      _ = d := by rw [mul_assoc, y7a_t_sq h, mul_one]
  rw [y7a_tdt h] at htdt
  exact h.cfg.z_ne (mul_right_cancel (b := d) (by simpa using htdt))

private lemma y7a_mem_A_of_mem_V_comm_t (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {v : G}
    (hv : v ∈ V) (hvt : v * t = t * v) : v ∈ A := by
  rcases y7a_V_elems h v hv with h1 | hz | hd | hzd
  · rw [h1]; exact A.one_mem
  · rw [hz]; exact y7a_z_mem_A h
  · exact absurd (by rw [hd] at hvt; exact hvt) (y7a_not_comm_d_t h)
  · exfalso
    have hzcomm : Commute z t := h.cfg.t_cent z (y7a_z_mem_A h)
    have hcomm : Commute (z * d) t := by rw [← hzd]; exact hvt
    have hdt : Commute d t := by
      have hdz : d = z⁻¹ * (z * d) := by group
      rw [hdz]
      exact (hzcomm.inv_left).mul_left hcomm
    exact y7a_not_comm_d_t h hdt

end Config

theorem y7a_acts_trans (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    ActsTransOutside (M6 c.e) (C1 c.e) (V1 c.e) (AV1 c.e) := by
  have h := c.y7acfg hH
  have hM6X : M6 c.e ≤ y7aX c := (y7a_M6_le_C6 c).trans (y7a_C6_le_X c hH hF)
  unfold ActsTransOutside
  refine ⟨hM6X.trans inf_le_left, hM6X.trans inf_le_right, ?_⟩
  intro u hu1 hu2 v hv1 hv2
  have hu16 : u ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) := ⟨hu1, hu2⟩
  have hv16 : v ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) := ⟨hv1, hv2⟩
  obtain ⟨p, hpP, hpuv⟩ := hP.P_trans (lab u) (lab v)
  obtain ⟨m, hmM6, hψm⟩ := y7a_psi_M6 c hH hF hP p hpP
  refine ⟨(m : G), hmM6, ?_⟩
  have hmX : (m : G) ∈ y7aX c := hM6X hmM6
  obtain ⟨hmC1, hmV⟩ := Subgroup.mem_inf.mp hmX
  have hact := hP.act m u hu16
  rw [hψm] at hact
  have hlab : lab ((m : G) * u * (m : G)⁻¹) = lab v := hact.symm.trans hpuv
  have hX16 : (m : G) * u * (m : G)⁻¹ ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp hmC1 u).mp hu1, ?_⟩
    intro hconj
    exact hu2 ((y7a_conj_AV h hmC1 hmV u).mpr hconj)
  have hmem : ((m : G) * u * (m : G)⁻¹)⁻¹ * v ∈ V1 c.e :=
    (hP.lab_iff _ hX16 v hv16).mp hlab
  simpa [mul_inv_rev, inv_inv] using (V1 c.e).inv_mem hmem

theorem y7a_H_inf_M6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    c.s.H ⊓ M6 c.e = c.s.fr.A := by
  have h := c.y7acfg hH
  apply le_antisymm
  · intro m hm
    obtain ⟨hmH, hmM6⟩ := Subgroup.mem_inf.mp hm
    have hmC6 : m ∈ C6 c.e := y7a_M6_le_C6 c hmM6
    have hmX : m ∈ y7aX c := (y7a_C6_le_X c hH hF) hmC6
    have hmC1 : m ∈ normalizer (C1 c.e : Set G) := (Subgroup.mem_inf.mp hmX).1
    have hmt : m * c.s.t = c.s.t * m := Subgroup.mem_centralizer_singleton_iff.mp hmH
    have hstab : c.s.t⁻¹ * (m * c.s.t * m⁻¹) ∈ V1 c.e := by
      have hconj : m * c.s.t * m⁻¹ = c.s.t := by
        calc m * c.s.t * m⁻¹ = c.s.t * m * m⁻¹ := by rw [hmt]
          _ = c.s.t := by group
      rw [hconj]
      simpa using (V1 c.e).one_mem
    have hmY : m ∈ y7aY c := (y7a_stab_iff h hmC1).mp hstab
    have hmAV : m ∈ AV1 c.e := by
      rw [← y7a_M6_inf_Y c hH hF hP]
      exact ⟨hmM6, hmY⟩
    obtain ⟨a, ha, v, hv, hm_eq⟩ := y7a_AV_elems h m hmAV
    have hvt : v * c.s.t = c.s.t * v := by
      have hma : Commute a c.s.t := h.cfg.t_cent a ha
      have hmm : Commute m c.s.t := hmt
      have hv' : v = a⁻¹ * m := by rw [hm_eq]; group
      rw [hv']
      exact (hma.inv_left).mul_left hmm
    have hvA : v ∈ c.s.fr.A := y7a_mem_A_of_mem_V_comm_t h hv hvt
    rw [hm_eq]
    exact (c.s.fr.A).mul_mem ha hvA
  · intro a ha
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · show a ∈ centralizer ({c.s.t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.cfg.t_cent a ha
    · exact y7a_AV1_le_M6 c hH hF (Subgroup.mem_sup_left ha)

theorem y7a_NC1_eq_NHA_M6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    normalizer (C1 c.e : Set G) = normIn c.s.H c.s.fr.A ⊔ M6 c.e := by
  have h := c.y7acfg hH
  rw [y7a_NC1_eq c hH hF]
  apply le_antisymm
  · intro x hx
    obtain ⟨m, hmC6, y, hyY, rfl⟩ := y7a_X_eq_C6Y c hH hF hP x hx
    have htK : c.s.t ∈ normIn c.s.H c.s.fr.A := s5_T_le_NHA hH (s3_t_mem_T c.s)
    have hM6K : M6 c.e ≤ normIn c.s.H c.s.fr.A ⊔ M6 c.e := le_sup_right
    have hC6K : C6 c.e ≤ normIn c.s.H c.s.fr.A ⊔ M6 c.e := by
      rw [(y7a_C6_eq_M6 c hH hF).2]
      exact sup_le hM6K (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left htK))
    have hmK : m ∈ normIn c.s.H c.s.fr.A ⊔ M6 c.e := hC6K hmC6
    have hdM6 : c.d ∈ M6 c.e :=
      y7a_AV1_le_M6 c hH hF (Subgroup.mem_sup_right (y7a_d_mem_V h))
    have hdK : c.d ∈ normIn c.s.H c.s.fr.A ⊔ M6 c.e := Subgroup.mem_sup_right hdM6
    have hYleK : y7aY c ≤ normIn c.s.H c.s.fr.A ⊔ M6 c.e := by
      rw [show y7aY c = normIn c.s.H c.s.fr.A ⊔ zpowers c.d from s5_Y_eq c.toCtx5 hH]
      exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hdK)
    exact (normIn c.s.H c.s.fr.A ⊔ M6 c.e).mul_mem hmK (hYleK hyY)
  · refine sup_le ?_ ?_
    · exact (s5_NHA_le_Y c.toCtx5 hH).trans (y7a_Y_le_X c hH)
    · exact (y7a_M6_le_C6 c).trans (y7a_C6_le_X c hH hF)

end CFSG.OddStandard.HigherRank.YamadaG23
