module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Norm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1RegD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_mem_AV_of_comm (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {m : G} (hm : m ∈ M6 c.e) (hmt : ⁅m, c.s.t⁆ ∈ V1 c.e) : m ∈ AV1 c.e := by
  haveI : (c.s.fr.Z.subgroupOf c.s.fr.A).Normal := y7a_Z_normal_A c hH
  obtain ⟨ψ, lab, P, hP⟩ := y7a_reg_data c hH hF
  obtain ⟨f, hchar, -, -, hker⟩ := y7a_mod_hom c hH hF hP
  have hfx : f ⟨m, hm⟩ = 1 := by
    have h1 := hchar ⟨m, hm⟩ (1 : ↥c.s.fr.A) (by simpa using hmt)
    simpa using h1
  have hmem : (⟨m, hm⟩ : ↥(M6 c.e)) ∈ f.ker := MonoidHom.mem_ker.mpr hfx
  rw [hker] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

theorem y7a_t_not_mem_M6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) : c.s.t ∉ M6 c.e := by
  intro ht
  have h := c.y7acfg hH
  have hd : c.d ∈ V1 c.e := by
    rw [h.hV]
    exact Subgroup.subset_closure (by simp)
  have hcomm : c.d * c.s.t = c.s.t * c.d :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht).2 c.d hd
  have h1 : c.s.t * c.d * c.s.t⁻¹ = c.d := by
    rw [← hcomm]
    group
  have h2 : c.s.fr.z * c.d = c.d := by
    rw [← y7a_tdt h]
    exact h1
  exact h.cfg.z_ne (by simpa using h2)

theorem y7a_inv_mem_C1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h3b : ∀ m ∈ M6 c.e, m ^ 2 ∈ V1 c.e) {y : G} (hy : y ∈ C6 c.e) (hyM : y ∉ M6 c.e)
    (hy2 : y ^ 2 ∈ V1 c.e) : y ∈ C1 c.e := by
  classical
  have h := c.y7acfg hH
  have ht2 : c.s.t * c.s.t = 1 := y7a_t_sq h
  have htinv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
  have htX : c.s.t ∈ y7aX c :=
    y7a_C6_le_X c hH hF
      (y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_right (y7a_t_mem_C0 h)))
  have hC6eq : C6 c.e = M6 c.e ⊔ zpowers c.s.t := (y7a_C6_eq_M6 c hH hF).2
  have htN : zpowers c.s.t ≤ normalizer (M6 c.e : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact y7a_M6_normal c hH hF c.s.t htX x hx
    · intro hx
      have hmem := y7a_M6_normal c hH hF c.s.t htX _ hx
      have heq : c.s.t * (c.s.t * x * c.s.t⁻¹) * c.s.t⁻¹ = x := by
        rw [htinv]
        calc c.s.t * (c.s.t * x * c.s.t) * c.s.t
            = (c.s.t * c.s.t) * x * (c.s.t * c.s.t) := by group
          _ = x := by rw [ht2]; group
      rw [heq] at hmem
      exact hmem
  have hy' : y ∈ ((M6 c.e ⊔ zpowers c.s.t : Subgroup G) : Set G) := hC6eq ▸ hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (M6 c.e) (zpowers c.s.t) htN] at hy'
  obtain ⟨m, hm, τ, hτ, rfl⟩ := hy'
  have hτt : τ = c.s.t := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    have h2 : c.s.t ^ (2 : ℤ) = 1 := by simpa [pow_two] using ht2
    have hti : c.s.t ^ i = c.s.t ^ (i % 2) := zpow_eq_zpow_emod i h2
    rcases Int.emod_two_eq_zero_or_one i with hi | hi
    · rw [hti, hi] at hyM
      exact absurd (by simpa using hm) hyM
    · rw [hti, hi]
      simp
  subst hτt
  have hm' : c.s.t * m * c.s.t⁻¹ ∈ M6 c.e := y7a_M6_normal c hH hF c.s.t htX m hm
  have hsq : (m * c.s.t) ^ 2 = m * (c.s.t * m * c.s.t⁻¹) := by
    rw [pow_two]
    calc m * c.s.t * (m * c.s.t) = m * (c.s.t * m * c.s.t⁻¹) * (c.s.t * c.s.t) := by group
      _ = m * (c.s.t * m * c.s.t⁻¹) := by rw [ht2]; group
  have hcomm : ⁅m, c.s.t⁆ ∈ V1 c.e := by
    obtain ⟨m', hm'def⟩ : ∃ m', m' = c.s.t * m * c.s.t⁻¹ := ⟨_, rfl⟩
    rw [← hm'def] at hm' hsq
    have hsq' : m * m' ∈ V1 c.e := hsq ▸ hy2
    have hsqm' : (m' * m')⁻¹ ∈ V1 c.e := by
      simpa [pow_two] using (V1 c.e).inv_mem (h3b _ hm')
    have heq : ⁅m, c.s.t⁆ = (m * m') * (m' * m')⁻¹ := by
      rw [commutatorElement_def, hm'def]
      group
    rw [heq]
    exact (V1 c.e).mul_mem hsq' hsqm'
  have hmAV : m ∈ AV1 c.e := y7a_mem_AV_of_comm c hH hF hm hcomm
  have hmC1 : m ∈ C1 c.e := y7a_AV_le_C1 h hmAV
  exact (C1 c.e).mul_mem hmC1 (Subgroup.mem_sup_right (y7a_t_mem_C0 h))

end CFSG.OddStandard.HigherRank.YamadaG23
