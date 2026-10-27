module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_quotModIso (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    QuotModIso (normIn c.s.H c.s.fr.A) (M6 c.e) (AV1 c.e) c.s.fr.A c.s.fr.Z := by
  have hcfg := c.y7acfg hH
  haveI hZ : (c.s.fr.Z.subgroupOf c.s.fr.A).Normal := by
    have hle : c.s.fr.Z ≤ c.s.fr.A := by
      rw [SFrame.Z]
      exact Subgroup.zpowers_le.mpr (y7a_z_mem_A hcfg)
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro w a hw ha
    rw [SFrame.Z] at hw ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : a * c.s.fr.z = c.s.fr.z * a :=
      y6q8_z_central hcfg.cfg.rel a (by rwa [hcfg.cfg.hA] at ha)
    rw [show a * c.s.fr.z ^ k * a⁻¹ = c.s.fr.z ^ k by
      rw [← conj_zpow, hcomm, mul_assoc, mul_inv_cancel, mul_one]]
    exact Subgroup.zpow_mem_zpowers c.s.fr.z k
  obtain ⟨f, hf1, hex, hsurj, hker⟩ := y7a_mod_hom c hH hF hP
  refine y7a_quotModIso_of f hsurj hker ?_
  intro n hn w w' hw q q' hq h1
  obtain ⟨hnH, hnA⟩ := Subgroup.mem_inf.mp hn
  have hnH' : n ∈ Subgroup.centralizer ({c.s.t} : Set G) := hnH
  have hnt : n * c.s.t = c.s.t * n := Subgroup.mem_centralizer_singleton_iff.mp hnH'
  obtain ⟨a, ha⟩ := hex w
  have h1a : (a : ↥c.s.fr.A ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) =
      (q : ↥c.s.fr.A ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) := by
    rw [← hf1 w a ha, h1]
  have haq : (a : G)⁻¹ * (q : G) ∈ c.s.fr.Z := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1a
    simpa using h1a
  have hZleV : c.s.fr.Z ≤ V1 c.e := by
    rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr (y7a_z_mem_V hcfg)
  have hqV : (q : G)⁻¹ * ⁅(w : G), c.s.t⁆ ∈ V1 c.e := by
    have hmem : ((a : G)⁻¹ * (q : G))⁻¹ * ((a : G)⁻¹ * ⁅(w : G), c.s.t⁆) ∈ V1 c.e :=
      (V1 c.e).mul_mem ((V1 c.e).inv_mem (hZleV haq)) ha
    rwa [show ((a : G)⁻¹ * (q : G))⁻¹ * ((a : G)⁻¹ * ⁅(w : G), c.s.t⁆) =
      (q : G)⁻¹ * ⁅(w : G), c.s.t⁆ by group] at hmem
  have hnY : n ∈ y7aY c := s5_NHA_le_Y c.toCtx5 hH ⟨hnH, hnA⟩
  have hnX : n ∈ y7aX c := y7a_Y_le_X c hH hnY
  have hnV : n ∈ Subgroup.normalizer (V1 c.e : Set G) := (Subgroup.mem_inf.mp hnX).2
  have hnt' : n * c.s.t * n⁻¹ = c.s.t := by
    rw [hnt, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : ⁅(w' : G), c.s.t⁆ = n * ⁅(w : G), c.s.t⁆ * n⁻¹ := by
    rw [hw, conjugate_commutatorElement, hnt']
  have hq'V : (q' : G)⁻¹ * ⁅(w' : G), c.s.t⁆ ∈ V1 c.e := by
    have hmem : n * ((q : G)⁻¹ * ⁅(w : G), c.s.t⁆) * n⁻¹ ∈ V1 c.e :=
      (Subgroup.mem_normalizer_iff.mp hnV _).mp hqV
    rwa [show n * ((q : G)⁻¹ * ⁅(w : G), c.s.t⁆) * n⁻¹ =
      (q' : G)⁻¹ * ⁅(w' : G), c.s.t⁆ by rw [hconj, hq]; group] at hmem
  exact hf1 w' q' hq'V

end CFSG.OddStandard.HigherRank.YamadaG23
