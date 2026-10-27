module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBBase
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79w

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7c_JF_inf_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    JF c.s ⊓ M3 c.s = c.s.fr.F := by
  refine le_antisymm ?_ (le_inf (y7c_F_le_JF hH) (y54_M3_cand c hH).1)
  calc JF c.s ⊓ M3 c.s ≤ c.s.H ⊓ M3 c.s :=
        inf_le_inf ((y7c_JF_le_L c.s).trans (s3_L_le_H c.s hH.hS)) le_rfl
    _ = c.s.fr.F := y54_H_inf_M3 c hH

theorem y7c_B_J_iso (c : Ctx7 G L) (hb : B7Std c) :
    Nonempty (↥(y7cJC c) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  classical
  let ψ : ↥(JF c.s) →* y7cGam c.s :=
    (y7cPi c.s).comp (Subgroup.inclusion (y7c_JF_le_X c hb))
  have hψran : ψ.range = y7cJC c := by
    rw [y7cJC, y7cImg, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hψker : ψ.ker = c.s.fr.F.subgroupOf (JF c.s) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change y7cPi c.s (Subgroup.inclusion (y7c_JF_le_X c hb) x) = 1 ↔
      (x : G) ∈ c.s.fr.F
    rw [y7cPi_eq_one_iff]
    simp only [Subgroup.coe_inclusion]
    constructor
    · intro hm
      rw [← y7c_JF_inf_M3 c.toCtx5 hb.hH, Subgroup.mem_inf]
      exact ⟨x.2, hm⟩
    · intro hf
      rw [← y7c_JF_inf_M3 c.toCtx5 hb.hH, Subgroup.mem_inf] at hf
      exact hf.2
  have hN : normIn L c.s.fr.F = JF c.s := y7c_NLF_eq_JF hb.hH
  have hz : zL L ⊔ c.s.fr.F = c.s.fr.F := by rw [f3_zL_eq_bot hb.hH, bot_sup_eq]
  obtain ⟨hNsub, ⟨eN⟩⟩ := hb.hH.hLF.fact18.2.2.2.2.1
  letI := hNsub
  haveI hFJ : (c.s.fr.F.subgroupOf (JF c.s)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by rw [← hN]; exact inf_le_right)
  let ψ' : ↥(JF c.s) →* ↥(y7cJC c) :=
    ψ.codRestrict (y7cJC c) (fun x => by rw [← hψran]; exact ⟨x, rfl⟩)
  have hψ'surj : Function.Surjective ψ' := by
    intro y
    have hy : (y : y7cGam c.s) ∈ ψ.range := by rw [hψran]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hψ'ker : ψ'.ker = c.s.fr.F.subgroupOf (JF c.s) := by
    rw [← hψker]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      simpa [ψ'] using Subtype.ext_iff.mp h
    · intro h
      exact Subtype.ext (by simpa [ψ'] using h)
  have e₁ : (↥(JF c.s) ⧸ c.s.fr.F.subgroupOf (JF c.s)) ≃* ↥(y7cJC c) :=
    (QuotientGroup.quotientMulEquivOfEq hψ'ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ'surj)
  have e₂ : (↥(JF c.s) ⧸ c.s.fr.F.subgroupOf (JF c.s)) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    ((QuotientGroup.equivQuotientSubgroupOfOfEq hz hN).symm).trans eN
  exact ⟨e₁.symm.trans e₂⟩

theorem y7c_B_rho_inj (c : Ctx7 G L) (hb : B7Std c) :
    ∀ j ∈ y7cJC c, y7cRhoC c hb j = 1 → j = 1 := by
  intro j hj hr
  rw [y7cJC, mem_y7cImg] at hj
  obtain ⟨x, hxJ, rfl⟩ := hj
  rw [y7cPi_eq_one_iff]
  have hxL : (x : G) ∈ L := y7c_JF_le_L c.s hxJ
  have hfix : ∀ m : ↥(M3 c.s), (x : G) * (m : G) * (x : G)⁻¹ = (m : G) := by
    intro m
    have h := congrArg (fun A : MulAut ↥(M3 c.s) => (A m : G)) hr
    rw [y7cRho_apply c.s (y7c_M3_comm c hb) x m] at h
    simpa using h
  have hxF : (x : G) ∈ c.s.fr.F := by
    rw [← y54_centIn_L_F hb.hH]
    refine Subgroup.mem_inf.mpr ⟨hxL, Subgroup.mem_centralizer_iff.mpr (fun f hf => ?_)⟩
    have hfM : f ∈ M3 c.s := (y54_M3_cand c.toCtx5 hb.hH).1 hf
    have hc := hfix ⟨f, hfM⟩
    calc f * (x : G) = (x : G) * f * (x : G)⁻¹ * (x : G) := by rw [hc]
      _ = (x : G) * f := by group
  exact (y54_M3_cand c.toCtx5 hb.hH).1 hxF

theorem y7c_fix_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) {x m : G} (hx : x ∈ JF c.s)
    (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1) (hm : m ∈ M3 c.s) (h : x * m * x⁻¹ = m) : m = 1 := by
  classical
  have hnc := y7c_order7_not_cent hH hx hx7 hx1
  have hF8 : Nat.card ↥c.s.fr.F = 8 := by simpa using (y54_F_isE3 hH).2
  have hxL : x ∈ L := y7c_JF_le_L c.s hx
  have hxnormF : ∀ f ∈ c.s.fr.F, x * f * x⁻¹ ∈ c.s.fr.F := y7c_JF_norm_F c.s x hx
  have hxH : x ∈ c.s.H := by
    rw [Setting3.H]
    exact Subgroup.mem_centralizer_iff.mpr (fun h' hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (s3_comm_t_of_mem_L c.s hxL).symm)
  have hxnorm : x ∈ normalizer (c.s.fr.F : Set G) := by
    have hxNL : x ∈ normIn L c.s.fr.F := by rw [y7c_NLF_eq_JF hH]; exact hx
    exact (Subgroup.mem_inf.mp hxNL).2
  have hxN : x ∈ normIn c.s.H c.s.fr.F := Subgroup.mem_inf.mpr ⟨hxH, hxnorm⟩
  obtain ⟨hNsub, hP⟩ := (y54_fact c hH).1.2.2.2
  letI := hNsub
  obtain ⟨φ, hφ⟩ := hP
  let m₀ : ↥(M3 c.s) := ⟨m, hm⟩
  have heq := hφ x hxN m₀ m₀ h.symm
  have hfix : ((φ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s)) m₀) : ↥c.s.fr.F) : G) = 1 :=
    y7c_order7_fpf hF8 hx7 hxnormF hnc
      (φ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s)) m₀)).2 heq.symm
  have hpi := (MulEquiv.map_eq_one_iff φ).mp (Subtype.ext hfix)
  have hmF : m ∈ c.s.fr.F := by
    have hker : m₀ ∈ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s))).ker :=
      MonoidHom.mem_ker.mpr hpi
    rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hker
    exact hker
  exact y7c_order7_fpf hF8 hx7 hxnormF hnc hmF h

theorem y7c_B_J_fpf (c : Ctx7 G L) (hb : B7Std c) :
    ∀ x ∈ y7cJC c, x ^ 7 = 1 → x ≠ 1 → ∀ m : ↥(M3 c.s), y7cRhoC c hb x m = m → m = 1 := by
  intro x hxJ hx7 hx1 m hxm
  rw [y7cJC, mem_y7cImg] at hxJ
  obtain ⟨x₁, hx₁J, rfl⟩ := hxJ
  have hconj : (x₁ : G) * (m : G) * (x₁ : G)⁻¹ = (m : G) := by
    have h := congrArg (fun z : ↥(M3 c.s) => (z : G)) hxm
    rw [y7cRho_apply c.s (y7c_M3_comm c hb) x₁ m] at h
    simpa using h
  have hx₁7M3 : (x₁ : G) ^ 7 ∈ M3 c.s := by
    have h7 : y7cPi c.s (x₁ ^ 7) = 1 := by rw [map_pow, hx7]
    simpa using (y7cPi_eq_one_iff c.s (x₁ ^ 7)).mp h7
  have hx₁7F : (x₁ : G) ^ 7 ∈ c.s.fr.F := by
    rw [← y7c_JF_inf_M3 c.toCtx5 hb.hH, Subgroup.mem_inf]
    exact ⟨pow_mem hx₁J 7, hx₁7M3⟩
  have hx₁14 : (x₁ : G) ^ 14 = 1 := by
    have h := y54_F_sq hb.hH ((x₁ : G) ^ 7) hx₁7F
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have hx0_7 : ((x₁ : G) ^ 2) ^ 7 = 1 := by
    rw [← pow_mul]
    norm_num
    exact hx₁14
  have hx0_ne : (x₁ : G) ^ 2 ≠ 1 := by
    intro h2
    apply hx1
    have hx₁2 : x₁ ^ 2 = 1 := Subtype.ext (by simpa using h2)
    have h2' : (y7cPi c.s x₁) ^ 2 = 1 := by rw [← map_pow, hx₁2, map_one]
    exact (pow_eq_one_iff_of_coprime (a := y7cPi c.s x₁) (m := 2) (n := 7)
      (by norm_num)).mp ⟨h2', hx7⟩
  have hx0_m : (x₁ : G) ^ 2 * (m : G) * ((x₁ : G) ^ 2)⁻¹ = (m : G) := by
    have hc : Commute (x₁ : G) (m : G) := by
      rw [commute_iff_eq]
      calc (x₁ : G) * (m : G) = (x₁ : G) * (m : G) * (x₁ : G)⁻¹ * (x₁ : G) := by group
        _ = (m : G) * (x₁ : G) := by rw [hconj]
    rw [(hc.pow_left 2).eq, mul_assoc, mul_inv_cancel, mul_one]
  exact Subtype.ext (y7c_fix_M3 c.toCtx5 hb.hH (pow_mem hx₁J 2) hx0_7 hx0_ne m.2 hx0_m)

end CFSG.OddStandard.HigherRank.YamadaG23
