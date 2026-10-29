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

theorem y7a_cent_M6_A (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    centIn (M6 c.e) c.s.fr.A = V1 c.e := by
  have h := c.y7acfg hH
  have htinv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right (y7a_t_sq h)
  have htX : c.s.t ∈ y7aX c :=
    y7a_C6_le_X c hH hF
      (y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_right (y7a_t_mem_C0 h)))
  have htN : c.s.t ∈ Subgroup.normalizer (V1 c.e : Set G) :=
    y7a_C1_le_N_V h (Subgroup.mem_sup_right (y7a_t_mem_C0 h))
  have hV1C : V1 c.e ≤ centIn (M6 c.e) c.s.fr.A := by
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨le_trans le_sup_right (y7a_AV1_le_M6 c hH hF) hv, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a ha
    exact y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  refine le_antisymm ?_ hV1C
  by_contra hle
  change ¬ ∀ x, x ∈ centIn (M6 c.e) c.s.fr.A → x ∈ V1 c.e at hle
  push Not at hle
  obtain ⟨m, hm, hmNotV⟩ := hle
  have hmM6 : m ∈ M6 c.e := (Subgroup.mem_inf.mp hm).1
  have htNormM : c.s.t ∈ Subgroup.normalizer (centIn (M6 c.e) c.s.fr.A : Set G) := by
    have hfwd : ∀ y ∈ centIn (M6 c.e) c.s.fr.A,
        c.s.t * y * c.s.t⁻¹ ∈ centIn (M6 c.e) c.s.fr.A := by
      intro y hy
      obtain ⟨hyM6, hyCent⟩ := Subgroup.mem_inf.mp hy
      have hyc : ∀ a ∈ c.s.fr.A, a * y = y * a := Subgroup.mem_centralizer_iff.mp hyCent
      refine Subgroup.mem_inf.mpr ⟨y7a_M6_normal c hH hF c.s.t htX y hyM6, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro a ha
      have hta : c.s.t * a = a * c.s.t := (s3_comm_t_of_mem_A c.s ha).symm
      have hya : a * y = y * a := hyc a ha
      rw [htinv]
      calc a * (c.s.t * y * c.s.t) = (a * c.s.t) * y * c.s.t := by group
        _ = (c.s.t * a) * y * c.s.t := by rw [← hta]
        _ = c.s.t * (a * y) * c.s.t := by group
        _ = c.s.t * (y * a) * c.s.t := by rw [hya]
        _ = c.s.t * y * (a * c.s.t) := by group
        _ = c.s.t * y * (c.s.t * a) := by rw [← hta]
        _ = (c.s.t * y * c.s.t) * a := by group
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hfwd y hy
    · intro hy
      have hmem := hfwd (c.s.t * y * c.s.t⁻¹) hy
      have heq : c.s.t * (c.s.t * y * c.s.t⁻¹) * c.s.t⁻¹ = y := by
        rw [htinv]
        calc c.s.t * (c.s.t * y * c.s.t) * c.s.t
            = (c.s.t * c.s.t) * y * (c.s.t * c.s.t) := by group
          _ = y := by rw [y7a_t_sq h]; group
      rw [heq] at hmem
      exact hmem
  have hCM : ∀ c' ∈ zpowers c.s.t, ∀ y ∈ centIn (M6 c.e) c.s.fr.A,
      c' * y * c'⁻¹ ∈ centIn (M6 c.e) c.s.fr.A := by
    intro c' hc' y hy
    exact (Subgroup.mem_set_normalizer_iff.mp (Subgroup.zpowers_le.mpr htNormM hc') y).mp hy
  have hMV : ∀ y ∈ centIn (M6 c.e) c.s.fr.A, ∀ v ∈ V1 c.e, y * v * y⁻¹ ∈ V1 c.e := by
    intro y hy v hv
    have hyc : ∀ w ∈ V1 c.e, w * y = y * w :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).2
    have hcomm : y * v = v * y := (hyc v hv).symm
    have heq : y * v * y⁻¹ = v := by rw [hcomm]; group
    rw [heq]
    exact hv
  have hCV : ∀ c' ∈ zpowers c.s.t, ∀ v ∈ V1 c.e, c' * v * c'⁻¹ ∈ V1 c.e := by
    intro c' hc' v hv
    exact (Subgroup.mem_set_normalizer_iff.mp (Subgroup.zpowers_le.mpr htN hc') v).mp hv
  have hC2 : IsPGroup 2 (zpowers c.s.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.s.t_order]; norm_num)
  have hM2 : IsPGroup 2 (centIn (M6 c.e) c.s.fr.A) :=
    (y7a_C6_isPGroup c).to_le (le_trans inf_le_left (y7a_M6_le_C6 c))
  obtain ⟨x, hxM, hxNotV, hxcomm⟩ :=
    y7a_pgroup_fixed (C := zpowers c.s.t) (M := centIn (M6 c.e) c.s.fr.A) (V := V1 c.e)
      hC2 hM2 hV1C hMV hCV hCM ⟨m, hm, hmNotV⟩
  have hxM6 : x ∈ M6 c.e := (Subgroup.mem_inf.mp hxM).1
  have hxt : ⁅x, c.s.t⁆ ∈ V1 c.e := by
    have h1 : ⁅c.s.t, x⁆ ∈ V1 c.e := hxcomm c.s.t (Subgroup.mem_zpowers c.s.t)
    have h2 : ⁅x, c.s.t⁆ = ⁅c.s.t, x⁆⁻¹ :=
      (commutatorElement_inv (g₁ := c.s.t) (g₂ := x)).symm
    rw [h2]
    exact (V1 c.e).inv_mem h1
  haveI : (c.s.fr.Z.subgroupOf c.s.fr.A).Normal := y7a_Z_normal_A c hH
  obtain ⟨ψ, lab, P, hP⟩ := y7a_reg_data c hH hF
  obtain ⟨f, hchar, -, -, hker⟩ := y7a_mod_hom c hH hF hP
  have hfx : f ⟨x, hxM6⟩ = 1 := by
    have h1 := hchar ⟨x, hxM6⟩ (1 : ↥c.s.fr.A) (by simpa using hxt)
    simpa using h1
  have hxAV : x ∈ AV1 c.e := by
    have hmem : (⟨x, hxM6⟩ : ↥(M6 c.e)) ∈ f.ker := MonoidHom.mem_ker.mpr hfx
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hxCentA : ∀ a ∈ c.s.fr.A, a * x = x * a :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxM).2
  have hxCentV : ∀ v ∈ V1 c.e, v * x = x * v :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxM6).2
  have hxCentral : ∀ w ∈ c.s.fr.A ⊔ V1 c.e, x * w = w * x := by
    intro w hw
    obtain ⟨a, ha, v, hv, rfl⟩ := y7a_AV_elems h w hw
    calc x * (a * v) = (x * a) * v := by group
      _ = (a * x) * v := by rw [(hxCentA a ha).symm]
      _ = a * (x * v) := by group
      _ = a * (v * x) := by rw [(hxCentV v hv).symm]
      _ = (a * v) * x := by group
  exact hxNotV (y7a_cen_AV h x hxAV hxCentral)

end CFSG.OddStandard.HigherRank.YamadaG23
