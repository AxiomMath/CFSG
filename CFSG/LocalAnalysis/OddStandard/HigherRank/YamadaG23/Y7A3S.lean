module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3CA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Frat

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_C1_le_cs (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    C1 c.e ≤ centralizerSection c.s.fr.A c.s.fr.Z := by
  have h := c.y7acfg hH
  have hLFA := lfactsA_of_setting hH.hS hH.hZ c.s
  have hAC : ∀ a ∈ c.s.fr.A, ∀ g ∈ C0 c.e, a * g = g * a :=
    fun a ha g hg => y6_C0_comm h.cfg a ha g hg
  have hzA : c.s.fr.z ∈ c.s.fr.A := hLFA.z_mem
  have hzc : ∀ a ∈ c.s.fr.A, a * c.s.fr.z = c.s.fr.z * a := by
    intro a ha
    rw [h.cfg.hA] at ha
    exact y6q8_z_central h.cfg.rel a ha
  have hconjA : ∀ x ∈ C1 c.e, ∀ y ∈ c.s.fr.A, x * y * x⁻¹ ∈ c.s.fr.A := by
    intro x hx y hy
    obtain ⟨a, ha, g, hg, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hAC hx
    have hgy : g * y = y * g := (hAC y hy g hg).symm
    have heq : a * g * y * (a * g)⁻¹ = a * y * a⁻¹ := by
      calc a * g * y * (a * g)⁻¹ = a * (g * y) * g⁻¹ * a⁻¹ := by group
        _ = a * (y * g) * g⁻¹ * a⁻¹ := by rw [hgy]
        _ = a * y * a⁻¹ := by group
    rw [heq]
    exact c.s.fr.A.mul_mem (c.s.fr.A.mul_mem ha hy) (c.s.fr.A.inv_mem ha)
  have hcz : ∀ x ∈ C1 c.e, x * c.s.fr.z = c.s.fr.z * x := by
    intro x hx
    obtain ⟨a, ha, g, hg, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hAC hx
    have hgz : g * c.s.fr.z = c.s.fr.z * g := (hAC c.s.fr.z hzA g hg).symm
    calc a * g * c.s.fr.z = a * (g * c.s.fr.z) := by group
      _ = a * (c.s.fr.z * g) := by rw [hgz]
      _ = (a * c.s.fr.z) * g := by group
      _ = (c.s.fr.z * a) * g := by rw [hzc a ha]
      _ = c.s.fr.z * (a * g) := by group
  have hcomm : ∀ x ∈ C1 c.e, ∀ k ∈ c.s.fr.A, ⁅k, x⁆ ∈ c.s.fr.Z := by
    intro x hx k hk
    obtain ⟨a, ha, g, hg, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hAC hx
    have hgk : g * k⁻¹ * g⁻¹ = k⁻¹ := by
      have hkg : k⁻¹ * g = g * k⁻¹ := hAC k⁻¹ (c.s.fr.A.inv_mem hk) g hg
      calc g * k⁻¹ * g⁻¹ = (k⁻¹ * g) * g⁻¹ := by rw [hkg]
        _ = k⁻¹ := by group
    have heq : ⁅k, a * g⁆ = ⁅k, a⁆ := by
      simp only [commutatorElement_def]
      calc k * (a * g) * k⁻¹ * (a * g)⁻¹ = k * a * (g * k⁻¹ * g⁻¹) * a⁻¹ := by group
        _ = k * a * k⁻¹ * a⁻¹ := by rw [hgk]
    rw [heq]
    exact hLFA.comm_A k hk a ha
  intro x hx
  refine ⟨?_, ?_, hcomm x hx⟩
  · rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · exact hconjA x hx y
    · intro hy
      have hmem := hconjA x⁻¹ ((C1 c.e).inv_mem hx) _ hy
      have heq : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rw [heq] at hmem
      exact hmem
  · refine Subgroup.centralizer_le_normalizer (c.s.fr.Z : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (hcz x hx).symm i)).eq

theorem y7a_sylow_C1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) :
    IsSylowIn 2 (centralizerSection c.s.fr.A c.s.fr.Z) (C1 c.e) := by
  have hC1p : IsPGroup 2 (C1 c.e) :=
    (y7a_C6_isPGroup c).to_le (y7a_C1_le_C6 c hH hF)
  refine ⟨y7a_C1_le_cs c hH, hC1p, ?_⟩
  exact y6_sylow_of_self_normalizing (y7a_C1_le_cs c hH) hC1p
    (fun x hxK hxN => y7a_NC1_cs c hH hF h71 hxN hxK)

theorem y7a_C6_le_cs (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    C6 c.e ≤ centralizerSection (AV1 c.e) (V1 c.e) := by
  have h := c.y7acfg hH
  intro x hx
  have hxX : x ∈ y7aX c := y7a_C6_le_X c hH hF hx
  refine ⟨?_, (Subgroup.mem_inf.mp hxX).2, ?_⟩
  · rw [Subgroup.mem_set_normalizer_iff]
    exact y7a_conj_AV h (Subgroup.mem_inf.mp hxX).1 (Subgroup.mem_inf.mp hxX).2
  · intro k hk
    have h1 : ⁅x, k⁆ ∈ V1 c.e := y7a_comm_C6_AV c hH hF x hx k hk
    have h2 : ⁅k, x⁆ = ⁅x, k⁆⁻¹ := (commutatorElement_inv (g₁ := x) (g₂ := k)).symm
    rw [h2]
    exact (V1 c.e).inv_mem h1

theorem y7a_sylow_C6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) (h73 : c.Fact73) :
    IsSylowIn 2 (centralizerSection (AV1 c.e) (V1 c.e)) (C6 c.e) := by
  have h := c.y7acfg hH
  have hC6le := y7a_C6_le_cs c hH hF
  refine ⟨hC6le, y7a_C6_isPGroup c, ?_⟩
  refine y6_sylow_of_self_normalizing hC6le (y7a_C6_isPGroup c) ?_
  intro x hxK hxN
  have hNM6 := y7a_NHA_le_normM6 c hH hF h71
  have hx' : x ∈ ((normIn c.s.H c.s.fr.A ⊔ M6 c.e : Subgroup G) : Set G) := by
    have := (h73 ▸ hxN : x ∈ normIn c.s.H c.s.fr.A ⊔ M6 c.e)
    exact this
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (normIn c.s.H c.s.fr.A) (M6 c.e) hNM6] at hx'
  obtain ⟨n, hn, m, hm, rfl⟩ := hx'
  have hmC6 : m ∈ C6 c.e := y7a_M6_le_C6 c hm
  have hmK : m ∈ centralizerSection (AV1 c.e) (V1 c.e) := hC6le hmC6
  have hnK : n ∈ centralizerSection (AV1 c.e) (V1 c.e) := by
    have hnm : n = (n * m) * m⁻¹ := by group
    rw [hnm]
    exact (centralizerSection (AV1 c.e) (V1 c.e)).mul_mem hxK
      ((centralizerSection (AV1 c.e) (V1 c.e)).inv_mem hmK)
  have hnNA : n ∈ normalizer (c.s.fr.A : Set G) := (Subgroup.mem_inf.mp hn).2
  have hc : ∀ a ∈ c.s.fr.A, ⁅a, n⁆ ∈ zpowers c.s.fr.z := by
    intro a ha
    have hV : ⁅a, n⁆ ∈ V1 c.e := hnK.2.2 a (Subgroup.mem_sup_left ha)
    have hA : ⁅a, n⁆ ∈ c.s.fr.A := by
      have h1 : n * a⁻¹ * n⁻¹ ∈ c.s.fr.A :=
        (Subgroup.mem_set_normalizer_iff.mp hnNA a⁻¹).mp (c.s.fr.A.inv_mem ha)
      have heq : ⁅a, n⁆ = a * (n * a⁻¹ * n⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [heq]
      exact c.s.fr.A.mul_mem ha h1
    rw [← y7a_A_inf_V h]
    exact Subgroup.mem_inf.mpr ⟨hA, hV⟩
  have hnC1 : n ∈ C1 c.e := y6_K_core c.toCtx5 hH (s5_NHA_le_Y c.toCtx5 hH hn) hc
  exact (C6 c.e).mul_mem (y7a_C1_le_C6 c hH hF hnC1) hmC6

theorem y7a_fact74 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) (h73 : c.Fact73) : c.Fact74 :=
  ⟨y7a_sylow_C1 c hH hF h71, y7a_sylow_C6 c hH hF h71 h73⟩

end CFSG.OddStandard.HigherRank.YamadaG23
