module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2SqA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2M6d
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2KSub
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2P3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_V1_le_M6' (c : Ctx7 G L) (hH : F33Hyp c.s c.e)
    (hF : c.toCtx5.Facts5) : V1 c.e ≤ M6 c.e :=
  le_sup_right.trans (y7a_AV1_le_M6 c hH hF)

private lemma y7a_M6_central_V1 (c : Ctx7 G L) :
    ∀ m ∈ M6 c.e, ∀ v ∈ V1 c.e, m * v = v * m := by
  intro m hm v hv
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hm).2 v hv).symm

private lemma y7a_M6_comm_mem_V1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e)
    (hF : c.toCtx5.Facts5) :
    ∀ x ∈ M6 c.e, ∀ y ∈ M6 c.e, ⁅x, y⁆ ∈ V1 c.e := by
  intro x hx y hy
  exact y7a_M6_comm_le_V1 c hH hF (Subgroup.commutator_mem_commutator hx hy)

private lemma y7a_V_sq_one (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ v ∈ V, v ^ 2 = 1 := by
  intro v hv
  rcases y7a_V_elems h v hv with rfl | rfl | rfl | rfl
  · simp
  · simpa [pow_two] using y7a_z_sq h
  · simpa [pow_two] using y7a_d_sq h
  · have hdz : d * z = z * d := (y7a_d_cent h z (y7a_z_mem_A h)).symm
    rw [pow_two]
    calc (z * d) * (z * d) = z * (d * z) * d := by group
      _ = z * (z * d) * d := by rw [hdz]
      _ = z * z * (d * d) := by group
      _ = 1 := by simp [y7a_z_sq h, y7a_d_sq h]

theorem y7a_M6_sq_mem_V1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : ∀ m ∈ M6 c.e, m ^ 2 ∈ V1 c.e := by
  have h := c.y7acfg hH
  have hLFA := lfactsA_of_setting hH.hS hH.hZ c.s
  obtain ⟨K, hKM, hK⟩ := y7a_sq_subgroup (y7a_V1_le_M6' c hH hF)
    (y7a_M6_central_V1 c) (y7a_M6_comm_mem_V1 c hH hF)
  have hAV : AV1 c.e ≤ K := by
    intro x hx
    rw [hK]
    obtain ⟨a, ha, v, hv, rfl⟩ := y7a_AV_elems h x hx
    have hmem : a * v ∈ c.s.fr.A ⊔ V1 c.e :=
      (c.s.fr.A ⊔ V1 c.e).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hv)
    refine ⟨y7a_AV1_le_M6 c hH hF hmem, ?_⟩
    have hav : a * v = v * a := y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
    have hsq : (a * v) ^ 2 = a ^ 2 * v ^ 2 := by
      rw [pow_two]
      calc (a * v) * (a * v) = a * (v * a) * v := by group
        _ = a * (a * v) * v := by rw [← hav]
        _ = a * a * (v * v) := by group
        _ = a ^ 2 * v ^ 2 := by rw [pow_two, pow_two]
    rw [hsq, y7a_V_sq_one h v hv, mul_one]
    exact Subgroup.zpowers_le.mpr (y7a_z_mem_V h) (hLFA.sq_A a ha)
  have hM3 : M3 c.s ≤ K := by
    intro m hm
    rw [hK]
    exact ⟨h71.2.2.2.1 hm,
      by rw [(y7a_M3_elemAbelian c hH).2 m hm]; exact (V1 c.e).one_mem⟩
  have hKX : ∀ x ∈ y7aX c, ∀ m ∈ K, x * m * x⁻¹ ∈ K := by
    intro x hx m hm
    rw [hK] at hm ⊢
    refine ⟨y7a_M6_normal c hH hF x hx m hm.1, ?_⟩
    have hxN : x ∈ normalizer (V1 c.e : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxV : x * m ^ 2 * x⁻¹ ∈ V1 c.e :=
      (Subgroup.mem_normalizer_iff.mp hxN (m ^ 2)).mp hm.2
    have hsq2 : (x * m * x⁻¹) ^ 2 = x * m ^ 2 * x⁻¹ := by
      simp only [pow_two]
      group
    rwa [hsq2]
  obtain ⟨D, hVD, hDA, hDinv, hFD, hD⟩ := y7a_exists_D c hH hF hKM hKX hAV hM3
  have hbF : c.s.fr.b₁ * c.s.fr.b₂ ∈ c.s.fr.F := Subgroup.subset_closure (by simp)
  have hAD : c.s.fr.A ≤ D := y7a_A_le_of_b1b2 c hH hVD hDA hDinv (hFD hbF)
  intro m hm
  exact ((hK m).mp (hD hAD hm)).2

theorem y7a_fact72_3 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) :
    ⁅M6 c.e, M6 c.e⁆ = V1 c.e ∧
      SecProp (M6 c.e) (V1 c.e) (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y)) := by
  refine ⟨y7a_M6_comm_eq_V1 c hH hF h71, ?_⟩
  have hVn : ∀ m ∈ M6 c.e, ∀ v ∈ V1 c.e, m * v * m⁻¹ ∈ V1 c.e := by
    intro m hm v hv
    simpa [y7a_M6_central_V1 c m hm v hv] using hv
  exact y7a_secProp_of_sq (y7a_V1_le_M6' c hH hF) hVn (y7a_M6_comm_mem_V1 c hH hF)
    (y7a_M6_sq_mem_V1 c hH hF h71)

end CFSG.OddStandard.HigherRank.YamadaG23
