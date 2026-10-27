module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1C6a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Idx2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_M6_le_C6 (c : Ctx7 G L) : M6 c.e ≤ C6 c.e := inf_le_left

theorem y7a_C6_eq_M6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    Nat.card ↥(M6 c.e) * 2 = Nat.card ↥(C6 c.e) ∧ C6 c.e = M6 c.e ⊔ zpowers c.s.t := by
  have h := c.y7acfg hH
  have htC : c.s.t ∈ C6 c.e :=
    y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_right (y7a_t_mem_C0 h))
  have hCV : C6 c.e ≤ normalizer (V1 c.e : Set G) :=
    (y7a_C6_le_X c hH hF).trans inf_le_right
  have hCz : ∀ x ∈ C6 c.e, x * c.s.fr.z * x⁻¹ = c.s.fr.z := fun x hx =>
    y7a_fix_z h (Subgroup.mem_inf.mp (y7a_C6_le_X c hH hF hx)).1
  exact y7a_index_two h htC hCV hCz

theorem y7a_M6_normal (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ x ∈ y7aX c, ∀ m ∈ M6 c.e, x * m * x⁻¹ ∈ M6 c.e := by
  intro x hx m hm
  have hmC6 : m ∈ C6 c.e := (Subgroup.mem_inf.mp hm).1
  have hmc : ∀ w ∈ V1 c.e, w * m = m * w :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hm).2
  have hxV : ∀ w : G, w ∈ V1 c.e ↔ x * w * x⁻¹ ∈ V1 c.e :=
    Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hx).2
  refine Subgroup.mem_inf.mpr ⟨y7a_C6_normal c hH hF x hx m hmC6, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : x⁻¹ * v * x ∈ V1 c.e := by
    have hmem : x * (x⁻¹ * v * x) * x⁻¹ ∈ V1 c.e := by
      rw [show x * (x⁻¹ * v * x) * x⁻¹ = v by group]
      exact hv
    exact (hxV (x⁻¹ * v * x)).mpr hmem
  calc v * (x * m * x⁻¹) = x * ((x⁻¹ * v * x) * m) * x⁻¹ := by group
    _ = x * (m * (x⁻¹ * v * x)) * x⁻¹ := by rw [hmc (x⁻¹ * v * x) hv']
    _ = (x * m * x⁻¹) * v := by group

theorem y7a_AV1_le_M6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    AV1 c.e ≤ M6 c.e := by
  have h := c.y7acfg hH
  intro x hx
  have hx1 : x ∈ C1 c.e := y7a_AV_le_C1 h hx
  refine Subgroup.mem_inf.mpr ⟨y7a_C1_le_C6 c hH hF hx1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (((y7a_cent_C1_V h x hx1).2 hx) v hv).symm

theorem y7a_psi_C1 (c : Ctx7 G L) {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    ∀ x : ↥(y7aX c), (x : G) ∈ C1 c.e → ψ x = 1 := by
  intro x hx
  rw [← MonoidHom.mem_ker, hP.ker, Subgroup.mem_subgroupOf]
  exact hx

theorem y7a_psi_M6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    ∀ p ∈ P, ∃ m : ↥(y7aX c), (m : G) ∈ M6 c.e ∧ ψ m = p := by
  have h := c.y7acfg hH
  have htC1 : c.s.t ∈ C1 c.e := Subgroup.mem_sup_right (y7a_t_mem_C0 h)
  have htC6 : c.s.t ∈ C6 c.e := y7a_C1_le_C6 c hH hF htC1
  have hM6leX : M6 c.e ≤ y7aX c := (y7a_M6_le_C6 c).trans (y7a_C6_le_X c hH hF)
  have hzpX : zpowers c.s.t ≤ y7aX c :=
    Subgroup.zpowers_le.mpr ((y7a_C6_le_X c hH hF) htC6)
  have hsub : (C6 c.e).subgroupOf (y7aX c) =
      (M6 c.e).subgroupOf (y7aX c) ⊔ (zpowers c.s.t).subgroupOf (y7aX c) := by
    rw [(y7a_C6_eq_M6 c hH hF).2]
    exact Subgroup.subgroupOf_sup (B := y7aX c) hM6leX hzpX
  have hker : Subgroup.map ψ ((zpowers c.s.t).subgroupOf (y7aX c)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker]
    exact y7a_psi_C1 c hP y (Subgroup.zpowers_le.mpr htC1 (Subgroup.mem_subgroupOf.mp hy))
  have hmap : Subgroup.map ψ ((C6 c.e).subgroupOf (y7aX c)) =
      Subgroup.map ψ ((M6 c.e).subgroupOf (y7aX c)) := by
    rw [hsub, Subgroup.map_sup, hker, sup_bot_eq]
  have hPmap : P = Subgroup.map ψ ((C6 c.e).subgroupOf (y7aX c)) := by
    apply le_antisymm
    · intro p hp
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hP.P_le hp)
      exact Subgroup.mem_map.mpr ⟨x, (y7a_mem_C6_iff c hH hF hP x).mpr (hx.symm ▸ hp), hx⟩
    · intro p hp
      obtain ⟨x, hx, hψ⟩ := Subgroup.mem_map.mp hp
      rw [← hψ]
      exact (y7a_mem_C6_iff c hH hF hP x).mp (Subgroup.mem_subgroupOf.mp hx)
  intro p hp
  rw [hPmap, hmap] at hp
  obtain ⟨m, hm, hmp⟩ := Subgroup.mem_map.mp hp
  exact ⟨m, Subgroup.mem_subgroupOf.mp hm, hmp⟩

theorem y7a_M6_inf_Y (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    M6 c.e ⊓ y7aY c = AV1 c.e := by
  have h := c.y7acfg hH
  apply le_antisymm
  · intro x hx
    have hxM6 : x ∈ M6 c.e := hx.1
    have hxC6 : x ∈ C6 c.e := y7a_M6_le_C6 c hxM6
    have hxC1 : x ∈ C1 c.e := by
      have hx' : x ∈ C6 c.e ⊓ y7aY c := ⟨hxC6, hx.2⟩
      rwa [y7a_C6_inf_Y c hH hF hP] at hx'
    have hmc : ∀ v ∈ V1 c.e, x * v = v * x := by
      intro v hv
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxM6).2) v hv).symm
    exact (y7a_cent_C1_V h x hxC1).1 hmc
  · intro x hx
    exact ⟨y7a_AV1_le_M6 c hH hF hx, y6_C1_le_NAt (c.y7acfg hH).cfg (y7a_AV_le_C1 h hx)⟩

end CFSG.OddStandard.HigherRank.YamadaG23
