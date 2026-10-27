module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFJrS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem s3_zt_conj_mem (hS : HRSetting G L) (h31 : s.Fact31) (hA : LFactsA s)
    (e : Setting3.Ext s) {g : G} (hg : g ∈ e.T₁) {w : G} (hw : w ∈ zt s) :
    g * w * g⁻¹ ∈ zt s := by
  rw [s3_mem_zt_iff s hA] at hw ⊢
  rcases hw with rfl | rfl | rfl | rfl
  · simp
  · rw [s3_T1_comm_z s hS hA h31 e hg]
    exact Or.inr (Or.inl rfl)
  · rcases em (g ∈ s.T) with hgT | hgT
    · right; right; left
      calc g * s.t * g⁻¹ = s.t * g * g⁻¹ := by rw [s3_comm_t_of_mem_T s hgT]
        _ = s.t := by group
    · right; right; right
      exact s3_T1_conj_t s hA h31 e hg hgT
  · rcases em (g ∈ s.T) with hgT | hgT
    · right; right; right
      rw [show g * (s.fr.z * s.t) * g⁻¹ =
          (g * s.fr.z * g⁻¹) * (g * s.t * g⁻¹) from by group,
        s3_T1_comm_z s hS hA h31 e hg, s3_comm_t_of_mem_T s hgT]
      group
    · right; right; left
      rw [show g * (s.fr.z * s.t) * g⁻¹ =
          (g * s.fr.z * g⁻¹) * (g * s.t * g⁻¹) from by group,
        s3_T1_comm_z s hS hA h31 e hg, s3_T1_conj_t s hA h31 e hg hgT]
      have hzz : s.fr.z * s.fr.z = 1 := by
        rw [← pow_two, ← s3_z_order s hA]
        exact pow_orderOf_eq_one s.fr.z
      rw [← mul_assoc, hzz, one_mul]

theorem s3_AT_conj (hS : HRSetting G L) (hOut : (innerAut (L ⧸ center L)).index = 2)
    (h31 : s.Fact31) (hA : LFactsA s) (e : Setting3.Ext s) (hRT : s.R ≠ s.T) {x : G}
    (hx : x ∈ e.T₁) {y : G} (hy : y ∈ s.fr.A ⊔ zpowers s.t) :
    x * y * x⁻¹ ∈ s.fr.A ⊔ zpowers s.t := by
  obtain ⟨hPnorm, hjr⟩ := s3_jr_section s hS hOut h31 hA hRT
  let N : Subgroup ↥s.T := (zt s).subgroupOf s.T
  haveI : N.Normal := hPnorm
  have hjr' : thompsonRank (⊤ : Subgroup (↥s.T ⧸ N)) =
      ((s.fr.A ⊔ zpowers s.t).subgroupOf s.T).map (QuotientGroup.mk' N) := hjr
  have hnormT : e.T₁ ≤ Subgroup.normalizer (s.T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer e.T_le).mp (s3_T_normal_T1 s hA h31 e)
  have hmapT : s.T.map (MulAut.conj x) = s.T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormT hx)
  let c : ↥s.T ≃* ↥s.T :=
    (MulEquiv.subgroupMap (MulAut.conj x) s.T).trans (MulEquiv.subgroupCongr hmapT)
  have hc : ∀ w : ↥s.T, (c w : G) = x * (w : G) * x⁻¹ := by
    intro w
    rfl
  have hxinv : x⁻¹ ∈ e.T₁ := Subgroup.inv_mem _ hx
  have hmemP : ∀ w : ↥s.T, (w : G) ∈ zt s ↔ (c w : G) ∈ zt s := by
    intro w
    constructor
    · intro hw
      have h := s3_zt_conj_mem s hS h31 hA e hx hw
      rw [← hc w] at h
      exact h
    · intro hw
      have h := s3_zt_conj_mem s hS h31 hA e hxinv hw
      have h2 : x⁻¹ * (c w : G) * x = (w : G) := by rw [hc w]; group
      rw [inv_inv, h2] at h
      exact h
  have hmapP : N.map c = N := by
    apply le_antisymm
    · intro u hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [Subgroup.mem_subgroupOf] at hv ⊢
      exact (hmemP v).mp hv
    · intro u hu
      rw [Subgroup.mem_map]
      refine ⟨c.symm u, ?_, c.apply_symm_apply u⟩
      rw [Subgroup.mem_subgroupOf]
      exact (hmemP (c.symm u)).mpr (by
        rw [MulEquiv.apply_symm_apply]
        exact Subgroup.mem_subgroupOf.mp hu)
  let cbar : (↥s.T ⧸ N) ≃* (↥s.T ⧸ N) := QuotientGroup.congr N N c hmapP
  have hyT : y ∈ s.T :=
    (sup_le (s3_A_le_T s) (Subgroup.zpowers_le.mpr (s3_t_mem_T s))) hy
  have hTa : x * y * x⁻¹ ∈ s.T :=
    Subgroup.mem_subgroupOf.mp
      ((s3_T_normal_T1 s hA h31 e).conj_mem ⟨y, e.T_le hyT⟩
        (Subgroup.mem_subgroupOf.mpr hyT) ⟨x, hx⟩)
  let a : ↥s.T := ⟨x * y * x⁻¹, hTa⟩
  have hca : c ⟨y, hyT⟩ = a := Subtype.ext (hc ⟨y, hyT⟩)
  have hq : QuotientGroup.mk' N ⟨y, hyT⟩ ∈ thompsonRank (⊤ : Subgroup (↥s.T ⧸ N)) := by
    rw [hjr']
    exact Subgroup.mem_map.mpr ⟨⟨y, hyT⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hcq : cbar (QuotientGroup.mk' N ⟨y, hyT⟩) ∈
      thompsonRank (⊤ : Subgroup (↥s.T ⧸ N)) := by
    have hmap := thompsonRank_top_map_equiv cbar
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨_, hq, rfl⟩
  rw [hjr'] at hcq
  obtain ⟨w, hw, hwq⟩ := Subgroup.mem_map.mp hcq
  have hcbar_a : cbar (QuotientGroup.mk' N ⟨y, hyT⟩) = QuotientGroup.mk' N a := by
    dsimp only [cbar]
    rw [QuotientGroup.congr_mk', hca]
  have hπeq : QuotientGroup.mk' N w = QuotientGroup.mk' N a := hwq.trans hcbar_a
  have hwN : w * a⁻¹ ∈ N := by
    have h1 : QuotientGroup.mk' N (w * a⁻¹) = 1 := by
      rw [map_mul, map_inv, hπeq]
      simp
    exact (QuotientGroup.eq_one_iff _).mp (by simpa using h1)
  have hztleJ : zt s ≤ s.fr.A ⊔ zpowers s.t := by
    rw [zt, Subgroup.closure_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact Subgroup.mem_sup_left (s3_z_mem_A s)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t)
  have hJsub : N ≤ (s.fr.A ⊔ zpowers s.t).subgroupOf s.T := by
    intro u hu
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    exact hztleJ hu
  have huJ : (w * a⁻¹)⁻¹ * w ∈ (s.fr.A ⊔ zpowers s.t).subgroupOf s.T :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hJsub hwN)) hw
  have hua : (((w * a⁻¹)⁻¹ * w : ↥s.T) : G) = x * y * x⁻¹ := by
    have h1 : ((w * a⁻¹)⁻¹ * w : ↥s.T) = a := by group
    rw [h1]
  rw [← hua]
  exact Subgroup.mem_subgroupOf.mp huJ

end CFSG.OddStandard.HigherRank.YamadaG23
