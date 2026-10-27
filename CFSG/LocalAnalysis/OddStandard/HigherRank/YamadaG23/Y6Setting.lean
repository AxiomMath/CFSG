module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54D
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53N
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6D8
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Cfg

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev y6X (c : Ctx6 G L) : Subgroup G :=
  normalizer (C1 c.e : Set G) ⊓ normalizer (V1 c.e : Set G)

abbrev y6K (c : Ctx6 G L) : Subgroup G :=
  CFSG.GH74.GLS.centralizerSection (C1 c.e) (V1 c.e)

abbrev y6Y (c : Ctx6 G L) : Subgroup G :=
  normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)

abbrev y6C (c : Ctx6 G L) : Subgroup G := y6X c ⊓ normalizer (C0 c.e : Set G)

theorem y6_C1_eq (c : Ctx6 G L) : C1 c.e = c.s.fr.A ⊔ C0 c.e := rfl

theorem Ctx6.y6cfg (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    Y6Cfg c.s.fr.A (C0 c.e) (V1 c.e) c.s.fr.a₁ c.s.fr.b₁ c.s.fr.a₂ c.s.fr.b₂ c.s.fr.z c.s.t
      (c.d * c.s.t) := by
  have hLF : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  have hz : orderOf c.s.fr.z = 2 := s3_z_order c.s hLF
  obtain ⟨hu4, hu2⟩ := Ctx5pre.u_facts c.toCtx5.toCtx5pre hz
  have hrel := s3_srel hH.hS hH.hZ c.s
  have ht2 : c.s.t * c.s.t = 1 := by
    have h := pow_orderOf_eq_one c.s.t
    rw [c.s.t_order] at h
    simpa [pow_two] using h
  have hd2 : c.d * c.d = 1 := by
    have h := pow_orderOf_eq_one c.d
    rw [c.d_order] at h
    simpa [pow_two] using h
  have hti : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
  have hdi : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right hd2
  refine
    { hA := rfl
      hC0 := ?_
      hV := c.hV
      rel := ⟨hrel.z_sq, hrel.a1_sq, rfl, hrel.a2_sq, hrel.b2_sq, hrel.comm1, hrel.comm2,
        hrel.a1a2, hrel.a1b2, hrel.b1a2, hrel.b1b2⟩
      z_ne := y54_z_ne_one (c := c.toCtx5) hH
      card_A := hLF.card_A
      t_ord := c.s.t_order
      u_ord := hu4
      u_sq := hu2
      t_inv := ?_
      t_cent := fun a ha => s3_comm_t_of_mem_A c.s ha
      u_cent := ?_ }
  · rw [c.intro5.gen]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · have hd : c.d = (c.d * c.s.t) * c.s.t⁻¹ := by group
        rw [hd]
        exact mul_mem (Subgroup.subset_closure (by simp))
          (inv_mem (Subgroup.subset_closure (by simp)))
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      · exact Subgroup.subset_closure (by simp)
  · have hmain : c.s.t * (c.d * c.s.t) * c.s.t = c.s.t * c.d := by
      calc c.s.t * (c.d * c.s.t) * c.s.t = c.s.t * c.d * (c.s.t * c.s.t) := by group
        _ = c.s.t * c.d := by rw [ht2, mul_one]
    rw [hti, mul_inv_rev, hti, hdi]
    exact hmain
  · intro a ha
    have hda : c.d * a = a * c.d := by
      have h := y5_d_cent_A c.toCtx5 a ha
      rw [hdi] at h
      calc c.d * a = (c.d * a * c.d) * c.d := by
            rw [mul_assoc (c.d * a) c.d c.d, hd2, mul_one]
        _ = a * c.d := by rw [h]
    have hta : a * c.s.t = c.s.t * a := s3_comm_t_of_mem_A c.s ha
    calc a * (c.d * c.s.t) = (a * c.d) * c.s.t := by group
      _ = (c.d * a) * c.s.t := by rw [hda]
      _ = c.d * (a * c.s.t) := by group
      _ = c.d * (c.s.t * a) := by rw [hta]
      _ = (c.d * c.s.t) * a := by group

theorem s6_d_comm_A (c : Ctx5 G L) {a : G} (ha : a ∈ c.s.fr.A) : a * c.d = c.d * a := by
  have hd2 : c.d * c.d = 1 := by
    have h := pow_orderOf_eq_one c.d
    rw [c.d_order] at h
    simpa [pow_two] using h
  have hdi : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right hd2
  have h := y5_d_cent_A c a ha
  rw [hdi] at h
  calc a * c.d = (c.d * a * c.d) * c.d := by rw [h]
    _ = c.d * a := by rw [mul_assoc (c.d * a) c.d c.d, hd2, mul_one]

theorem s6_Y_eq (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    y6Y c = normIn c.s.H c.s.fr.A ⊔ zpowers c.d :=
  y5_normN_Aqt (c := c.toCtx5) hH

theorem s6_Y_le_NA (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    y6Y c ≤ normalizer (c.s.fr.A : Set G) := by
  rw [s6_Y_eq c hH]
  refine sup_le inf_le_right ?_
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer (c.s.fr.A : Set G) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact s6_d_comm_A c.toCtx5 ha

theorem s6_Y_le_NC0 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    y6Y c ≤ normalizer (C0 c.e : Set G) := by
  rw [s6_Y_eq c hH]
  exact y5_normN_C0 (c := c.toCtx5) hH

theorem s6_NC0_le_NV (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    normalizer (C0 c.e : Set G) ≤ normalizer (V1 c.e : Set G) := by
  have cfg := c.y6cfg hH
  intro x hx
  have hx' : x ∈ normalizer ((closure ({c.d * c.s.t, c.s.t} : Set G) : Subgroup G) : Set G) := by
    rw [← cfg.hC0]
    exact hx
  have := y6_d8_norm cfg.u_ord cfg.t_ord cfg.t_inv x hx'
  rw [cfg.hV]
  exact this

theorem s6_Y_le_X (c : Ctx6 G L) (hH : F33Hyp c.s c.e) : y6Y c ≤ y6X c := by
  intro x hx
  have hxA := s6_Y_le_NA c hH hx
  have hxC0 := s6_Y_le_NC0 c hH hx
  exact ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hxA, hxC0⟩, s6_NC0_le_NV c hH hxC0⟩

theorem s6_NHA_le_Y (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    normIn c.s.H c.s.fr.A ≤ y6Y c := by
  rw [s6_Y_eq c hH]
  exact le_sup_left

theorem s6_d_mem_Y (c : Ctx6 G L) (hH : F33Hyp c.s c.e) : c.d ∈ y6Y c := by
  rw [s6_Y_eq c hH]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.d)

theorem s6_NLA_le_Y (c : Ctx6 G L) (hH : F33Hyp c.s c.e) : normIn L c.s.fr.A ≤ y6Y c :=
  le_trans (inf_le_inf_right _ (s3_L_le_H c.s hH.hS)) (s6_NHA_le_Y c hH)

theorem s6_T_le_NHA (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    c.s.T ≤ normIn c.s.H c.s.fr.A := by
  intro x hx
  refine ⟨c.s.sylow_T.1 hx, ?_⟩
  have hx1 : x ∈ c.e.T₁ := c.e.T_le hx
  have hx2 : x⁻¹ ∈ c.e.T₁ := inv_mem hx1
  show x ∈ normalizer (c.s.fr.A : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact s3_conj_A c.s c.e hH.h32 hx1 ha
  · intro ha
    have := s3_conj_A c.s c.e hH.h32 hx2 ha
    simpa [mul_assoc] using this

theorem s6_T_le_Y (c : Ctx6 G L) (hH : F33Hyp c.s c.e) : c.s.T ≤ y6Y c :=
  le_trans (s6_T_le_NHA c hH) (s6_NHA_le_Y c hH)

end CFSG.OddStandard.HigherRank.YamadaG23
