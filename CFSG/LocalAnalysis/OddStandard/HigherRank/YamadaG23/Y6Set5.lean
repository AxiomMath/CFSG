module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Setting
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Char

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem Ctx5.y6cfg5 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    Y6Cfg c.s.fr.A (C0 c.e) (zpowers (c.d * c.s.t)) c.s.fr.a₁ c.s.fr.b₁ c.s.fr.a₂ c.s.fr.b₂
      c.s.fr.z c.s.t (c.d * c.s.t) := by
  have hLF : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  have hz : orderOf c.s.fr.z = 2 := s3_z_order c.s hLF
  obtain ⟨hu4, hu2⟩ := Ctx5pre.u_facts c.toCtx5pre hz
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
      hV := rfl
      rel := ⟨hrel.z_sq, hrel.a1_sq, rfl, hrel.a2_sq, hrel.b2_sq, hrel.comm1, hrel.comm2,
        hrel.a1a2, hrel.a1b2, hrel.b1a2, hrel.b1b2⟩
      z_ne := y54_z_ne_one (c := c) hH
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
    have hda : c.d * a = a * c.d := (s6_d_comm_A c ha).symm
    have hta : a * c.s.t = c.s.t * a := s3_comm_t_of_mem_A c.s ha
    calc a * (c.d * c.s.t) = (a * c.d) * c.s.t := by group
      _ = (c.d * a) * c.s.t := by rw [hda]
      _ = c.d * (a * c.s.t) := by group
      _ = c.d * (c.s.t * a) := by rw [hta]
      _ = (c.d * c.s.t) * a := by group

theorem s5_T_le_NHA {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.T ≤ normIn s.H s.fr.A := by
  intro x hx
  refine ⟨s.sylow_T.1 hx, ?_⟩
  have hx1 : x ∈ e.T₁ := e.T_le hx
  have hx2 : x⁻¹ ∈ e.T₁ := inv_mem hx1
  show x ∈ normalizer (s.fr.A : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact s3_conj_A s e hH.h32 hx1 ha
  · intro ha
    have := s3_conj_A s e hH.h32 hx2 ha
    simpa [mul_assoc] using this

theorem s5_Y_eq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) =
      normIn c.s.H c.s.fr.A ⊔ zpowers c.d :=
  y5_normN_Aqt (c := c) hH

theorem s5_Y_le_NA (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) ≤
      normalizer (c.s.fr.A : Set G) := by
  rw [s5_Y_eq c hH]
  refine sup_le inf_le_right ?_
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer (c.s.fr.A : Set G) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact s6_d_comm_A c ha

theorem s5_Y_le_NC0 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) ≤
      normalizer (C0 c.e : Set G) := by
  rw [s5_Y_eq c hH]
  exact y5_normN_C0 (c := c) hH

theorem s5_NHA_le_Y (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normIn c.s.H c.s.fr.A ≤ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
  rw [s5_Y_eq c hH]
  exact le_sup_left

theorem s5_d_mem_Y (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.d ∈ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
  rw [s5_Y_eq c hH]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.d)

theorem s5_NLA_le_Y (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normIn L c.s.fr.A ≤ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
  le_trans (inf_le_inf_right _ (s3_L_le_H c.s hH.hS)) (s5_NHA_le_Y c hH)

theorem s5_T_le_Y (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.T ≤ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
  le_trans (s5_T_le_NHA hH) (s5_NHA_le_Y c hH)

theorem s5_Y_le_NC1 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) ≤
      normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) :=
  fun _ hx => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨s5_Y_le_NA c hH hx,
    s5_Y_le_NC0 c hH hx⟩

theorem s5_Y_le_NU (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) ≤
      normalizer ((zpowers (c.d * c.s.t) : Subgroup G) : Set G) := by
  have cfg := c.y6cfg5 hH
  intro x hx
  have hx' : x ∈ normalizer ((closure ({c.d * c.s.t, c.s.t} : Set G) : Subgroup G) : Set G) := by
    rw [← cfg.hC0]
    exact s5_Y_le_NC0 c hH hx
  exact y6_d8_norm cfg.u_ord cfg.t_ord cfg.t_inv x hx'

theorem s5_hY_conj (c : Ctx5 G L) (hH : F33Hyp c.s c.e) {y : G}
    (hy : y ∈ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)) :
    y * c.s.t * y⁻¹ = c.s.t ∨ y * c.s.t * y⁻¹ = c.s.fr.z * c.s.t :=
  (y6_mem_NAt_iff (c.y6cfg5 hH) (s5_Y_le_NC1 c hH hy) (s5_Y_le_NU c hH hy)).mp hy

end CFSG.OddStandard.HigherRank.YamadaG23
