module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx48
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx44
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx45
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx47

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem zpowers_sup_Nh (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    zpowers h ⊔ Nh S h = (S ⊔ zpowers h) ⊓ normalizer (zpowers h : Set G) := by
  have hhN : zpowers h ≤ normalizer (zpowers h : Set G) :=
    Subgroup.zpowers_le.2 h_mem_normalizer_zpowers
  apply le_antisymm
  · exact sup_le (le_inf le_sup_right hhN)
      (le_inf (Nh_le_S.trans le_sup_left) (inf_le_right : Nh S h ≤ normalizer (zpowers h : Set G)))
  · intro n hn
    obtain ⟨s, hsS, i, rfl⟩ := hs.mem_N_decomp hn.1
    have hhi : h ^ i ∈ zpowers h := Subgroup.zpow_mem _ (Subgroup.mem_zpowers h) i
    have hsN : s ∈ normalizer (zpowers h : Set G) := by
      have : s = (s * h ^ i) * (h ^ i)⁻¹ := by group
      rw [this]
      exact mul_mem hn.2 (inv_mem (hhN hhi))
    exact mul_mem (Subgroup.mem_sup_right (mem_Nh.2 ⟨hsS, hsN⟩)) (Subgroup.mem_sup_left hhi)

end Setup8

theorem lemma_8_6 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h85 : Lemma8_5) (h29 : IV2_2_9_no_S3) : Lemma8_6 := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h hs hP8 hS7
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  obtain ⟨m, hm⟩ := hs.h_order
  obtain ⟨Y, hY⟩ := hs.exists_YData hII hq hrec hP8 hS7 h85
  obtain ⟨t₁, ht₁D, -, ht₁2, -, ht₁h⟩ := hs.exists_t hII hq hk hY
  obtain ⟨eY⟩ := hs.Y_equiv_SL34 hII hq hrec hk hY h29 ht₁D.1 ht₁2 ht₁h
  obtain ⟨t, htD, htW, ht2, htu, hth, htP⟩ := hs.exists_t_P hII hq hrec hk hY eY
  obtain ⟨w, hwD, hwW, hD₀, hw⟩ := hs.exists_w hII hq hrec hP8 hS7 hY htD htW
  have hDeq : Nh S h = zpowers t ⊔ zpowers w := hs.Nh_eq_sup hII htD htW hwD hD₀
  have hwh : w * h = h * w := hs.W_Nh_comm hII hwW hwD
  have hSeq : S = Y ⊔ Nh S h := hY.S_eq_sup
  have ht1 : t ≠ 1 := fun h' => htW (h' ▸ one_mem _)
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  refine ⟨Y, Nh S h, t, w, ?_, hSeq, ⟨hY.A_le, hY.Y_le_S.trans le_sup_left, hY.normedBy_N hs, ⟨eY⟩,
    hY.cent_h⟩, ⟨hDeq, hs.zpowers_sup_Nh, rfl⟩, ⟨htP, ?_, ?_, ?_⟩,
    ⟨(hs.Nh_inf_centralizer).trans hD₀, hwh⟩, ?_⟩
  ·
    apply le_antisymm
    · apply sup_le
      · exact hSeq.le.trans (sup_le_sup le_sup_left le_rfl)
      · exact le_sup_right.trans le_sup_left
    · exact sup_le (sup_le (hY.Y_le_S.trans le_sup_left) le_sup_right)
        (Nh_le_S.trans le_sup_left)
  · exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  · calc t⁻¹ * u * t = t * u * t⁻¹ := by rw [ht']
      _ = u * z := htu
  · calc t⁻¹ * h * t = t * h * t⁻¹ := by rw [ht']
      _ = h⁻¹ := hth
  · rcases hw with hw1 | ⟨hw1, hw2, -⟩
    · left
      refine ⟨hw1, ?_⟩
      have hDt : Nh S h = zpowers t := by
        rw [hDeq, hw1, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
      rw [hDt]
      exact Basic.exists_sigma3 hm ht2 hth
    · right
      have htw : t * w = w * t := hs.t_comm_w hII htD hwD hwW hD₀ hw1 hw2
      have hwt : w ≠ t := fun h' => htW (h' ▸ hwW)
      refine ⟨hs.w_inv_A hII hq hrec hk htD.1 ht2 htu hwW htw hwh hw1, ?_⟩
      rw [hDeq]
      exact Basic.exists_dihedral12 hm ht2 hw2 hth hwh htw hw1 hwt
        (fun x hx hxD => hs.S_inf_h hII (Nh_le_S (by rw [hDeq]; exact hxD)) hx)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
