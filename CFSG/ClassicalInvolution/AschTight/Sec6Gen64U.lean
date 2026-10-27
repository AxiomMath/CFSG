module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64T

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

theorem v_pow_half : v ^ (Nat.card (Subgroup.zpowers u) / 2) = j ∧
    2 * (Nat.card (Subgroup.zpowers u) / 2) = Nat.card (Subgroup.zpowers u) := by
  have h4 := d.c.four_le_U
  have hU2 : 2 * (Nat.card (Subgroup.zpowers u) / 2) = Nat.card (Subgroup.zpowers u) := by
    have : 2 ∣ Nat.card (Subgroup.zpowers u) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers u) d.c.z_mem_U
      rwa [orderOf_eq_prime (by rw [pow_two]; exact d.c.hz.sq) d.c.hz.ne_one] at h
    omega
  refine ⟨?_, hU2⟩
  have hord : orderOf v = Nat.card (Subgroup.zpowers u) := by
    rw [← Nat.card_zpowers, d.c.natCard_U_eq_V]
  have hne : v ^ (Nat.card (Subgroup.zpowers u) / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hsq : v ^ (Nat.card (Subgroup.zpowers u) / 2) * v ^ (Nat.card (Subgroup.zpowers u) / 2)
      = 1 := by rw [← pow_add, ← two_mul, hU2, ← hord, pow_orderOf_eq_one]
  exact (d.c.hj.unique _ (Subgroup.pow_mem _ (d.c.hVJ (Subgroup.mem_zpowers v)) _)
    hsq).resolve_left hne

theorem natCard_UV : Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
    Nat.card (Subgroup.zpowers u) * Nat.card (Subgroup.zpowers u) := by
  have h2 := card_sup_mul_card_inf_of_le_normalizer (AscL62.le_normalizer_of_commutes d.c.hUV)
  rwa [d.c.U_inf_V, Subgroup.card_bot, mul_one, ← d.c.natCard_U_eq_V] at h2

theorem natCard_Ustar : Nat.card ↥(conjSub (r * t)⁻¹ (Subgroup.zpowers v)) =
    Nat.card (Subgroup.zpowers u) := by
  rw [AscL62.natCard_conjSub, ← d.c.natCard_U_eq_V]

theorem Ustar_mem_USet : conjSub (r * t)⁻¹ (Subgroup.zpowers v) ∈ USet Ω := by
  refine mem_USet_of_natCard d.Kstar_mem d.Rstar0_sylow
    (d.Ustar_le_Rstar d.Rstar0_sylow d.Rstar0_le_normalizer)
    (AscL62.isCyclic_conjSub _ inferInstance) ?_
  rw [d.natCard_Ustar, AscL62.natCard_conjSub, ← d.c.natCard_R_eq_T, d.c.natCard_R]

theorem Ustar_inf_V : conjSub (r * t)⁻¹ (Subgroup.zpowers v) ⊓ Subgroup.zpowers v = ⊥ := by
  have hP : Pair Ω (conjSub (r * t)⁻¹ J) J z j :=
    ⟨d.Kstar_mem, d.c.hJ, d.isUniqueInvolution_J', d.c.hj, d.c.z_ne_j⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  exact hP.eq_one_of_mem_of_mem (conjSub_mono d.c.hVJ hg.1) (d.c.hVJ hg.2)
    (AscL62.orderOf_eq_two_pow_of_isPGroup d.c.symm.U_isPGroup hg.2)

theorem UV_eq : Subgroup.zpowers u ⊔ Subgroup.zpowers v =
    conjSub (r * t)⁻¹ (Subgroup.zpowers v) ⊔ Subgroup.zpowers v := by
  have hle : conjSub (r * t)⁻¹ (Subgroup.zpowers v) ⊔ Subgroup.zpowers v ≤
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := sup_le d.Ustar_le_UV le_sup_right
  have hcomm : Commutes (conjSub (r * t)⁻¹ (Subgroup.zpowers v)) (Subgroup.zpowers v) :=
    fun a ha b hb => d.c.UV_comm a (d.Ustar_le_UV ha) b (Subgroup.mem_sup_right hb)
  have h2 := card_sup_mul_card_inf_of_le_normalizer (AscL62.le_normalizer_of_commutes hcomm)
  rw [d.Ustar_inf_V, Subgroup.card_bot, mul_one, d.natCard_Ustar, ← d.c.natCard_U_eq_V] at h2
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [d.natCard_UV, h2]

theorem mul_self_mem (hne : conjSub (r * t)⁻¹ J ≠ K) {w : G}
    (hw : w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) :
    w * w ∈ Subgroup.zpowers u ⊔ conjSub (r * t)⁻¹ (Subgroup.zpowers v) := by
  set A := Subgroup.zpowers u ⊔ conjSub (r * t)⁻¹ (Subgroup.zpowers v) with hA
  have hAUV : A ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := sup_le le_sup_left d.Ustar_le_UV
  have hcomm : Commutes (Subgroup.zpowers u) (conjSub (r * t)⁻¹ (Subgroup.zpowers v)) :=
    fun a ha b hb => d.c.UV_comm a (Subgroup.mem_sup_left ha) b (d.Ustar_le_UV hb)
  have hprod := card_sup_mul_card_inf_of_le_normalizer (AscL62.le_normalizer_of_commutes hcomm)
  have hinf : Nat.card ↥(Subgroup.zpowers u ⊓ conjSub (r * t)⁻¹ (Subgroup.zpowers v)) ≤ 2 :=
    card_le_two_of_le_inf d.c.hΩ d.c.hK d.Kstar_mem hne.symm (d.c.U_isPGroup.to_le inf_le_left)
      (inf_le_left.trans d.c.hUK) (inf_le_right.trans (conjSub_mono d.c.hVJ))
  rw [d.natCard_Ustar] at hprod
  have hA2 : Nat.card (Subgroup.zpowers u) * Nat.card (Subgroup.zpowers u) ≤ Nat.card A * 2 := by
    rw [← hprod]
    exact Nat.mul_le_mul_left _ hinf
  set H := A.subgroupOf (Subgroup.zpowers u ⊔ Subgroup.zpowers v) with hH
  have hHcard : Nat.card H = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAUV).toEquiv
  have hidx := H.index_mul_card
  rw [hHcard, d.natCard_UV] at hidx
  have hA0 : 0 < Nat.card A := Nat.card_pos
  have hle2 : H.index ≤ 2 := by
    by_contra h
    push Not at h
    have : 3 * Nat.card A ≤ H.index * Nat.card A := Nat.mul_le_mul_right _ h
    omega
  have hpos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    have : (⟨w * w, Subgroup.mul_mem _ hw hw⟩ : ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v)) ∈ H :=
      h1 ▸ Subgroup.mem_top _
    exact this
  · exact Subgroup.mul_self_mem_of_index_two h2 ⟨w, hw⟩

theorem v_sq_mem (hne : conjSub (r * t)⁻¹ J ≠ K) : v * v ∈ K ⊔ conjSub (r * t)⁻¹ J :=
  (sup_le_sup d.c.hUK (conjSub_mono d.c.hVJ))
    (d.mul_self_mem hne (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)))

theorem j_mem (hne : conjSub (r * t)⁻¹ J ≠ K) :
    j ∈ Subgroup.zpowers u ⊔ conjSub (r * t)⁻¹ (Subgroup.zpowers v) := by
  obtain ⟨hvj, -⟩ := d.v_pow_half
  obtain ⟨n, hn⟩ := d.c.U_isPGroup.exists_card_eq
  have h4 := d.c.four_le_U
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have he : Nat.card (Subgroup.zpowers u) / 2 = 2 ^ (n - 2) + 2 ^ (n - 2) := by
    rw [hn]
    have : 2 ^ n = 2 ^ (n - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  rw [he, pow_add] at hvj
  rw [← hvj]
  exact d.mul_self_mem hne (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers v) _))

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
