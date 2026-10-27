module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4K0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6b_exists_k (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∃ k ∈ normIn L c.s.fr.F, k * (c.d * c.s.t) * k⁻¹ = c.d * c.s.t ∧
      ∀ f ∈ c.s.fr.F, f⁻¹ * (k * f * k⁻¹) ∈ c.s.fr.Z → f ∈ c.s.fr.Z := by
  obtain ⟨⟨h2a, h2b, h2c⟩, ⟨h3a, h3b, h3c, h3d, h3e, h3f⟩,
    ⟨h4a, h4b, h4c, h4d, h4e⟩, ⟨h5a, h5b, h5c, h5d, h5e, h5f⟩⟩ := hH.hLF.fact18
  rw [f3_zL_eq_bot hH, bot_sup_eq] at h5e
  obtain ⟨k, hk, hk3⟩ := exists_three_elt h5e
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk3
    norm_num at hk3
  have hkzL : k ∉ zL L := by
    rw [f3_zL_eq_bot hH]
    exact fun h => hk1 (Subgroup.mem_bot.mp h)
  have hpg : IsPGroup 3 ↥(zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk3]; norm_num)
  have hk3pow : k ^ 3 = 1 := by simpa [hk3] using pow_orderOf_eq_one k
  have htrans : ActsTransitively (zpowers k) c.s.fr.F (zpowers c.s.fr.z) :=
    (h5f k hk hpg hkzL).1
  have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s (lfactsA_of_setting hH.hS hH.hZ c.s)
  have hzc : ∀ f ∈ c.s.fr.F, f * c.s.fr.z = c.s.fr.z * f :=
    fun f hf => y54_F_comm hH f hf c.s.fr.z (y54_z_mem_F c.s)
  have hF8 : Nat.card ↥c.s.fr.F = 8 := by simpa using (y54_F_isE3 hH).2
  have hkz : k * c.s.fr.z * k⁻¹ = c.s.fr.z := by
    have hkA : k ∈ centEl L c.s.fr.z := by rw [← h2a]; exact hk.1
    have hcomm : k * c.s.fr.z = c.s.fr.z * k :=
      Subgroup.mem_centralizer_singleton_iff.mp hkA.2
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hkfpf := fpf_of_trans' (F := c.s.fr.F) hz2 hzc hF8 hk3pow hkz htrans
  have hcfg := c.y6cfg hH
  set u : G := c.d * c.s.t with hu_def
  have hu4 : orderOf u = 4 := by simpa [hu_def] using hcfg.u_ord
  have ht2 : orderOf c.s.t = 2 := hcfg.t_ord
  have htinv : c.s.t * u * c.s.t⁻¹ = u⁻¹ := by simpa [hu_def] using hcfg.t_inv
  have hC0 : C0 c.e = closure ({u, c.s.t} : Set G) := by simpa [hu_def] using hcfg.hC0
  have hkC0 : k ∈ normalizer (C0 c.e : Set G) := by
    have hkHA : k ∈ normIn c.s.H c.s.fr.A :=
      (inf_le_inf_right _ (s3_L_le_H c.s hH.hS)) hk.1
    exact hF.2.1.2.1 (Subgroup.mem_sup_left hkHA)
  have huC0 : u ∈ C0 c.e := by rw [hC0]; exact Subgroup.subset_closure (by simp)
  have hku_mem : k * u * k⁻¹ ∈ closure ({u, c.s.t} : Set G) := by
    rw [← hC0]
    exact (Subgroup.mem_set_normalizer_iff.mp hkC0 u).mp huC0
  have hku_ord : orderOf (k * u * k⁻¹) = 4 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu4]
  have hku : k * u * k⁻¹ = u := by
    rcases y6_d8_ord4 hu4 ht2 htinv (k * u * k⁻¹) hku_mem hku_ord with h | h
    · exact h
    · exfalso
      have hφu : MulAut.conj k u = u⁻¹ := by rw [MulAut.conj_apply]; exact h
      have hφ3 : (MulAut.conj k) ^ 3 = 1 := by rw [← map_pow, hk3pow, map_one]
      have h1 : ((MulAut.conj k) ^ 3) u = u⁻¹ := by
        have h2 : ((MulAut.conj k) ^ 2) u = u := by
          rw [pow_two, MulAut.mul_apply, hφu, map_inv, hφu, inv_inv]
        rw [pow_succ', MulAut.mul_apply, h2, hφu]
      have hu_eq_inv : u = u⁻¹ := by rw [← h1, hφ3, MulAut.one_apply]
      have hu2one : u ^ 2 = 1 := by
        rw [pow_two]
        exact (mul_eq_one_iff_eq_inv).mpr hu_eq_inv
      have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2one
      rw [hu4] at hdvd
      omega
  exact ⟨k, hk.2, by simpa [hu_def] using hku, hkfpf⟩

theorem y6b_a_normalizes_V1 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c.toCtx5) {a : G} (haX : a ∈ y6bX c.toCtx5)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) (haW : a ∉ y6bW c.toCtx5)
    (hconj : ∀ w ∈ M3 c.s, ∃ f ∈ c.s.fr.F, a * w * a⁻¹ = f * w) :
    a ∈ normalizer (V1 c.e : Set G) := by
  set u : G := c.d * c.s.t with hu_def
  have hcfg := c.y6cfg hH
  have hu2 : u ^ 2 = c.s.fr.z := by simpa [hu_def] using hcfg.u_sq
  have hV1 : V1 c.e = zpowers u := by rw [c.hV, ← hu_def]
  have huV1 : u ∈ V1 c.e := by rw [hV1]; exact Subgroup.mem_zpowers u
  have huM3 : u ∈ M3 c.s := (inf_le_right : V1 c.e ≤ M3 c.s) huV1
  obtain ⟨f, hfF, haf⟩ := hconj u huM3
  by_cases hfZ : f ∈ c.s.fr.Z
  · have hfU : f ∈ zpowers u := by
      have hle : zpowers (u ^ 2) ≤ zpowers u :=
        Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers u 2)
      apply hle
      rw [hu2]
      exact hfZ
    have hau : a * u * a⁻¹ ∈ zpowers u := by
      rw [haf]
      exact Subgroup.mul_mem _ hfU (Subgroup.mem_zpowers u)
    rw [hV1]
    exact mem_normalizer_zpowers_of_conj_mem hau
  · exfalso
    obtain ⟨k, hkF, hku, hkfpf⟩ := y6b_exists_k c hH hF
    have hku' : k * u * k⁻¹ = u := by simpa [hu_def] using hku
    have hy1W : a⁻¹ * (k * a * k⁻¹) ∈ y6bW c.toCtx5 :=
      y6b_equivar c.toCtx5 hH hF hRT h1 haX haF haW k hkF
    obtain ⟨e, heE, m, hmM3, hy1eq⟩ :=
      (y6b_mem_W c.toCtx5 hH hF hRT).mp hy1W
    have hm_comm : m * u = u * m := by
      haveI := y6e_M3_comm c.toCtx5 hF
      exact Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) hmM3 huM3
    have hmu : m * u * m⁻¹ = u := by rw [hm_comm, mul_assoc, mul_inv_cancel, mul_one]
    have hy1u : (a⁻¹ * (k * a * k⁻¹)) * u * (a⁻¹ * (k * a * k⁻¹))⁻¹ = e * u * e⁻¹ := by
      rw [hy1eq]
      calc e * m * u * (e * m)⁻¹ = e * (m * u * m⁻¹) * e⁻¹ := by group
        _ = e * u * e⁻¹ := by rw [hmu]
    have hwa : k * a * k⁻¹ = a * (a⁻¹ * (k * a * k⁻¹)) := by group
    have hleft : (k * a * k⁻¹) * u * (k * a * k⁻¹)⁻¹ = (k * f * k⁻¹) * u := by
      have hkinv_u : k⁻¹ * u * k = u := by
        calc k⁻¹ * u * k = k⁻¹ * (k * u * k⁻¹) * k := by rw [hku']
          _ = u := by group
      calc (k * a * k⁻¹) * u * (k * a * k⁻¹)⁻¹
          = k * (a * (k⁻¹ * u * k) * a⁻¹) * k⁻¹ := by group
        _ = k * (a * u * a⁻¹) * k⁻¹ := by rw [hkinv_u]
        _ = k * (f * u) * k⁻¹ := by rw [haf]
        _ = (k * f * k⁻¹) * (k * u * k⁻¹) := by group
        _ = (k * f * k⁻¹) * u := by rw [hku']
    have hright : (k * a * k⁻¹) * u * (k * a * k⁻¹)⁻¹ =
        a * (e * u * e⁻¹) * a⁻¹ := by
      calc (k * a * k⁻¹) * u * (k * a * k⁻¹)⁻¹
          = a * ((a⁻¹ * (k * a * k⁻¹)) * u *
              (a⁻¹ * (k * a * k⁻¹))⁻¹) * a⁻¹ := by
            rw [hwa]; group
        _ = a * (e * u * e⁻¹) * a⁻¹ := by rw [hy1u]
    have hkey : (k * f * k⁻¹) * u = a * (e * u * e⁻¹) * a⁻¹ := by
      rw [← hleft, hright]
    rcases y6b_conj_u_of_mem_E c hH hF hRT heE with heu | heu
    · have hkeyA : (k * f * k⁻¹) * u = f * u := by rw [hkey, heu, haf]
      have hkf : k * f * k⁻¹ = f := by
        have h := congrArg (· * u⁻¹) hkeyA
        simpa [mul_assoc] using h
      have hfk : f⁻¹ * (k * f * k⁻¹) ∈ c.s.fr.Z := by
        rw [hkf, inv_mul_cancel]
        exact (c.s.fr.Z).one_mem
      exact absurd (hkfpf f hfF hfk) hfZ
    · have hkeyB : (k * f * k⁻¹) * u = u⁻¹ * f⁻¹ := by
        rw [hkey, heu]
        calc a * u⁻¹ * a⁻¹ = (a * u * a⁻¹)⁻¹ := by group
          _ = (f * u)⁻¹ := by rw [haf]
          _ = u⁻¹ * f⁻¹ := by rw [mul_inv_rev]
      have hfu : u * f = f * u := (hcfg.u_cent f (s3_F_le_A c.s hfF)).symm
      have hfu_inv : u⁻¹ * f⁻¹ = f⁻¹ * u⁻¹ := by
        have h := congrArg Inv.inv hfu
        simpa [mul_inv_rev] using h.symm
      have hz_inv : c.s.fr.z⁻¹ = c.s.fr.z := by
        have hzz : c.s.fr.z * c.s.fr.z = 1 := by simpa [pow_two] using hcfg.rel.z_sq
        exact inv_eq_of_mul_eq_one_left hzz
      have huu : u⁻¹ * u⁻¹ = c.s.fr.z := by
        rw [← mul_inv_rev, ← pow_two, hu2, hz_inv]
      have hkf_eq : k * f * k⁻¹ = f⁻¹ * c.s.fr.z := by
        have h := congrArg (· * u⁻¹) hkeyB
        simp only [mul_assoc, mul_inv_cancel, mul_one] at h
        rw [show u⁻¹ * (f⁻¹ * u⁻¹) = f⁻¹ * c.s.fr.z by
          rw [← mul_assoc, hfu_inv, mul_assoc, huu]] at h
        simpa [mul_assoc] using h
      have hf2inv : f⁻¹ * f⁻¹ = 1 := by
        have h := y54_F_sq hH f hfF
        rw [← mul_inv_rev, ← pow_two, h, inv_one]
      have hfk : f⁻¹ * (k * f * k⁻¹) ∈ c.s.fr.Z := by
        rw [hkf_eq, ← mul_assoc, hf2inv, one_mul]
        exact Subgroup.mem_zpowers c.s.fr.z
      exact absurd (hkfpf f hfF hfk) hfZ

end CFSG.OddStandard.HigherRank.YamadaG23
