module

public import CFSG.ClassicalInvolution.Asc77.AscT7RA
public import CFSG.ClassicalInvolution.Asc77.AscT7BAlpha
public import CFSG.ClassicalInvolution.Asc77.AscT7FF

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.exists_good_frame (h : Hyp21 p f Ω K K' z u J t W) :
    ∃ u' : G, TwinFrameData Ω K K' z u' J t ∧ Thompson.GoodElt Ω W u' ∧
      Thompson.GoodElt Ω W z ∧ Thompson.GoodElt Ω W t := by
  have hst := h.std.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst h.hW
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  obtain ⟨ρK, hρK⟩ := c.exists_rep_of_involution_mem hst.mem hz h.hzW
  obtain ⟨ρK', hρK'⟩ := c.exists_rep_of_involution_mem hK'Ω hzK' h.hzW
  obtain ⟨ρJ, hρJ⟩ := c.exists_rep_of_involution_mem h.hJ.1 h.ht h.htW
  have hzρ : IsUniqueInvolution ρK.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρK'.K z := by rw [hρK']; exact hzK'
  have htρ : IsUniqueInvolution ρJ.K t := by rw [hρJ]; exact h.ht
  obtain ⟨w, hwRW, hwz, hw4⟩ := c.exists_mul_self_eq ρK hzρ
  obtain ⟨w', hw'RW, hw'z, hw'4⟩ := c.exists_mul_self_eq ρK' hzρ'
  have hwK : w ∈ K := by
    have := ρK.hRK.1 hwRW.1
    rwa [hρK] at this
  have hw'K' : w' ∈ K' := by
    have := ρK'.hRK.1 hw'RW.1
    rwa [hρK'] at this
  have hwW : w ∈ W := hwRW.2
  have hw'W : w' ∈ W := hw'RW.2
  have hno4 : ∀ x ∈ K ⊓ K', orderOf x ≠ 4 := by
    intro x hx hx4
    have hcard : Nat.card ↥(Subgroup.zpowers x) = 2 ^ 2 := by
      rw [Nat.card_zpowers, hx4]
      norm_num
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers x) := IsPGroup.of_card hcard
    have := hΩ.card_le_two_of_le_inf hst.mem hK'Ω h.std.hne.symm h2
      (Subgroup.zpowers_le.mpr hx.1) (Subgroup.zpowers_le.mpr hx.2)
    rw [hcard] at this
    omega
  have hcomm : w * w' = w' * w := c.comm_W w hwW w' hw'W
  have hw'w : w' ≠ w := fun heq => hno4 w ⟨hwK, heq ▸ hw'K'⟩ hw4
  have hu2 : (w * w') * (w * w') = 1 := by
    calc (w * w') * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [← hcomm]
      _ = (w * w) * (w' * w') := by group
      _ = 1 := by rw [hwz, hw'z, hz.sq]
  have hu1 : w * w' ≠ 1 := by
    intro h1
    have h2 : w = w'⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hno4 w ⟨hwK, h2 ▸ K'.inv_mem hw'K'⟩ hw4
  have huz : w * w' ≠ z := by
    intro h1
    apply hw'w
    have h2 : w * w' = w * w := by rw [h1, hwz]
    exact mul_left_cancel h2
  have hfr : TwinFrameData Ω K K' z (w * w') J t :=
    { mem := hst.mem
      hz := hz
      hK' := h.std.hK'
      hne := h.std.hne
      hu := Subgroup.mul_mem_sup hwK hw'K'
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := h.hJ
      ht := h.ht
      htu := c.comm_W t h.htW (w * w') (W.mul_mem hwW hw'W) }
  have hgw : Thompson.GoodElt Ω W w :=
    c.good_of_mem_inf ρK ⟨ρK.hRK.1 hwRW.1, hwW⟩
  have hgw' : Thompson.GoodElt Ω W w' :=
    c.good_of_mem_inf ρK' ⟨ρK'.hRK.1 hw'RW.1, hw'W⟩
  have hzin := c.mem_inf_W_of_isUniqueInvolution ρK hzρ
  have htin := c.mem_inf_W_of_isUniqueInvolution ρJ htρ
  exact ⟨w * w', hfr, c.good_mul hgw hgw', c.good_of_mem_inf ρK ⟨ρK.hRK.1 hzin.1, hzin.2⟩,
    c.good_of_mem_inf ρJ ⟨ρJ.hRK.1 htin.1, htin.2⟩⟩

theorem c21_13_M_ne_of_c21_3 (hC3 : C21_3 p f) : C21_13_M_ne p f := by
  intro G _ _ _ Ω K K' z u J t W h _
  have hst := h.std.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst h.hW
  obtain ⟨u', hfr, hgu, hgz, hgt⟩ := h.exists_good_frame
  have h' : Hyp21 p f Ω K K' z u' J t W := Hyp21.of_twinFrameData h.std hfr h.hW h.hzW h.htW
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hp hΩ
  have hA0 : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.ht.sq h.std.hz.sq h.ht.ne_one h.std.hz.ne_one
      h.twinFrameData.t_ne_z hzt.symm
  have hA0B : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hA0B' : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, u', t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hα := (hC3 G Ω K K' z u J t W h).2 _ hA0B hA0
  have hα' := (hC3 G Ω K K' z u' J t W h').2
  have hA0W : Subgroup.closure ({t, z} : Set G) ≤ W := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h.htW
    · exact h.hzW
  refine iSup₂_le fun R hR => ?_
  obtain ⟨K₁, hK₁, hRK₁⟩ := exists_isSylow2In_of_mem_RSet hR.1
  intro n hn
  by_cases hnW : n ∈ W
  · have hcent : n ∈ Subgroup.centralizer ((Subgroup.closure ({t, z} : Set G) : Subgroup G) :
        Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact c.comm_W x (hA0W hx) n hnW
    have := T7B.centralizer_le_normalizer_alphaOf _ hcent
    rwa [hα] at this
  · let ρ : Thompson.Rep Ω W := ⟨K₁, R, n, hK₁, hR, hRK₁, hn, hnW⟩
    obtain ⟨A, hAB, hA4, hAc⟩ := c.exists_fourGroup_centralized ρ hgz hgu hgt h.std.hz.sq hfr.hu2
      h.ht.sq h.std.hz.ne_one hfr.hu1 hfr.huz.symm (hfr.t_not_mem_closure hp hq hΩ)
    have hcent : n ∈ Subgroup.centralizer ((A : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hAc x hx).symm
    have h1 := T7B.centralizer_le_normalizer_alphaOf A hcent
    have h2 : alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
      rw [hα' A hAB hA4, ← hα' _ hA0B' hA0, hα]
    rwa [h2] at h1

end Frame

end CFSG.ClassicalInvolution.Asc77
