module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf7Ident
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscAlpha
public import CFSG.ClassicalInvolution.Q3.Q3T7W21B02
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mu

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc


section Frame

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {K K' J W : Subgroup Y}
  {z u t : Y}

theorem exists_good_frame (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W) :
    ∃ u' : Y, TwinFrameData Ω K K' z u' J t ∧ Thompson.GoodElt Ω W u' ∧
      Thompson.GoodElt Ω W z ∧ Thompson.GoodElt Ω W t := by
  have hf := d.frame
  have hΩ : HypOmegaGen Ω := hP.hyp
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP d.hW
  have hz : IsUniqueInvolution K z := hf.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hf.hK'
  have hK'Ω : K' ∈ Ω := hf.hK'.1
  obtain ⟨ρK, hρK⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hf.mem hz d.hzW
  obtain ⟨ρK', hρK'⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hK'Ω hzK' d.hzW
  obtain ⟨ρJ, hρJ⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hf.hJ.1 hf.ht d.htW
  have hzρ : IsUniqueInvolution ρK.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρK'.K z := by rw [hρK']; exact hzK'
  have htρ : IsUniqueInvolution ρJ.K t := by rw [hρJ]; exact hf.ht
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
    have := Sec6Gen.card_le_two_of_le_inf hΩ hf.mem hK'Ω hf.hne.symm h2
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
    { mem := hf.mem
      hz := hz
      hK' := hf.hK'
      hne := hf.hne
      hu := Subgroup.mul_mem_sup hwK hw'K'
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := hf.hJ
      ht := hf.ht
      htu := c.comm_W t d.htW (w * w') (W.mul_mem hwW hw'W) }
  have hgw : Thompson.GoodElt Ω W w := c.good_of_mem_inf ρK ⟨ρK.hRK.1 hwRW.1, hwW⟩
  have hgw' : Thompson.GoodElt Ω W w' := c.good_of_mem_inf ρK' ⟨ρK'.hRK.1 hw'RW.1, hw'W⟩
  have hzin := c.mem_inf_W_of_isUniqueInvolution ρK hzρ
  have htin := c.mem_inf_W_of_isUniqueInvolution ρJ htρ
  exact ⟨w * w', hfr, c.good_mul hgw hgw', c.good_of_mem_inf ρK ⟨ρK.hRK.1 hzin.1, hzin.2⟩,
    c.good_of_mem_inf ρJ ⟨ρJ.hRK.1 htin.1, htin.2⟩⟩

theorem comm_zt (hΩ : HypOmegaGen Ω) (hf : TwinFrameData Ω K K' z u J t) : z * t = t * z := by
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, -, -, -, -, hRT, -⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hf.mem hf.hz hf.hK' hf.hne hf.hJ
  have h8R : 8 ≤ Nat.card R₀ := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hf.mem hR₀)
  have h8T : 8 ≤ Nat.card T₀ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hf.hJ.1 hT₀)
  have hzR : z ∈ R₀ := mem_of_isUniqueInvolution_of_isPGroup hf.hz hR₀.1 hR₀.2.1 (by omega)
  have htT : t ∈ T₀ := mem_of_isUniqueInvolution_of_isPGroup hf.ht hT₀.1 hT₀.2.1 (by omega)
  exact hRT z hzR t htT

theorem mGrp_le_normalizer_alpha (hP : Q3CL.PartIHypG Ω) (hs : AlphaSteps Ω)
    (d : Data Ω K K' z u J t W) :
    MGrp Ω W ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := by
  have hf := d.frame
  have hΩ : HypOmegaGen Ω := hP.hyp
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP d.hW
  obtain ⟨u', hfr, hgu, hgz, hgt⟩ := exists_good_frame hP d
  have hzt : z * t = t * z := comm_zt hΩ hf
  have hA0 : IsElemAbelian2 (Subgroup.closure ({t, z} : Set Y)) 2 :=
    T7A.isElemAbelian2_closure_pair hf.ht.sq hf.hz.sq hf.ht.ne_one hf.hz.ne_one
      hf.t_ne_z hzt.symm
  have hA0B : Subgroup.closure ({t, z} : Set Y) ≤ Subgroup.closure ({z, u, t} : Set Y) := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hA0B' : Subgroup.closure ({t, z} : Set Y) ≤ Subgroup.closure ({z, u', t} : Set Y) := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hα := (hs.alpha_eq hf).2 _ hA0B hA0
  have hα' := (hs.alpha_eq hfr).2
  have hA0W : Subgroup.closure ({t, z} : Set Y) ≤ W := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact d.htW
    · exact d.hzW
  refine iSup₂_le fun R hR => ?_
  obtain ⟨K₁, hK₁, hRK₁⟩ := exists_isSylow2In_of_mem_RSet hR.1
  intro n hn
  by_cases hnW : n ∈ W
  · have hcent : n ∈ Subgroup.centralizer ((Subgroup.closure ({t, z} : Set Y) : Subgroup Y) :
        Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact c.comm_W x (hA0W hx) n hnW
    have := centralizer_le_normalizer_alphaOf _ hcent
    rwa [hα] at this
  · let ρ : Thompson.Rep Ω W := ⟨K₁, R, n, hK₁, hR, hRK₁, hn, hnW⟩
    obtain ⟨A, hAB, hA4, hAc⟩ := c.exists_fourGroup_centralized ρ hgz hgu hgt hf.hz.sq hfr.hu2
      hf.ht.sq hf.hz.ne_one hfr.hu1 hfr.huz.symm
      (Hat2A7S.twinFrame_t_not_mem_closure hΩ hfr)
    have hcent : n ∈ Subgroup.centralizer ((A : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hAc x hx).symm
    have h1 := centralizer_le_normalizer_alphaOf A hcent
    have h2 : alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set Y)) := by
      rw [hα' A hAB hA4, ← hα' _ hA0B' hA0, hα]
    rwa [h2] at h1

end Frame

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
