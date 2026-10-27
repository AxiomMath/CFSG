module

public import CFSG.CGT.PushingUpLit.BHS7.BlockJ
public import CFSG.CGT.PushingUpLit.BHS7.ClaimA
public import CFSG.CGT.PushingUpLit.BHS7.SevenEight

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem exists_subnormal_block_of_le (h : MinCex G T) {E L : Subgroup Γ} (hE : IsBTBlock G T E)
    (hn : ¬ E ≤ cStarIn G T) (hL : L ∈ lSet G T) (hEL : E ≤ L) :
    ∃ F : Subgroup Γ, IsBTBlock G T F ∧ E ≤ F ∧ F ≤ L ∧ ¬ F ≤ cStarIn G T ∧
      IsSubnormal F L := by
  have hT : IsSylowTwoOf T G := h.sylow
  obtain ⟨hLG, hBL, hLC⟩ := hL
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  obtain ⟨S, hS, hBS⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBL
  obtain ⟨-, -, hconcl⟩ := seven_three h hT ⟨hLG, hBL, hLC⟩ hS
  have hEL' : IsBTBlock L S E := isBTBlock_of_super hT hE hLG.le hEL hS hBS hn
  have hn' : ¬ E ≤ cStarIn L S := fun hc => hn (hc.trans (two_three_d hT hb0 hLG.le hS hBS))
  obtain ⟨F, hFb, hEF, hsub⟩ := exists_subnormal_block_ge hconcl hEL' hn'
  have hSX : baum S = baum T := baum_eq_of_isPGroup_of_baum_le hT hS.2.1 (hS.1.trans hLG.le) hBS
  have hFG : IsBTBlock G T F := isBTBlock_of_sub hFb hLG.le hSX (fun hc => hn (hEF.trans hc))
  exact ⟨F, hFG, hEF, hFb.le, fun hc => hn (hEF.trans hc), hsub⟩

theorem commutator_zSub_le_centralizer (h : MinCex G T) {F L : Subgroup Γ} (hF : IsBTBlock G T F)
    (hn : ¬ F ≤ cStarIn G T) (hL : L ∈ lSet G T) (hFL : F ≤ L) (hsub : IsSubnormal F L) :
    ∀ z ∈ zSub T, ∀ f ∈ F, ⁅z, f⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ) := by
  have hT : IsSylowTwoOf T G := h.sylow
  obtain ⟨hLG, hBL, hLC⟩ := hL
  obtain ⟨S, hS, hBS⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBL
  obtain ⟨hcharL, -, -⟩ := seven_three h hT ⟨hLG, hBL, hLC⟩ hS
  have hF' : IsBTBlock L S F := isBTBlock_of_super hT hF hLG.le hFL hS hBS hn
  have hb : baum S = baum T := baum_eq_of_isPGroup_of_baum_le hT hS.2.1 (hS.1.trans hLG.le) hBS
  have hWZ : ⁅blockW F, omegaOneCenterOf (baum S)⁆ = ⊥ :=
    commutator_blockW_omegaOneCenter_baum hcharL (isSylowOf_of_isSylowTwoOf hS) hF' hsub
  have hVQ : vSub G T ≤ pCoreOf 2 G := vSub_le_pCoreOf h.charTwo hT
  have hFV : F ≤ Subgroup.normalizer (vSub G T : Set Γ) := hF.le.trans (le_normalizer_vSub G T)
  have hne : ⁅F, vSub G T⁆ ≠ ⊥ := commutator_vSub_ne_bot hF.le hn
  have hFC : F ⊓ Subgroup.centralizer (blockW F : Set Γ) ≤
      Subgroup.centralizer (vSub G T : Set Γ) := by
    have := (bridge_data_of_isBTBlock h.charTwo h.sylow hF hVQ hFV hne).2.2
    exact (this ▸ inf_le_right : F ⊓ Subgroup.centralizer (blockW F : Set Γ) ≤ _)
  have hFW : ∀ g ∈ F, ∀ w ∈ blockW F, g * w * g⁻¹ ∈ blockW F := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockW F hg) w).mp hw
  intro z hz f hf
  have hz' : z ∈ omegaOneCenterOf (baum S) := by rw [hb]; exact hz
  have hzB : z ∈ baum T := C1GN.omegaOneCenterOf_le_self (baum T) hz
  have hzN : z ∈ Subgroup.normalizer (F : Set Γ) := baum_le_normalizer_of_isBTBlock hF hzB
  have hzc : ∀ w ∈ blockW F, w * z = z * w := fun w hw => by
    have h1 : ⁅w, z⁆ ∈ (⁅blockW F, omegaOneCenterOf (baum S)⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hw hz'
    rw [hWZ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hzc' : ∀ w ∈ blockW F, w * z⁻¹ = z⁻¹ * w := fun w hw => by
    have h1 : ⁅w, z⁻¹⁆ ∈ (⁅blockW F, omegaOneCenterOf (baum S)⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hw ((omegaOneCenterOf (baum S)).inv_mem hz')
    rw [hWZ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  refine hFC ⟨?_, ?_⟩
  · have h1 : z * f * z⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hzN f).mp hf
    have h2 : ⁅z, f⁆ = (z * f * z⁻¹) * f⁻¹ := rfl
    rw [h2]
    exact F.mul_mem h1 (F.inv_mem hf)
  · show ⁅z, f⁆ ∈ Subgroup.centralizer (blockW F : Set Γ)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : f⁻¹ * w * f ∈ blockW F := by
      have := hFW f⁻¹ (F.inv_mem hf) w hw
      simpa using this
    have e1 : w * z = z * w := hzc w hw
    have e2 : (f⁻¹ * w * f) * z⁻¹ = z⁻¹ * (f⁻¹ * w * f) := hzc' _ hw'
    calc w * ⁅z, f⁆ = (w * z) * f * z⁻¹ * f⁻¹ := by simp only [commutatorElement_def]; group
      _ = (z * w) * f * z⁻¹ * f⁻¹ := by rw [e1]
      _ = z * f * ((f⁻¹ * w * f) * z⁻¹) * f⁻¹ := by group
      _ = z * f * (z⁻¹ * (f⁻¹ * w * f)) * f⁻¹ := by rw [e2]
      _ = ⁅z, f⁆ * w := by simp only [commutatorElement_def]; group

omit [Finite Γ] in
@[expose] def cenModSub (G V F : Subgroup Γ) (hGV : G ≤ Subgroup.normalizer (V : Set Γ)) :
    Subgroup Γ where
  carrier := {x | x ∈ G ∧ ∀ f ∈ F, ⁅x, f⁆ ∈ Subgroup.centralizer (V : Set Γ)}
  mul_mem' := by
    rintro x y ⟨hxG, hx⟩ ⟨hyG, hy⟩
    refine ⟨G.mul_mem hxG hyG, fun f hf => ?_⟩
    have h1 : ⁅x * y, f⁆ = x * ⁅y, f⁆ * x⁻¹ * ⁅x, f⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    refine Subgroup.mul_mem _ ?_ (hx f hf)
    have hxN : x ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set Γ) : Set Γ) :=
      B6.le_normalizer_centralizer hGV hxG
    exact (Subgroup.mem_normalizer_iff.mp hxN _).mp (hy f hf)
  one_mem' := ⟨G.one_mem, fun f _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxG, hx⟩
    refine ⟨G.inv_mem hxG, fun f hf => ?_⟩
    have h1 : ⁅x⁻¹, f⁆ = x⁻¹ * (⁅x, f⁆)⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have hxN : x⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set Γ) : Set Γ) :=
      B6.le_normalizer_centralizer hGV (G.inv_mem hxG)
    have h2 := (Subgroup.mem_normalizer_iff.mp hxN _).mp (Subgroup.inv_mem _ (hx f hf))
    rwa [inv_inv] at h2

theorem seven_eleven (h : MinCex G T) {E L : Subgroup Γ} (hE : IsBTBlock G T E)
    (hn : ¬ E ≤ cStarIn G T) (hL : L ∈ lSet G T) (hEL : E ≤ L) (hT0 : tZero G T ≤ L) :
    ∀ x ∈ tZero G T, ∀ e ∈ E, ⁅x, e⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ) := by
  have hT : IsSylowTwoOf T G := h.sylow
  obtain ⟨F, hF, hEF, hFL, hnF, hsub⟩ := exists_subnormal_block_of_le h hE hn hL hEL
  by_cases hZ : ⁅vSub G T, zSub T⁆ = ⊥
  · rw [tZero_of_eq hZ] at hT0 ⊢
    have hV : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub h.charTwo hT
    have hVQ : vSub G T ≤ pCoreOf 2 G := vSub_le_pCoreOf h.charTwo hT
    have hGV : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
    have hne : ⁅F, vSub G T⁆ ≠ ⊥ := commutator_vSub_ne_bot hF.le hnF
    have hQ : qSub (vSub G T) T ≤ cenModSub G (vSub G T) F hGV := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      refine ⟨hT.1 (hA.1.1 ha), ?_⟩
      exact commutator_le_of_offStarMin h.charTwo h.sylow hF hV hVQ hGV hFL
        ((le_qSub hA).trans hT0) hsub hne hA a ha
    intro x hx e he
    exact (hQ hx).2 e (hEF he)
  · rw [tZero_of_ne hZ]
    intro x hx e he
    exact commutator_zSub_le_centralizer h hF hnF hL hFL hsub x hx e (hEF he)

end CFSG.CGT.PushingUpLit.BHS7
