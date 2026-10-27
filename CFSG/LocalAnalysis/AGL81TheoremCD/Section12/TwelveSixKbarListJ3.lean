module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListJ3Cfg
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListAct
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarE27Kit
import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.NineSettingOfHypC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Lift

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C

namespace KbarJ3

private theorem conj_injective {S : Type} [Group S] (hZ : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  rw [← hZ, mem_center_iff]
  intro g
  have h := congrArg (fun φ : MulAut S => φ g) hz
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * z = z * g * z⁻¹ * z := by rw [h]
    _ = z * g := by group

private theorem eq_one_of_commute_conj {S : Type} [Group S] (hZ : center S = ⊥) {α : MulAut S}
    (hα : ∀ s : S, α * MulAut.conj s = MulAut.conj s * α) : α = 1 := by
  apply MulEquiv.ext
  intro s
  have hconj : α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
    apply MulEquiv.ext
    intro x
    change α (s * α.symm x * s⁻¹) = α s * x * (α s)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h : MulAut.conj (α s) = MulAut.conj s := by
    rw [← hconj, hα s, mul_inv_cancel_right]
  exact conj_injective hZ h

end KbarJ3

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem TwelveSixKbarHyp.false_of_j3 (hJS : CFSG.AGLEmbedding.KFactJ3Sylow)
    (hJO : CFSG.AGLEmbedding.KFactJ3OuterInvolution) (hJR : CFSG.AGLEmbedding.KFactJ3OuterRank)
    (hyp : TwelveSixKbarHyp G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hK : IsTwoPrimeComponentIn (kSub 3 M H) H)
    (hJ : Nonempty (kbarQuot 3 M H ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH := hyp.2.2.2.2.2.2
  obtain ⟨V, W₁, W₂, W₃, t₁, t₂, t₃, hcfg, hVB, ht₁, ht₂, ht₃, hinj⟩ := hyp.exists_cfg_inf hK hKH
  have hc := hyp.1
  have hL := hyp.2.2.2.1
  have hXM := hyp.2.2.2.2.1
  set ψ := KbarList.kbarAct hKH with hψ
  set ψ' : ↥H →* ↥ψ.range := ψ.rangeRestrict with hψ'
  have hψ's : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  have hZS : center (kbarQuot 3 M H) = ⊥ := by
    obtain ⟨-, hs, a, b, hab⟩ := hK.2.2.1
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right fun ht =>
      hab (mem_center_iff.mp (ht ▸ mem_top b) a)
  have hInnY := KbarList.conj_range_le_range hKH
  have hInnN : ((MulAut.conj : kbarQuot 3 M H →* MulAut (kbarQuot 3 M H)).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set K₀ : Subgroup ↥ψ.range :=
    ((MulAut.conj : kbarQuot 3 M H →* MulAut (kbarQuot 3 M H)).range).subgroupOf ψ.range with hK₀
  have hK₀n : K₀.Normal := hInnN.subgroupOf _
  have hK₀J : Nonempty (↥K₀ ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) := by
    obtain ⟨e⟩ := hJ
    exact ⟨(subgroupOfEquivOfLe hInnY).trans
      ((MonoidHom.ofInjective (KbarJ3.conj_injective hZS)).symm.trans e)⟩
  have hK₀C : centralizer (K₀ : Set ↥ψ.range) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    have h1 : (y : MulAut (kbarQuot 3 M H)) = 1 := by
      refine KbarJ3.eq_one_of_commute_conj hZS fun s => ?_
      have hs : (⟨MulAut.conj s, hInnY ⟨s, rfl⟩⟩ : ↥ψ.range) ∈ K₀ := by
        rw [hK₀, mem_subgroupOf]
        exact ⟨s, rfl⟩
      exact (congrArg Subtype.val (mem_centralizer_iff.mp hy _ hs)).symm
    exact Subtype.ext h1
  obtain ⟨E₀, hE₀Q, hE₀, hE₀c, hΓ⟩ := hc.ctx.exists_E_sq
  have hd := hc.ctx.hypCGen hE₀Q hE₀ hE₀c hΓ
  have hU : NineNineOne M 3 := hc.hI G M E₀ H E₀ 3 hd.toNineSettingGen hd.not_mem_sigmaM
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (H ⊓ M)
  obtain ⟨hPH, hPN⟩ := isSylowOf_of_NineNineOne hc.ctx.maxLocal hc.ctx.mem_QSet hc.ctx.Q_le_H
    hd.not_mem_sigmaM hU hP
  obtain ⟨PH, hPHe⟩ := hPH.exists_sylow_eq_subgroupOf
  set B : Subgroup ↥ψ.range := ((H ⊓ M).subgroupOf H).map ψ' with hB
  have hNPH : normalizer ((PH : Subgroup ↥H) : Set ↥H) ≤ (H ⊓ M).subgroupOf H := by
    intro h hh
    rw [hPHe, ← subgroupOf_normalizer_eq hPH.le, mem_subgroupOf] at hh
    exact mem_subgroupOf.mpr ⟨h.2, hPN hh⟩
  have hNB : normalizer (((PH.mapSurjective hψ's : Sylow 3 ↥ψ.range) : Subgroup ↥ψ.range) :
      Set ↥ψ.range) ≤ B := by
    have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Lift.map_normalizer_sylow ψ'
      Nat.prime_three PH.isPGroup' PH.not_dvd_index
    rw [MonoidHom.range_eq_top.2 hψ's, inf_top_eq] at h
    rw [Sylow.coe_mapSurjective, ← h]
    exact map_mono hNPH
  have hBne : B ≠ ⊤ := by
    intro hBtop
    apply Section14.not_kSub_le_of_not_pLayerIn_le hL
    intro k hk
    have hkH : k ∈ H := Section14.kSub_le 3 M H hk
    obtain ⟨m, hm, hmk⟩ : ψ' ⟨k, hkH⟩ ∈ B := hBtop ▸ mem_top _
    have hker : m⁻¹ * ⟨k, hkH⟩ ∈ ψ'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmk, inv_mul_cancel]
    rw [MonoidHom.ker_rangeRestrict] at hker
    have hX := KbarList.ker_kbarAct_le hc.ctx hKH hK hker
    rw [mem_subgroupOf] at hX
    have hmM : (m : G) ∈ M := (mem_subgroupOf.mp hm).2
    have hk' : k = (m : G) * ((m⁻¹ * ⟨k, hkH⟩ : ↥H) : G) := by simp
    rw [hk']
    exact M.mul_mem hmM (hXM hX)
  have hinj' : ∀ v ∈ V, ψ' v = 1 → v = 1 := fun v hv h1 =>
    hinj v hv (by simpa [hψ'] using congrArg Subtype.val h1)
  exact KbarJ3.false_of_j3 hJS hJO hJR hK₀n hK₀J hK₀C _ hNB hBne
    (KbarE27.isE27InvConfig_map hcfg ψ' hinj') (map_mono hVB) (mem_map_of_mem _ ht₁)
    (mem_map_of_mem _ ht₂) (mem_map_of_mem _ ht₃)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
