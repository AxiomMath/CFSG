module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bCover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf25Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Ee

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc (coreHull)

section Transport

theorem mem_pCore_iff_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (p : ℕ) (a : A) :
    a ∈ pCore p A ↔ e a ∈ pCore p B := by
  rw [← pCore_map_iso p e]
  constructor
  · intro h
    exact ⟨a, h, rfl⟩
  · rintro ⟨y, hy, hya⟩
    have : y = a := e.injective hya
    rwa [this] at hy

theorem card_pCore_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (p : ℕ) :
    Nat.card (pCore p A) = Nat.card (pCore p B) := by
  rw [← pCore_map_iso p e, Subgroup.card_map_of_injective e.injective]

end Transport

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem layer_pCoreOf (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 ↥M) (hO : oddCoreOf (rLayer Ω c) = ⊥)
    (hS : TwinDisc.Q8Section (TwinPerpV3.LSec Ω c) (TwinDisc.secFam Ω c))
    (I : AEIdent (TwinDisc.secFam Ω c) 6) (hH : TL4.AECoverHyp I)
    (hcY : c ∈ rLayer Ω c) (hc1 : c ≠ 1) :
    Nat.card ↥(pCoreOf 2 (rLayer Ω c)) = 32 ∧ (∀ x ∈ pCoreOf 2 (rLayer Ω c), x * x = 1) ∧
      c ∈ pCoreOf 2 (rLayer Ω c) ∧
      ∀ J ∈ tqMembers3 Ω c, ∀ t : G, IsUniqueInvolution J t → t ∈ pCoreOf 2 (rLayer Ω c) := by
  classical
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 (fun M hM => (h2 M hM).to_quotient _)
  have hOYu : classicalInvolutionOddCore ↥(rLayer Ω c) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hO
  have hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv (TwinPerpV3.hullEquiv hmap).symm hOYu
  have hgen : pSpan (TwinDisc.secFam Ω c) = ⊤ := TwinDisc.AE5.hgen_of hS
  let qe : ↥(coreHull Ω c) ≃* TwinPerpV3.LSec Ω c :=
    MulEquiv.ofBijective (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact hOH),
        QuotientGroup.mk'_surjective _⟩
  let pe : TwinPerpV3.LSec Ω c ≃* ↥(pSpan (TwinDisc.secFam Ω c)) :=
    ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv).symm
  let e : ↥(rLayer Ω c) ≃* ↥(pSpan (TwinDisc.secFam Ω c)) :=
    ((TwinPerpV3.hullEquiv hmap).symm.trans qe).trans pe
  have hk6 : 5 ≤ 6 := by norm_num
  have hcent : e ⟨c, hcY⟩ ∈ Subgroup.center ↥(pSpan (TwinDisc.secFam Ω c)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (TwinPerpV3.rLayer_le_centralizer Ω c hy)
  have hcentker : e ⟨c, hcY⟩ ∈ I.φ.ker := by
    rw [Sec13.EvenCov.ker_eq_center hk6 I]
    exact hcent
  have hū1 : e ⟨c, hcY⟩ ≠ 1 := fun h =>
    hc1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  have hker : I.φ.ker ≠ ⊥ := fun h => by
    rw [h] at hcentker
    exact hū1 (Subgroup.mem_bot.mp hcentker)
  obtain ⟨hcard, hexp, hkerle, hinv⟩ := pCore_cover_AE6 hH hker
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : Nat.card ↥(pCoreOf 2 (rLayer Ω c)) = Nat.card (pCore 2 ↥(rLayer Ω c)) := by
      unfold pCoreOf
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [h1, card_pCore_of_equiv e 2, hcard]
  · rintro x ⟨x', hx', rfl⟩
    have h1 := hexp (e x') ((mem_pCore_iff_of_equiv e 2 x').mp hx')
    have h2 : x' * x' = 1 := e.injective (by rw [map_mul, h1, map_one])
    simpa using congrArg Subtype.val h2
  · exact ⟨⟨c, hcY⟩, (mem_pCore_iff_of_equiv e 2 _).mpr (hkerle hcentker), rfl⟩
  · intro J hJ t ht
    obtain ⟨htC, htY, hU⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hJ ht
    have htYu : t ∈ rLayer Ω c := hmap ▸ ⟨⟨t, htC⟩, htY, rfl⟩
    refine ⟨⟨t, htYu⟩, (mem_pCore_iff_of_equiv e 2 _).mpr ?_, rfl⟩
    have h1 := hinv (TwinDisc.secImg Ω c J) (TwinDisc.secImg_mem_secFam hJ) _ hU
    have he1 : (TwinPerpV3.hullEquiv hmap).symm ⟨t, htYu⟩ = ⟨⟨t, htC⟩, htY⟩ :=
      (MulEquiv.symm_apply_eq _).mpr (Subtype.ext rfl)
    show pe (qe ((TwinPerpV3.hullEquiv hmap).symm ⟨t, htYu⟩)) ∈ _
    rw [he1]
    exact h1

end Layer

section Final


theorem v3AE6E_proved {n : ℕ} : A6S.V3AE6E n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨hStd, hF, hα, h2g, -⟩ := H.ex
  have hd := hStd.datum
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hd.hyp
  have hc2' : (u₁ * u₂) * (u₁ * u₂) = 1 := hd.sq_12
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2'
  have hO := oddCoreOf_rLayer_eq_bot hStd hF hα h2g H.oddC
  have hS := TwinPerpV3.layer_q8Section hStd.perp hc2'
  obtain ⟨I⟩ := H.ae6
  obtain ⟨hmem3, hmem4⟩ := TwinPerpV3.v3_tq_members hStd hF
  have hz4 : IsUniqueInvolution K₄ t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  obtain ⟨_, _, hU3⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem3 hd.hzK₃
  obtain ⟨_, _, hU4⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem4 hz4
  have hH : TL4.AECoverHyp I :=
    aeCoverHyp_of_twins (by norm_num) (by norm_num) hS I (TwinDisc.secImg_mem_secFam hmem3)
      (TwinDisc.secImg_mem_secFam hmem4) (Ne.symm (TwinPerpV3.v3_secImg_ne hStd hF)) hU3 hU4
  obtain ⟨hK₃Y, hK₄Y⟩ := members_le_rLayer hStd hF h2g
  have hYn : conjSub y (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) =
      rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := TwinMu.Pf3.conjSub_rLayer hΩ fr.hc
  have htY : t ∈ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := hK₃Y hd.hzK₃.mem
  have hτY : y * t * y⁻¹ ∈ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
    have := conj_mem_conjSub (n := y) htY
    rwa [hYn] at this
  have hcY : u₁ * u₂ ∈ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
    have e : u₁ * u₂ = (y * t * y⁻¹) * (a₃ * a₄)⁻¹ := by
      rw [fr.hy, ← fr.hu]
      group
    have h := Subgroup.mul_mem _ hτY
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hK₃Y fr.h₃.1) (hK₄Y fr.h₄.1)))
    rwa [← e] at h
  obtain ⟨hcard, hexp, hcE, hinvE⟩ :=
    layer_pCoreOf hΩ hc2 h2g hO hS I hH hcY hd.mul_ne_one
  have htE := hinvE K₃ hmem3 t hd.hzK₃
  have hyN : y ∈ Subgroup.normalizer
      (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) : Set Y) :=
    Asc77.mem_normalizer_iff_conjSub_eq.mpr hYn
  exact ⟨⟨by unfold A6S.ae6E; rw [hcard]; norm_num, hexp⟩, hcE, htE,
    TwinThin.pCoreOf_conj_mem hyN htE⟩

end Final

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6b
