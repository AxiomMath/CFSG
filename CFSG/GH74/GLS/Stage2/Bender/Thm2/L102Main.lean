module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Quasi
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Odd
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10Two

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement



section Main

theorem lemma10_2b_C2_of_b2 (hB2 : B_B2_g4) : Lemma10_2b_C2 := by
  intro G _ _ z k S M p Q T U t g h hnot H hHtop hHOK R hR hmax
  have ctx9 := h.ctx9
  have ctx : Stage2Ctx G z k S := ctx9.ctx
  have hch := h.choice
  obtain ⟨hTdef, hsw, hSyl, hIne, hzc⟩ := hch.T_two hnot
  have hUgen : U = zpowers z ⊔ zpowers t := hch.U_gen
  have hUS : U ≤ S := hch.U_le
  have hU4 : IVK.IsFourSubgroup U := hch.U_four
  have htconj : t = g⁻¹ * z * g := hch.t_conj
  subst hUgen
  have hz2 : orderOf z = 2 := ctx.orderOf_z
  have hzt : z * t = t * z := mul_comm_of_isFour hU4 mem_sup_left' mem_sup_right'
  have htc : IsConj z t := isConj_iff.mpr ⟨g⁻¹, by rw [htconj]; group⟩
  have ht2 : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    rw [← hc, orderOf_conj_eq]
    exact hz2
  have htS : t ∈ S := hUS mem_sup_right'
  obtain ⟨q, L₁, L₂, x, hpair, htwo⟩ := caseC_of_not_typeOne ctx hnot
  have hts : Swaps z t L₁ L₂ := swaps_of_swapsComps hpair hsw
  obtain ⟨hs, hnc⟩ := Iof_quotient_simple hB2 ctx hpair htwo htS htc hts hU4
  generalize hUdef : zpowers z ⊔ zpowers t = U at *
  have hXU : XU z t = centralizer (U : Set G) := by rw [← hUdef]
  have hIle : Iof U ≤ centralizer (U : Set G) := TwoThin.pLayerOf_le 2 (centralizer (U : Set G))
  have hXUeq : centralizer (U : Set G) = centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
    rw [← hXU, XU_eq hzt, inf_comm]
  have hIU : Iof U ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := hXUeq ▸ hIle
  have hIdef : Iof U = pLayerOf 2 (XU z t) := by rw [hXU]; rfl
  have hCI : ∀ c ∈ centralizer (U : Set G), c ∈ normalizer ((Iof U : Subgroup G) : Set G) := by
    intro c hc
    rw [hIdef]
    rw [← hXU] at hc
    exact CFSG.GH74.GLS.Stage1.Thm2.Recip.mem_normalizer_pLayerOf (X := XU z t) hc
  have hIperf : ⁅Iof U, Iof U⁆ = Iof U := by
    have hp' : Group.IsPerfect ↥(pLayer ↥(XU z t) 2) :=
      Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect _)
    have hmap : Iof U = (pLayer ↥(XU z t) 2).map (XU z t).subtype := by
      rw [hIdef]
      exact CFSG.GH74.GLS.Stage2.Final.Thm4.pLayerOf_eq_map 2 _
    rw [hmap]
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.map (f := (XU z t).subtype)
      (H := pLayer ↥(XU z t) 2))
  have hKI : pPrimeCoreOf 2 (Iof U) ≤ Iof U := TwoThin.pPrimeCoreOf_le _
  have hKn : Iof U ≤ normalizer ((pPrimeCoreOf 2 (Iof U) : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_pPrimeCoreOf (le_normalizer hg)
  have hKodd : Odd (Nat.card ↥(pPrimeCoreOf 2 (Iof U))) := TwoThin.card_pPrimeCoreOf_odd _
  have hKmax : ∀ L : Subgroup G, L ≤ Iof U → Iof U ≤ normalizer (L : Set G) →
      Odd (Nat.card ↥L) → L ≤ pPrimeCoreOf 2 (Iof U) := fun L hLI hIL hLodd =>
    le_pPrimeCoreOf_of_normal_odd hLI (fun x hx n hn => (Subgroup.mem_normalizer_iff.mp (hIL hx) n).mp hn)
      hLodd
  have hTH : T ≤ normalizer (H : Set G) := hHOK.1
  have hTN : T ≤ normalizer ((pPrimeCoreOf 2 H : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_pPrimeCoreOf (hTH hg)
  have hNH : pPrimeCoreOf 2 H ≤ H := TwoThin.pPrimeCoreOf_le _
  have hHN : H ≤ normalizer ((pPrimeCoreOf 2 H : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_pPrimeCoreOf (le_normalizer hg)
  have hNodd : Odd (Nat.card ↥(pPrimeCoreOf 2 H)) := TwoThin.card_pPrimeCoreOf_odd _
  have hSp : IsPGroup 2 ↥S := ctx.sylow.isPGroup
  have hTS : T ≤ S := by rw [hTdef]; exact inf_le_left
  have hT2 : IsPGroup 2 ↥T := hSp.to_le hTS
  have hUcent : U ≤ centralizer (U : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => mul_comm_of_isFour hU4 hv hu
  have hTcent : T ≤ centralizer (U : Set G) := by rw [hTdef]; exact inf_le_right
  have hUT : U ≤ T := by rw [hTdef]; exact le_inf hUS hUcent
  have hTI : T ≤ normalizer ((Iof U : Subgroup G) : Set G) := fun g hg => hCI g (hTcent hg)
  have hp : p.Prime := ctx9.prime
  have hp2 : p ≠ 2 := ctx9.odd
  refine ⟨hR, fun R₂ hR₂ hRR₂ => ?_⟩
  obtain ⟨hR₂ne, hR₂p, hR₂H, hTR₂, hcov₂⟩ := hR₂
  obtain ⟨hR₁ne, hR₁p, hR₁H, hTR₁, hcov₁⟩ := hR
  have hUH : U ≤ normalizer (H : Set G) := hUT.trans hTH
  have hH₁n : H ⊔ U ≤ normalizer (H : Set G) := sup_le le_normalizer hUH
  have hH₁top : H ⊔ U ≠ ⊤ := by
    intro htop
    have hn : normalizer (H : Set G) = ⊤ := eq_top_iff.mpr (htop ▸ hH₁n)
    have : H.Normal := Subgroup.normalizer_eq_top_iff.mp hn
    rcases ctx.std.kps.1.eq_bot_or_eq_top_of_normal H with h0 | h0
    · exact hR₁ne (le_bot_iff.mp (h0 ▸ hR₁H))
    · exact hHtop h0
  have hzU : z ∈ U := hUdef ▸ mem_sup_left'
  have htU : t ∈ U := hUdef ▸ mem_sup_right'
  have hN₁ := pPrimeCoreOf_sup_le (hT2.to_le hUT) hUH
  have hCI' : ∀ c ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
      c ∈ normalizer ((Iof U : Subgroup G) : Set G) := fun c hc => hCI c (hXUeq ▸ hc)
  have hkey := hkey_of_quasi hB2 ctx.std.kps ctx.std.gen4 hz2 ht2 hzt hH₁top
    (Subgroup.mem_sup_right hzU) (Subgroup.mem_sup_right htU) le_sup_left hH₁n hIU hCI' hs hnc hN₁
  have hRR : R₂ ≤ R := core hp hp2 hT2 hUT hTH hTI hTN hTR₁ hTR₂ hIle hIperf hCI hKI hKn hKodd hKmax
    hNH hHN hNodd hRR₂ hR₂H hR₂p hR₁ne (hcov₁ hnot) (hcov₂ hnot) hkey
    (fun V hV0 hVp hVle hTV hcovV hRV => hmax.2 V ⟨hV0, hVp, hVle, hTV, fun _ => hcovV⟩ hRV)
  exact le_antisymm hRR hRR₂

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
