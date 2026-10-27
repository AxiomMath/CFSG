module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Pairs
public import Certificates.Certificate320330
public import Certificates.Certificate320331
public import Certificates.Certificate320332

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.C3.Layer1.EndN.U43 (hud P43)
open CFSG.GH74.GLS.C3.Layer1.EndN.U43.Mat (isPrimeFormGram_one4)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LieType.Multipliers.U43 (F9)

theorem pairWit_map_equiv {W W' : Type*} [Group W] [Group W'] (e : W ≃* W') {F₀ : Subgroup W}
    {F₀' : Subgroup W'} (hF : F₀.map e.toMonoidHom = F₀') {x t : W} (h : PairWit F₀ x t) :
    PairWit F₀' (e x) (e t) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hc₁, hc₂, a, ha, b, hb, hao, hbo, hab⟩ := h
  have himg : (Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set W)).map e.toMonoidHom =
      Subgroup.closure ({e x, e g₁ * e x * (e g₁)⁻¹, e g₂ * e x * (e g₂)⁻¹} : Set W') := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom, map_mul,
      map_inv]
  have hord : ∀ c : W, orderOf (e c) = orderOf c := fun c => MulEquiv.orderOf_eq e c
  refine ⟨e g₁, hF ▸ Subgroup.mem_map_of_mem _ hg₁, e g₂, hF ▸ Subgroup.mem_map_of_mem _ hg₂, ?_,
    ?_, e a, ?_, e b, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hc₁]
  · rw [← map_mul, ← map_mul, hc₂]
  · rw [← himg]
    exact Subgroup.mem_map_of_mem _ ha
  · rw [← himg]
    exact Subgroup.mem_map_of_mem _ hb
  · rw [hord]
    exact hao
  · rw [hord]
    exact hbo
  · rw [← map_mul, hord]
    exact hab

theorem exists_mulEquiv_P43 {F : Type} [Group F] (h : CFSG.Blueprint.LieModel F .PSU 4 3 1) :
    Nonempty (F ≃* P43) := by
  have hst := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hst
  have : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, hK, F9.card_eq]
    norm_num
  let ι : K ≃+* F9 := FiniteField.ringEquivOfCardEq hKF
  let e2 := e.trans (CFSG.Fischer.Classification.Recognition.statedProjSUEquiv ι 4 (3 ^ 1))
  obtain ⟨eT⟩ := nonempty_primeFormP_mulEquiv hud (isPrimeFormGram_one (n := 4) (K := F9))
  exact ⟨(e2.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hud (by norm_num)).symm).trans
    eT.symm⟩


theorem pairWit_P43 : ∀ x t : MulAut P43, orderOf x = 8 → orderOf t = 2 → x * t = t * x →
    PairWit (inner P43) x t := by
  intro x t hx ht hxt
  haveI : Finite P43 := Nat.finite_of_card_ne_zero (by rw [card_P43]; norm_num)
  haveI : Finite (MulAut P43) :=
    Finite.of_injective (fun f : MulAut P43 => (f : P43 → P43)) DFunLike.coe_injective
  have hs : sylowOK u43Data = true := Certificates.certificate320330
  have hc : coverOK u43Data = true := Certificates.certificate320331
  have hr : repsOK u43Data = true := Certificates.certificate320332
  exact pairWit_of_sylow (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal P43)
    (ssub_isPGroup hs) (ssub_index_odd hs) (pairWit_of_checks hs hc hr) hx ht hxt

theorem localU43_holds : LocalU43 := by
  refine localNoQ16Q16_of_pairWit ?_
  intro F _ hF x t hx ht hxt
  obtain ⟨eP⟩ := exists_mulEquiv_P43 hF
  let e : MulAut F ≃* MulAut P43 := MulAut.congr eP
  have h := pairWit_P43 (e x) (e t) (by rw [MulEquiv.orderOf_eq]; exact hx)
    (by rw [MulEquiv.orderOf_eq]; exact ht) (by rw [← map_mul, ← map_mul, hxt])
  have hF' : (inner P43).map e.symm.toMonoidHom = inner F := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr eP, Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      ext z
      simp
    rw [this, Subgroup.map_id]
  have h2 := pairWit_map_equiv e.symm hF' h
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h2
  exact h2

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
