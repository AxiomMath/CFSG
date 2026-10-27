module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafGLR
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafSL2Cent
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Core

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3 CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4


theorem localD43_holds : LocalNoQ16Q16' fun F _ => LieModel F .trialityD4 0 3 1 := by
  intro F _ hF Y _ _ N _ ⟨e⟩ hC t ht K K' hK hK' h2 h2' x hx y hy x' hx' y' hy' hxt hq
  have hm : LieModel ↥N .trialityD4 0 3 1 := LieModel.of_mulEquiv e.symm hF
  have hO : Nobq.OutTwoCyclic ↥N :=
    outTwoCyclic_trialityD4 (by decide)
      (Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide))
  obtain ⟨D, Ō, M, hDC, hŌD, hMD, htM, hDn, hŌn, hŌodd, hDŌ, -, hM64⟩ :=
    Q16Q16.local_reduction N hC hO hK hK' h2 h2' hx hy hx' hy' hq hxt
  have htN : t ∈ N := (Subgroup.mem_inf.1 (hDC (hMD htM))).1
  have htN' : orderOf (⟨t, htN⟩ : ↥N) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  obtain ⟨F₁, F₂, _, _, _, _, Sh, hc₁, hc₂, hz⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_D4 Nat.prime_three (by decide) hm _ htN'
  have hF₂ : Nat.card F₂ = 3 := by rw [hc₂, pow_one]
  have hF₁ : Nat.card F₁ = 27 := by rw [hc₁]; norm_num
  have h3 : (3 : F₂) = 0 := LieType.HighestRoot.three_eq_zero hF₂
  have hzt : ((Sh.z : ↥N) : Y) = t := by rw [hz]
  let P := Q3Sh.toCentShape htN Sh hzt h3 (two_ne_zero_of_three h3)
  have hcomm := commute_of_normal_odd_two (C := N ⊓ Subgroup.centralizer ({t} : Set Y))
    (A := P.A) (D := D) (O := Ō) (by rw [hF₁]; decide) (by rw [hF₁]; norm_num) P.eA P.le_A hDC
    P.normal_A hDn hŌn hŌodd hDŌ
  have hMB : M ≤ P.B := hMD.trans fun d hd => P.cent_A d (hDC hd) (hcomm d hd)
  have hB : Nat.card P.B = 24 := by
    rw [Nat.card_congr P.eB.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      hF₂]
    norm_num
  have hle : Nat.card M ≤ 24 :=
    hB ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hMB)
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
