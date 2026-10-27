module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Dg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Db
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Bundles

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem isSubnormal_subgroupOf_of_eq {X : Type*} [Group X] {K A B : Subgroup X}
    (hAB : A = B) (h : (K.subgroupOf A).IsSubnormal) : (K.subgroupOf B).IsSubnormal := by
  subst hAB
  exact h

theorem asc82Step109D_of (hK0 : Asc82Lemma10K0) (hf : Asc82Facts10) (hb : Asc82Basic10) :
    Asc82Step109D := by
  intro G _ _ t L S z K1 K2 g hctx hsc
  have hctx' : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  obtain ⟨ht2, hz2, ht1, hz1, hne, htz⟩ := sec10D_basic hb hctx'
  obtain ⟨hpsp, -, -, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  let H : Subgroup G := centralizer ({z} : Set G)
  have hT : IsSylow2Of (S ⊔ zpowers g) H := sec10D_sylow hz2 htS hctx hsc
  have htT : t ∈ S ⊔ zpowers g := Subgroup.mem_sup_left htS
  have hzT : z ∈ S ⊔ zpowers g := Subgroup.mem_sup_left hctx.mem_S
  have hdec : ∀ h ∈ H, ∃ o ∈ oddCoreIn H, ∃ c ∈ hatCent t z, h = o * c :=
    sec10D_decomp hT htT hzT hsc ht2 hz2 htz ht1 hz1 hne
  obtain ⟨hK1K0, -, -⟩ := sec10D_K0_contains hK0 hctx'
  have hK0H : secK0 t z ≤ H := (sec10D_K0_le t z).trans inf_le_right
  have hOK0 : oddCoreIn (secK0 t z) ≤ secK0 t z := CFSG.ClassicalInvolution.Balance.oddCoreIn_le _
  have hK1H : K1 ≤ H := hK1K0.trans hK0H
  have hK1OH : K1 ⊔ oddCoreIn (secK0 t z) ≤ H := sup_le hK1H (hOK0.trans hK0H)
  have hN : oddCoreIn H ≤ H := CFSG.ClassicalInvolution.Balance.oddCoreIn_le H
  have hNn : ∀ h ∈ H, ∀ n ∈ oddCoreIn H, h * n * h⁻¹ ∈ oddCoreIn H :=
    fun h hh n hn => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := H) hh hn
  have hsub : (((K1 ⊔ oddCoreIn (secK0 t z)) ⊔ oddCoreIn H).subgroupOf H).IsSubnormal :=
    sec10_isSubnormal_sup_odd (H := H) (C := hatCent t z) (K := secK0 t z)
      (K1 := K1 ⊔ oddCoreIn (secK0 t z)) (N := oddCoreIn H) hN hNn inf_le_left hdec
      (sec10D_K0_le_hatCent t z)
      (fun c hc x hx => sec10D_hatCent_normalizes_K0 hK0 hctx' ht2 hz2 htz ht1 hne hc x hx)
      (sup_le hK1K0 hOK0) (sec10D_K0_normalizes_K1O hK0 hf.pockets5 hpsp hctx')
  have hSL1 : IsSL23Mod ↥(K1 ⊔ oddCoreIn (secK0 t z)) :=
    isSL23Mod_sup_odd (K1 := K1) (N := oddCoreIn (secK0 t z)) hctx.pocket1.2.2.2
      (fun k hk n hn =>
        CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := secK0 t z) (hK1K0 hk) hn)
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn _)
  have hSL : IsSL23Mod ↥((K1 ⊔ oddCoreIn (secK0 t z)) ⊔ oddCoreIn H) :=
    isSL23Mod_sup_odd (K1 := K1 ⊔ oddCoreIn (secK0 t z)) (N := oddCoreIn H) hSL1
      (fun k hk n hn =>
        CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := H) (hK1OH hk) hn)
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn H)
  refine ⟨hctx.toSec10Z.pocket.1, (K1 ⊔ oddCoreIn (secK0 t z)) ⊔ oddCoreIn H,
    Subgroup.mem_sup_left (Subgroup.mem_sup_left hctx.pocket1.1), ?_, ?_, hSL⟩
  · exact le_inf le_top (sup_le hK1OH hN)
  · exact isSubnormal_subgroupOf_of_eq (K := (K1 ⊔ oddCoreIn (secK0 t z)) ⊔ oddCoreIn H)
      (A := H) (B := ⊤ ⊓ centralizer ({z} : Set G)) (top_inf_eq H).symm hsub

end CFSG.OddStandard.SmallF3.Omega
