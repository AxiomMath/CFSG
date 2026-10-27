module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResAssemblyC
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResTConc
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResModD
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResGL
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHElemAb
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHSeven
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputSecond
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataGenStrong
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open
open scoped commutatorElement

theorem oddSolv : OddSolv := fun _ _ _ h => CFSG.FeitThompson.isSolvable_of_odd_natCard _ h

theorem elemAbH1 : ElemAbH1 := by
  intro p r _ hp2 V _ _ hV hcard S hS hcomm
  exact CResH.elemAb_card_le_and_inv_mem hp2 hV hcard S hS hcomm

theorem elemAbH2 : ElemAbH2 := by
  intro p r _ hp2 V _ _ hV hcard S hS hcomm h8 hconj
  exact CResH.seven_le_of_elemAb_eight hp2 hV hcard S hS hcomm h8 hconj

theorem commutator_eq_top_of_simple {E : Type*} [Group E]
    (hs : ∀ N : Subgroup E, N.Normal → N = ⊥ ∨ N = ⊤) (hnc : ∃ a b : E, a * b ≠ b * a) :
    commutator E = ⊤ := by
  rcases hs (commutator E) inferInstance with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have : ⁅a, b⁆ ∈ commutator E := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · exact h

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {A B C D : Subgroup G}

theorem false_of_layer_eData
    (hs : LocalSetting G L z) (hF : FirstHalfData L z A B C D)
    (hE : EData ↥(egaLayer (egQD C ⧸ fusionOddCore (egQD C)))) : False := by
  classical
  have h : CSide.Setup L A C z := ⟨hs, hF.pair.1, hF.sextet, hF.cData, hF.c_elem⟩
  have hty : SextetType L A := hF.pair.sextet
  have hQ : SextetFactsQ L A := sextetFactsQ_of_type hty
  obtain ⟨H, hH, hTz, hTperf, hT1080, hTw, hlat⟩ := CSide.exists_triple_cover h hty
  have hC := h.hC.comm
  let ρ : egQD C →* MulAut C := CSide.actC C hC
  have hCc : Nat.card (MulAut C) ∣ gl12 :=
    card_mulAut_dvd_gl12 (fun a b => Subtype.ext (hC a a.2 b b.2))
      (fun a => Subtype.ext (hF.c_elem a a.2)) (by rw [h.hC.card]; norm_num)
  have hO : Odd (Nat.card (fusionOddCore (egQD C))) := odd_natCard_fusionOddCore _
  have hkerO : ρ.ker ≤ fusionOddCore (egQD C) :=
    (CSide.ker_actC_le_cQuot C hC).trans (CSide.cQuot_le_oddCore h)
  have hQodd : Odd (Nat.card ρ.ker) := hO.of_dvd_nat (Subgroup.card_dvd_of_le hkerO)
  have hQz : ∀ k ∈ ρ.ker, CSide.zt h * k = k * CSide.zt h → k = 1 := fun k hk hc =>
    CSide.eq_one_of_comm h (CSide.ker_actC_le_cQuot C hC hk) hc
  have hEperf : commutator ↥(egaLayer (egQD C ⧸ fusionOddCore (egQD C))) = ⊤ :=
    commutator_eq_top_of_simple hE.chief.simple hE.nonab
  have : (egaLayer (egQD C ⧸ fusionOddCore (egQD C))).Normal := egaLayer_normal _
  obtain ⟨U, hUn, hUperf, q, hq, hqm⟩ :=
    exists_perfect_cover (fusionOddCore (egQD C)) (egaLayer (egQD C ⧸ fusionOddCore (egQD C)))
      hEperf
  have := hUn
  have hker0 : ∀ u : U, q u = 1 → (u : egQD C) ∈ fusionOddCore (egQD C) := by
    intro u hu
    have := hqm u
    rw [hu] at this
    exact (QuotientGroup.eq_one_iff _).1 this.symm
  have hqodd : Odd (Nat.card q.ker) := by
    let f : q.ker →* fusionOddCore (egQD C) :=
      (U.subtype.comp q.ker.subtype).codRestrict _ fun k => hker0 k.1 (MonoidHom.mem_ker.1 k.2)
    have hf : Function.Injective f := fun a b hab => by
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact hO.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)
  have hker : ∀ u : U, ρ u = 1 → q u = 1 := by
    intro u hu
    have hmem : ((u : egQD C)) ∈ fusionOddCore (egQD C) := hkerO hu
    apply Subtype.ext
    rw [hqm u]
    exact (QuotientGroup.eq_one_iff _).2 hmem
  exact false_of_layer oddSolv elemAbH1 elemAbH2 hCc ρ hQodd (CSide.zt h) (CSide.zt_mul_self h) hQz
    (H.map (CSide.psi h)) hTz hTperf hT1080 hTw hlat
    (fun K hK => CSide.card_centralizer_le h hQ hH K hK) U hUperf q hq hqodd hker hE

end CFSG.EvenSporadicStandard.M24Std
