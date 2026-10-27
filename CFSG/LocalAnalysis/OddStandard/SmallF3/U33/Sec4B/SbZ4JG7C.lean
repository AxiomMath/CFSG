module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD18D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG3C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG4B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG5A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG5B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG6A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG7A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG7B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma z4j_mul_sq_of_comm {H : Type*} [Group H] {a b : H} (hab : a * b = b * a)
    (ha : a * a = 1) (hb : b * b = 1) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab.symm]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

namespace Ctx4Z


theorem z4j_false (hG : Sec4Glob G) (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
    (hsyl : IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho))
    (hrel : (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 1) : False := by
  haveI : IsSimpleGroup G := hG.simple
  obtain ⟨Ng, hN⟩ := hz.z4i_exists_odd hsyl
  haveI := hz.z4i_normal_N hN
  obtain ⟨V', v₁, v₂, hV⟩ := hz.data_V
  have hVQ : V' ≤ ctxQ t tau x₁ x₂ rho := by rw [hV.2.2.1]; exact le_sup_right
  have hH := hz.z4jHData hN hV (hVQ hV.2.2.2.2.2.2.1) (hVQ hV.2.2.2.2.2.2.2.1) hrel
  obtain ⟨Mh, hMh⟩ := hH.exists_Mh
  obtain ⟨Mc, hMc⟩ := hH.exists_Mc hMh
  have hodd : Odd (Nat.card (hz.z4iSub Ng)) := by
    rw [hz.z4i_card_sub hN.le_NQ]; exact hN.odd
  have hQ2 : IsPGroup 2 (hz.z4iSub (ctxQ t tau x₁ x₂ rho)) :=
    IsPGroup.of_card (n := 6) (by rw [hz.z4i_card_sub hz.z4i_Q_le_NQ, hz.card_Q] <;> norm_num)
  obtain ⟨Vc, hVc, hQVc, -⟩ := S4B.z4j_exists_lift_max hodd hQ2 (hH.Vh_isPGroup hMh hMc)
    ((hH.Q_le_Mc hMh hMc).trans (S4B.Mc_le_zjVh _ _ _ _))
    (fun P h hle => hH.Vh_maximal hMh hMc h hle)
  have hVsub : hz.z4iSub (fourGrp x₁ x₂) ≤ Vc := fun x hx =>
    hQVc ((hz.V_le_Y.trans hz.Y_le_Q) hx)
  have hT : ∀ a : ↥(ctxNQ t tau x₁ x₂ rho), a * a = 1 → a ≠ 1 →
      (hz.z4jT (Ng := Ng) (S4B.z4iπ (hz.z4iSub Ng) a) ↔ ∃ g : G, (a : G) = g * t * g⁻¹) :=
    fun a ha ha1 => hz.z4jT_map_iff hN ha ha1
  have hTlt : hz.z4jT (Ng := Ng) (S4B.z4iπ (hz.z4iSub Ng) hz.z4iLam *
      S4B.z4iπ (hz.z4iSub Ng) hz.z4iT) := by
    obtain ⟨h, hh⟩ := hz.sigma_conj_t
    exact ⟨hz.z4iLam * hz.z4iT, by rw [map_mul], h, hh.symm⟩
  have hTt : hz.z4jT (Ng := Ng) (S4B.z4iπ (hz.z4iSub Ng) hz.z4iT) :=
    ⟨hz.z4iT, rfl, 1, by show t = 1 * t * 1⁻¹; group⟩
  have hnormV : ∀ g ∈ S4B.zjVh Mc (S4B.z4iπ (hz.z4iSub Ng) hz.z4iT)
      (S4B.z4iπ (hz.z4iSub Ng) hz.z4iTau) (S4B.z4iπ (hz.z4iSub Ng) hz.z4iLam), ∀ v ∈
      (hz.z4iSub (fourGrp x₁ x₂)).map (S4B.z4iπ (hz.z4iSub Ng)),
      g * v * g⁻¹ ∈ (hz.z4iSub (fourGrp x₁ x₂)).map (S4B.z4iπ (hz.z4iSub Ng)) :=
    fun g _ v hv => hH.normal_V g v hv
  have hσ2 := z4j_mul_sq_of_comm hH.t_l.symm hH.l_sq hH.t_sq
  have hVgi : ¬ 2 ∣ (Vc.map (ctxNQ t tau x₁ x₂ rho).subtype).index :=
    S4B.z4j_stageF hVc hVsub (S4B.Mc_le_zjVh _ _ _ _) hnormV (hH.V_le_commutator_Vh hMh hMc)
      hH.card_V (hH.V_elem_ab hMh hMc)
      (fun W hW hWn hWd hW4 hWe => hH.V_unique hMh hMc hW hWn hWd hW4 hWe)
      (hH.cent_V_Vh hMh hMc)
      (Subgroup.mul_mem _ (S4B.l_mem_zjVh _ _ _ _) (S4B.t_mem_zjVh _ _ _ _)) hσ2
      (hH.lt_not_mem_McTT hMh hMc) hT hTlt
      (fun u hu hu2 hTu huK => hH.T_invol_coset hMh hMc (hz.z4j_class hN) hu hu2 hTu huK)
      (hH.card_cent_Vh_lt hMh hMc) (fun g R hR hRc => hz.z4j_bound_conj g hR hRc)
  have hgold := S4B.z4j_gold_lift hz.z4j_nonabelian hVc (hH.Vq_le_Vh hMh hMc)
    (by rw [hH.card_Vh hMh hMc, hH.card_Vq hMh hMc] <;> norm_num) hVgi
    (T := hz.z4jT (Ng := Ng)) hT (S4B.t_mem_zjVh _ _ _ _) (hH.t_not_mem_Vq hMh hMc) hH.t_sq hTt
    (fun g P hP hPc hPi => hz.z4j_card_syl_cent g hP hPc hPi)
  have hVL : fourGrp x₁ x₂ ≤ ctxNQ t tau x₁ x₂ rho :=
    (hz.V_le_Y.trans hz.Y_le_Q).trans hz.z4i_Q_le_NQ
  have htV : ∀ g : G, ∀ v ∈ (hz.z4iSub (fourGrp x₁ x₂)).map (ctxNQ t tau x₁ x₂ rho).subtype,
      g * t * g⁻¹ ≠ v := by
    intro g v hv
    rw [Subgroup.map_subgroupOf_eq_of_le hVL] at hv
    exact Ctx4.tG_inf_four hz.toCtx10.toCtx4 g v hv
  exact hH.zj_end hMh hMc (hz.z4j_bound hN)
    { toZJClass := hz.z4j_class hN
      no_abelian := hz.z4j_no_abelian hN
      e16 := fun F hFV hFab hF2 hF => hz.z4j_e16 hN hVc hFV hFab hF2 hF
      gold := hgold
      d17 := fun m hm hTm hcardm => by
        have hβK : m * S4B.z4iπ (hz.z4iSub Ng) hz.z4iTau ∈ Mc ⊔
            closure ({S4B.z4iπ (hz.z4iSub Ng) hz.z4iT, S4B.z4iπ (hz.z4iSub Ng) hz.z4iTau} :
              Set (↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng)) :=
          Subgroup.mul_mem _ (Subgroup.mem_sup_left hm)
            (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
        have hinv := (hz.z4j_class hN).invol _ hTm
        exact S4B.z4j_d17_lift hVc hVsub (fun g _ v hv => hH.normal_V g v hv) hH.card_V
          (hH.V_elem_ab hMh hMc) htV
          (fun g P hP hPc hP128 => hz.z4j_conj_onto_S g hP hPc hP128)
          (fun V'' hV''S hn h4 he ht => hz.z4j_count17 hV''S hn h4 he ht)
          (T := hz.z4jT (Ng := Ng)) hT
          (Subgroup.mul_mem _ (S4B.Mc_le_zjVh _ _ _ _ hm) (S4B.tau_mem_zjVh _ _ _ _))
          hinv.1 hinv.2 hTm ((hH.cent_V_Vh hMh hMc).ge hβK).2 hcardm }

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
