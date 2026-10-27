module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Hull

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J}

theorem Setting.false_of_fusionStronglyEmbedded_map (h : Setting J Q B)
    (hH : fusionStronglyEmbedded (B.map (QuotientGroup.mk' (Subgroup.center J)))) : False := by
  obtain ⟨j, hjB, P, hP, hPc, hPB⟩ := h.quaternion
  have hj : ((j : J ⧸ Subgroup.center J))⁻¹ ∉ B.map (QuotientGroup.mk' (Subgroup.center J)) := by
    rw [← QuotientGroup.mk_inv, h.mk_mem_map_iff]
    exact fun h' => hjB (by simpa using B.inv_mem h')
  refine Nat.not_even_iff_odd.mpr (hH.2.2 _ hj) (even_iff_two_dvd.mpr ?_)
  refine (h.two_dvd_card_map hP hPc).trans (Subgroup.card_dvd_of_le ?_)
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨(h.mk_mem_map_iff p).mpr (hPB p hp).1, Subgroup.mem_map.mpr
    ⟨((j⁻¹ * p * j : J) : J ⧸ Subgroup.center J), (h.mk_mem_map_iff _).mpr (hPB p hp).2, ?_⟩⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk'_apply]
  group

variable {u : J}

theorem PartC.false_of_caseB1
    (h : Setting J Q B) (T : Sylow 2 (quasiNormalizer u))
    (hTB : (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u))
    {L : Subgroup (QuasiQuotient u)} (hLn : L.Normal)
    (hc : PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u)
    (hT : partCSylow T ≤ partCLeft T L ⊔ partCRight T L) {n : ℕ} (hn : 4 ≤ n)
    (hφ : Nonempty (partCRight T L ≃* QuaternionGroup (2 ^ (n - 2)))) : False := by
  have hb := h.caseB1 T hTB hLn hc hT hn hφ
  obtain ⟨⟨x, hx⟩, hx1⟩ := (b1X T L).ne_bot_iff_exists_ne_one.mp fun hbot => by
    have h4 := hb.card_X
    rw [hbot, Subgroup.card_bot] at h4
    omega
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hloc : InvolutionPointLocalEmbedding (b1Bar B) x :=
    ⟨hb.setting.map_ne_top, hb.S_le (hb.X_le_S hx), hb.orderOf_of_mem_X hx hx1',
      hb.unique_containment hx hx1', hb.local_embedding hx hx1'⟩
  have hsimple := h.simple
  have hstrong := theoremTwo _ _ _ hloc (hb.centralSylow hx)
  rw [involutionPointHull_eq_top hx1'] at hstrong
  exact h.false_of_fusionStronglyEmbedded_map (fusionStronglyEmbedded_of_subgroupOf_top hstrong)

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
