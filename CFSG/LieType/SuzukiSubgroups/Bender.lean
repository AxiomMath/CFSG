module

public import CFSG.LieType.SuzukiSubgroups.Facts
public import CFSG.LieType.SuzukiSubgroups.Generic
public import CFSG.Goldschmidt.Steps.G32QSz8
public import CFSG.Holt.BenderBasic
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz

public section

namespace CFSG.LieType.SuzukiSubgroups

open CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem.CatalogBridge

variable {n : ℕ} {H : Type} [Group H] [Finite H]

private theorem isElemAbelian_subgroupOf_four {U E : Subgroup H} (hEU : E ≤ U)
    (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4) :
    IsElemAbelian 2 (E.subgroupOf U) ∧ Nat.card (E.subgroupOf U) = 4 :=
  ⟨hE.subgroupOf U, by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEU).toEquiv, hE4]⟩

private theorem eq_bot_of_normal_odd_of_isSz (hH : CFSG.Quasithin.IsSz n H)
    {U E : Subgroup H} (hEU : E ≤ U) (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4)
    {M : Subgroup ↥U} (hMnorm : M.Normal) (hModd : Odd (Nat.card M)) : M = ⊥ := by
  haveI := hMnorm
  obtain ⟨hV, hcardV⟩ := isElemAbelian_subgroupOf_four hEU hE hE4
  refine eq_bot_of_elemAbelian_four (G := ↥U) (M := M) (E := E.subgroupOf U)
    Subgroup.le_normalizer_of_normal hV hcardV ?_
  intro e he he1 m hm hcomm
  have heE : (e : H) ∈ E := he
  have he2 : orderOf (e : H) = 2 :=
    orderOf_eq_prime (hE.2 (e : H) heE) fun h => he1 (Subtype.ext h)
  have hmemC : (m : H) ∈ centralizer ({(e : H)} : Set H) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun x : ↥U => (x : H)) hcomm.symm
  have hmH1 : (m : H) = 1 := by
    by_contra hm1
    have h2dvd : 2 ∣ orderOf (m : H) := by
      have hcent := isPGroup_centralizer_of_isSz hH he2
      have hdvd : 2 ∣ orderOf (⟨(m : H), hmemC⟩ :
          ↥(centralizer ({(e : H)} : Set H))) :=
        hcent.dvd_orderOf fun h => hm1 (congrArg Subtype.val h)
      rwa [← Subgroup.orderOf_coe] at hdvd
    have hodd : Odd (orderOf (m : H)) := by
      refine Odd.of_dvd_nat hModd ?_
      rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk m hm]
      exact orderOf_dvd_natCard (⟨m, hm⟩ : M)
    exact hodd.not_two_dvd_nat h2dvd
  exact Subtype.ext hmH1

theorem exists_normal_sz_of_forall_not_le
    (hH : CFSG.Quasithin.IsSz n H) {U E : Subgroup H}
    (hEU : E ≤ U) (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4)
    (hU : ∀ Q : Sylow 2 H, ¬ U ≤ normalizer ((Q : Subgroup H) : Set H)) :
    ∃ N : Subgroup ↥U, N.Normal ∧ Odd N.index ∧ ∃ a : ℕ, 1 ≤ a ∧ Nonempty (↥N ≃* ↥(Sz a)) := by
  obtain ⟨u, huE, hu1⟩ := CFSG.Holt.exists_mem_ne_one_of_card_eq_four hE4
  have hu2 : orderOf u = 2 := orderOf_eq_prime (hE.2 u huE) hu1
  obtain ⟨Q, hEQ⟩ := hE.isPGroup.exists_le_sylow
  have huU : u ∈ U := hEU huE
  have huB : u ∈ normalizer ((Q : Subgroup H) : Set H) :=
    (Q : Subgroup H).le_normalizer (hEQ huE)
  let B : Subgroup ↥U := (normalizer ((Q : Subgroup H) : Set H)).subgroupOf U
  have hSE : fusionStronglyEmbedded B :=
    CFSG.Goldschmidt.G32Q.fusionStronglyEmbedded_subgroupOf
      (B := normalizer ((Q : Subgroup H) : Set H)) (M := U)
      (fusionBenderBorel_of_isSz hH Q).1 (hU Q) huU huB hu2
  rcases CFSG.Open.bender_strongly_embedded_normal_series ↥U B hSE with hlow |
    ⟨M, N, hMnorm, hNnorm, hMNnorm, _, hModd, hNodd, hK⟩
  · exfalso
    obtain ⟨hV, hcardV⟩ := isElemAbelian_subgroupOf_four hEU hE hE4
    exact (CFSG.Holt.not_forall_sylow_cyclic_or_quaternion hcardV hV.2) hlow
  · have hMbot : M = ⊥ := eq_bot_of_normal_odd_of_isSz hH hEU hE hE4 hMnorm hModd
    have hMsub : M.subgroupOf N = ⊥ := by rw [hMbot, Subgroup.bot_subgroupOf]
    haveI : (M.subgroupOf N).Normal := hMNnorm
    have eN : (N ⧸ M.subgroupOf N) ≃* ↥N :=
      (QuotientGroup.quotientMulEquivOfEq hMsub).trans QuotientGroup.quotientBot
    have h3 : ¬ 3 ∣ Nat.card (N ⧸ M.subgroupOf N) := by
      intro h
      apply not_three_dvd_card_of_isSz hH
      rw [Nat.card_congr eN.toEquiv] at h
      exact (h.trans (Subgroup.card_subgroup_dvd_card N)).trans
        (Subgroup.card_subgroup_dvd_card U)
    rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact (h3 ((Nat.card_congr e.toEquiv).symm ▸ three_dvd_card_psl2_two_pow (by omega))).elim
    · exact (h3 ((Nat.card_congr e.toEquiv).symm ▸ three_dvd_card_psu3 (by omega))).elim
    · exact ⟨N, hNnorm, hNodd, a, ha, ⟨eN.symm.trans e⟩⟩

end CFSG.LieType.SuzukiSubgroups
