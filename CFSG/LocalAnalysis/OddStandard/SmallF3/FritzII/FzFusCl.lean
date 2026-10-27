module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusLab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusLet
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusRow
public import Certificates.Data.FzFusN2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzJ36 Certificates.FzFus

variable {G : Type} [Group G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G} {π : Model →* G}

theorem fzfus_classes [Finite G] [IsSimpleGroup G] (hA : Fz722c)
    (hC : ClassFact) (hR : RowsFact) (hS : SubsFact)
    (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂)
    (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) :
    ConjClasses.mk t ≠ ConjClasses.mk ((x₁ * x₂) ^ 2) ∧ ConjClasses.mk tau = ConjClasses.mk t ∧
      ConjClasses.mk (t * tau) = ConjClasses.mk t ∧
      (∀ c ∈ rzList, ConjClasses.mk (π (rep c)) = ConjClasses.mk t) ∧
      ConjClasses.mk (π (rep .oI)) = ConjClasses.mk t ∧
      ConjClasses.mk (π (rep .oJ)) = ConjClasses.mk t ∧
      ConjClasses.mk (π (rep .oK)) = ConjClasses.mk t := by
  obtain ⟨ht2, -, -, h12⟩ := fzFus_rels h
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have ht1 : t ≠ 1 := fun h1 => by
    have := h.ctx.hyp.ord_t
    rw [h1, orderOf_one] at this
    omega
  have hRZ : ∀ c ∈ rzList, ConjClasses.mk (π (rep c)) ≠ ConjClasses.mk ((x₁ * x₂) ^ 2) := by
    intro c hc heq
    obtain ⟨hinv, -, -, -, n, hn⟩ := rz_rep_facts c hc
    have hiR : π (rep c) ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ := hd.mem_fzR6_iff.mpr ⟨n, by rw [hn]⟩
    have hi2 : π (rep c) ^ 2 = 1 := by rw [pow_two]; exact ((hd.isInvM_iff _).mp hinv).1
    exact hA G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ h _ hiR hi2 (fzfus_rep_not_four hd h12 hc)
      (ConjClasses.mk_eq_mk_iff_isConj.mp heq).symm
  have hIII : ConjClasses.mk (π (rep .III)) = ConjClasses.mk t := by
    show ConjClasses.mk (π tM) = _
    rw [hd.t_eq]
  have hTZ : ConjClasses.mk t ≠ ConjClasses.mk ((x₁ * x₂) ^ 2) := fun heq =>
    hRZ .III (by decide) (hIII.trans heq)
  obtain ⟨hL1a, hL1b, hL1c⟩ := fzfus_L1 h hd
  have hL2 := fzfus_L2 h hd
  obtain ⟨hL3a, hL3b⟩ := fzfus_L3 h hd
  have hcard : 2 < Nat.card G := by
    have h1 : Nat.card T₂ ≤ Nat.card G := Subgroup.card_le_card_group T₂
    rw [h.shape.card] at h1
    have : (2 : ℕ) ^ 9 = 512 := by norm_num
    omega
  have htT : t ∈ T₂ := hd.mem_T₂_iff.mpr ⟨tM, hd.t_eq⟩
  have trans : ∀ s ∈ subTable, ∃ c ∈ s.2.2, ConjClasses.mk (π (rep c)) = ConjClasses.mk t := by
    intro s hs
    have hker : ∀ m, π m = 1 → phi s.1 s.2.1 m = 1 := fun m hm =>
      phi_keq_one _ _ ((hd.eq_one_iff m).mp hm)
    obtain ⟨m, hm, a, ham⟩ := fzfus_transfer h.sylow hcard π hd.range_eq (phi s.1 s.2.1) hker
      (phi_surj_tbl s hs) htT htt
    have hmm : IsInvM m := by
      rw [hd.isInvM_iff, ← ham]
      refine ⟨?_, fun h1 => ht1 ?_⟩
      · calc a⁻¹ * t * a * (a⁻¹ * t * a) = a⁻¹ * (t * t) * a := by group
          _ = 1 := by rw [htt]; group
      · calc t = a * (a⁻¹ * t * a) * a⁻¹ := by group
          _ = 1 := by rw [h1]; group
    refine ⟨clsOf m, hS s hs m hmm hm, (hd.cl_eq hC hmm).symm.trans ?_⟩
    rw [← ham]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨a, by group⟩)
  have cj : ∀ {a b : G}, IsConj a b → ConjClasses.mk b = ConjClasses.mk a := fun hab =>
    ConjClasses.mk_eq_mk_iff_isConj.mpr hab.symm
  have key := fzFus_logic (fun c => ConjClasses.mk (π (rep c))) (ConjClasses.mk t)
    (ConjClasses.mk ((x₁ * x₂) ^ 2)) (ConjClasses.mk tau) (ConjClasses.mk (t * tau)) hTZ hRZ
    ⟨cj hL1a, cj hL1b, cj hL1c⟩ hIII (cj hL2) (hL3a.imp cj cj) (hL3b.imp cj cj)
    (fzfus_rows hC hR h hd) trans
  obtain ⟨hA', hB', hrz, hoI, hoJ, hoK⟩ := key
  exact ⟨hTZ, hA', hB', hrz, hoI, hoJ, hoK⟩

end CFSG.OddStandard.SmallF3.FritzII
