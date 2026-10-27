module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoListGammaMcL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryOvergroup
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def KFactTenFourteenTwoA5GammaJFour : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) (K₁ J : Subgroup K),
    p.Prime → p ≠ 2 →
    (∃ i : TauCeti.CFSGIndex, RankOneCent.IsTenFourteenOneIndex p i ∧
      (∀ h, i ≠ .alternating 10 h) ∧ (∀ d m, i = .lie d → d.1 ≠ .reeG2 m) ∧
      i ≠ .sporadic .McL ∧ (∀ d, i = .lie d → ¬ IsUnitaryIndex p d) ∧
      Nonempty (K ≃* i.Group)) → center K = ⊥ →
    ¬ IsCaseTwoGroup p K → (∀ [Fact p.Prime] (a : ℕ), 2 ≤ a → IsEmpty (K ≃* PSL2GF p a)) →
    (RankOneCent.StepThreeGroup p K → IsEmpty (K ≃* alternatingGroup (Fin 10)) →
      ¬ (IsElemAbelian p (T : Subgroup K) ∧ Nat.card (T : Subgroup K) = p ^ 2)) →
    CFSG.Open.pRank p (T : Subgroup K) ≤ 2 → RankOneCent.narrowGamma p (T : Subgroup K) ≤ K₁ →
    K₁ ≠ ⊤ → IsSubnormal J K₁ → ⁅J, J⁆ = J → J ≠ ⊥ →
    (∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) →
    p = 5 ∧ Nonempty (J ≃* alternatingGroup (Fin 5))

theorem kFactTenFourteenTwoA5GammaUThreeJFour_of_jFour (hR : KFactTenFourteenTwoA5GammaJFour) :
    KFactTenFourteenTwoA5GammaUThreeJFour := by
  intro p K _ _ T K₁ J hp hp2 hL hZ hC2 hL2 hS3 hrank hΓ hK₁ hJs hJp hJ1 hJirr
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, hi10, hRee, hMcL, ⟨e⟩⟩ := hL
  by_cases hU : ∃ d, i = .lie d ∧ IsUnitaryIndex p d
  · exfalso
    obtain ⟨d, rfl, hd⟩ := hU
    have h : Nonempty (K ≃* CatGroup d) := ⟨e⟩
    obtain ⟨-, hf, -⟩ := UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
    obtain ⟨-, -, -, E, hET, hE, hEc⟩ := kFactUnitarySylowStructure K p d hp2 hd h T
    have hEne : E ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hEc
      have : 1 < p ^ (2 * d.1.fieldExponent) := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    haveI : Nontrivial (T : Subgroup K) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 fun h0 => hEne (eq_bot_iff.2 (h0 ▸ hET))
    haveI : Nontrivial (center (T : Subgroup K)) := T.isPGroup'.center_nontrivial
    obtain ⟨n, hn0, hnc⟩ :=
      (T.isPGroup'.to_subgroup (center (T : Subgroup K))).nontrivial_iff_card.1 inferInstance
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p (hnc ▸ dvd_pow_self p hn0.ne')
    have hzT : ((g : (T : Subgroup K)) : K) ∈ (T : Subgroup K) := (g : (T : Subgroup K)).2
    have hoz : orderOf ((g : (T : Subgroup K)) : K) = p := by
      simp only [Subgroup.orderOf_coe]
      exact hg
    have hTz : (T : Subgroup K) ≤ centralizer {((g : (T : Subgroup K)) : K)} := by
      intro t ht
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_center_iff.1 g.2 ⟨t, ht⟩)
    have h2 : 2 ≤ CFSG.Open.pRank p ((T : Subgroup K) ⊓
        centralizer {((g : (T : Subgroup K)) : K)}) :=
      le_trans (by omega)
        (CFSG.SectionRank.le_pRank hp.one_lt (le_inf hET (hET.trans hTz)) hE hEc)
    have hTK₁ := hTz.trans ((RankOneCent.centralizer_le_narrowGamma hzT hoz h2).trans hΓ)
    haveI := UnitaryModel.isSolvable_of_unitary_sylow_le hd h T hTK₁ hK₁
    haveI : Group.IsSolvable J :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hJs.le)
    haveI : Group.IsPerfect J :=
      (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq J).mpr hJp
    haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot _).2 hJ1
    have hlt := IsSolvable.commutator_lt_of_ne_bot (G := J) (H := ⊤) top_ne_bot
    rw [show ⁅(⊤ : Subgroup J), ⊤⁆ = ⊤ from
      (inferInstance : Group.IsPerfect J).commutator_eq_top] at hlt
    exact lt_irrefl _ hlt
  refine hR p K T K₁ J hp hp2 ⟨i, hi, hi10, hRee, hMcL, fun d hd hdU => hU ⟨d, hd, hdU⟩, ⟨e⟩⟩
    hZ hC2 hL2 hS3 hrank hΓ hK₁ hJs hJp hJ1 hJirr

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
