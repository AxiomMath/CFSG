module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoListGammaRest
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLCentOver
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def KFactTenFourteenTwoA5GammaUThreeJFour : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) (K₁ J : Subgroup K),
    p.Prime → p ≠ 2 →
    (∃ i : TauCeti.CFSGIndex, RankOneCent.IsTenFourteenOneIndex p i ∧
      (∀ h, i ≠ .alternating 10 h) ∧ (∀ d m, i = .lie d → d.1 ≠ .reeG2 m) ∧
      i ≠ .sporadic .McL ∧ Nonempty (K ≃* i.Group)) → center K = ⊥ →
    ¬ IsCaseTwoGroup p K → (∀ [Fact p.Prime] (a : ℕ), 2 ≤ a → IsEmpty (K ≃* PSL2GF p a)) →
    (RankOneCent.StepThreeGroup p K → IsEmpty (K ≃* alternatingGroup (Fin 10)) →
      ¬ (IsElemAbelian p (T : Subgroup K) ∧ Nat.card (T : Subgroup K) = p ^ 2)) →
    CFSG.Open.pRank p (T : Subgroup K) ≤ 2 → RankOneCent.narrowGamma p (T : Subgroup K) ≤ K₁ →
    K₁ ≠ ⊤ → IsSubnormal J K₁ → ⁅J, J⁆ = J → J ≠ ⊥ →
    (∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) →
    p = 5 ∧ Nonempty (J ≃* alternatingGroup (Fin 5))

theorem kFactTenFourteenTwoA5GammaRest_of_uThreeJFour
    (hR : KFactTenFourteenTwoA5GammaUThreeJFour) :
    KFactTenFourteenTwoA5GammaRest := by
  intro p K _ _ T K₁ J hp hp2 hL hZ hC2 hL2 hS3 hrank hΓ hK₁ hJs hJp hJ1 hJirr
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, hi10, hRee, ⟨e⟩⟩ := hL
  by_cases hMcL : i = .sporadic .McL
  · exfalso
    subst hMcL
    have hp5 : p = 5 := by
      rcases hi with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
      all_goals first | exact h | cases h
    subst hp5
    obtain ⟨⟨z, hzT, hz1, hTz, hY⟩, hH⟩ :=
      CFSG.AGLEmbeddingD2.centOverLocal_of_mulEquiv_mcl e T
    have hexp : ∀ r ∈ (T : Subgroup K), r ^ 5 = 1 := hH.2.2.2.2.2.1
    have hoz : orderOf z = 5 := orderOf_eq_prime (hexp z hzT) hz1
    have hTnc : ¬ IsCyclic (T : Subgroup K) := by
      intro hcyc
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (T : Subgroup K))
      have hg5 : g ^ 5 = 1 := Subtype.ext (by simpa using hexp _ g.2)
      have hdvd := orderOf_dvd_of_pow_eq_one hg5
      rw [hg, hH.1] at hdvd
      norm_num at hdvd
    obtain ⟨E, hET, hE, hEc⟩ :=
      GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic hp2 T.isPGroup' hTnc
    have h2 := CFSG.SectionRank.le_pRank (by norm_num) (le_inf hET (hET.trans hTz)) hE hEc
    have hCK₁ := (RankOneCent.centralizer_le_narrowGamma hzT hoz h2).trans hΓ
    rcases hY K₁ hCK₁ with h | h
    · apply hJ1
      haveI := hH.2.2.2.2.2.2.1
      haveI : Group.IsSolvable J :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective (hJs.le.trans h))
      haveI : Group.IsPerfect J :=
        (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq J).mpr hJp
      obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable J).solvable
      have htop : ∀ k, derivedSeries J k = ⊤ := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [derivedSeries_succ, ih]
          exact (inferInstance : Group.IsPerfect J).commutator_eq_top
      rw [htop n] at hn
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : J) ∈ (⊥ : Subgroup J) := hn ▸ mem_top _
      exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp this))
    · exact hK₁ h
  exact hR p K T K₁ J hp hp2 ⟨i, hi, hi10, hRee, hMcL, ⟨e⟩⟩ hZ hC2 hL2 hS3 hrank hΓ hK₁ hJs hJp
    hJ1 hJirr

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
