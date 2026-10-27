module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoListGammaU3
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoJ4Normalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowCriteria
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.Sporadic.Schreier.J4SEleven

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open CFSG.AGLEmbedding Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem normalizer_le_narrowGamma_jFour
    {K : Type} [Group K] [Finite K] (e : K ≃* (TauCeti.CFSGIndex.sporadic .J4).Group)
    (T : Sylow 11 K) :
    normalizer ((T : Subgroup K) : Set K) ≤ RankOneCent.narrowGamma 11 (T : Subgroup K) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let eKJ : K ≃* CFSG.Sporadic.J4.J :=
    e.trans ((CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv.some).symm.trans
      (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat))
  haveI hfinJ : Finite CFSG.Sporadic.J4.J := Finite.of_equiv K eKJ.toEquiv
  obtain ⟨Ψ, hΨ⟩ := @exists_mulEquiv_map_eq_sylow CFSG.Sporadic.J4.J K (Subgroup.toGroup _)
    hfinJ _ eKJ.symm 11 _ (T : Subgroup K) T.isPGroup' T.not_dvd_index
    CFSG.Sporadic.J4Schreier.Q11Sylow
  have hT : (T : Subgroup K) =
      (CFSG.Sporadic.J4Schreier.Q11Sylow : Subgroup _).map Ψ.symm.toMonoidHom := by
    rw [hΨ]
    ext x
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  rw [hT, ← Subgroup.map_equiv_normalizer_eq]
  refine (Subgroup.map_mono ?_).trans
    (@RankOneCent.narrowGamma_map_le 11 _ K (Subgroup.toGroup _) hfinJ _ _ (by norm_num)
      Ψ.symm _)
  rw [CFSG.Sporadic.J4Schreier.Q11Sylow_coe]
  exact J4Gamma.normalizer_Q11_le_narrowGamma

theorem isSolvable_of_narrowGamma_le_jFour
    {K : Type} [Group K] [Finite K] (e : K ≃* (TauCeti.CFSGIndex.sporadic .J4).Group)
    (hZ : center K = ⊥) (T : Sylow 11 K) {K₁ : Subgroup K}
    (hΓ : RankOneCent.narrowGamma 11 (T : Subgroup K) ≤ K₁) (hK₁ : K₁ ≠ ⊤) :
    Group.IsSolvable K₁ := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hC : centralizer ((⊤ : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]
  obtain ⟨-, -, hmax, -, -, -, -, hsolv, -⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4 K ⊤ Subgroup.normal_top hC
      ⟨Subgroup.topEquiv.trans e⟩ 11 rfl T
  rcases hmax K₁ ((normalizer_le_narrowGamma_jFour e T).trans hΓ) with h | h
  · exact h ▸ hsolv
  · exact absurd h hK₁

@[expose] def KFactTenFourteenTwoA5GammaExcluded : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) (K₁ J : Subgroup K),
    p.Prime → p ≠ 2 →
    (∃ i : TauCeti.CFSGIndex, RankOneCent.IsTenFourteenOneIndex p i ∧
      (∀ h, i ≠ .alternating 10 h) ∧ (∀ d m, i = .lie d → d.1 ≠ .reeG2 m) ∧
      i ≠ .sporadic .McL ∧ (∀ d, i = .lie d → ¬ IsUnitaryIndex p d) ∧ i ≠ .sporadic .J4 ∧
      Nonempty (K ≃* i.Group)) → center K = ⊥ →
    ¬ IsCaseTwoGroup p K → (∀ [Fact p.Prime] (a : ℕ), 2 ≤ a → IsEmpty (K ≃* PSL2GF p a)) →
    (RankOneCent.StepThreeGroup p K → IsEmpty (K ≃* alternatingGroup (Fin 10)) →
      ¬ (IsElemAbelian p (T : Subgroup K) ∧ Nat.card (T : Subgroup K) = p ^ 2)) →
    CFSG.Open.pRank p (T : Subgroup K) ≤ 2 → RankOneCent.narrowGamma p (T : Subgroup K) ≤ K₁ →
    K₁ ≠ ⊤ → IsSubnormal J K₁ → ⁅J, J⁆ = J → J ≠ ⊥ →
    (∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) →
    p = 5 ∧ Nonempty (J ≃* alternatingGroup (Fin 5))

theorem kFactTenFourteenTwoA5GammaJFour_of_excluded
    (hR : KFactTenFourteenTwoA5GammaExcluded) : KFactTenFourteenTwoA5GammaJFour := by
  intro p K _ _ T K₁ J hp hp2 hL hZ hC2 hL2 hS3 hrank hΓ hK₁ hJs hJp hJ1 hJirr
  obtain ⟨i, hi, hi10, hRee, hMcL, hU, ⟨e⟩⟩ := hL
  by_cases hJ4 : i = .sporadic .J4
  · exfalso
    subst hJ4
    have hp11 : p = 11 := by
      simp only [RankOneCent.IsTenFourteenOneIndex] at hi
      rcases hi with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h
    subst hp11
    haveI := isSolvable_of_narrowGamma_le_jFour e hZ T hΓ hK₁
    haveI : Group.IsSolvable J :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hJs.le)
    haveI : Group.IsPerfect J :=
      (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq J).mpr hJp
    haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot _).2 hJ1
    have hlt := IsSolvable.commutator_lt_of_ne_bot (G := J) (H := ⊤) top_ne_bot
    rw [show ⁅(⊤ : Subgroup J), ⊤⁆ = ⊤ from
      (inferInstance : Group.IsPerfect J).commutator_eq_top] at hlt
    exact lt_irrefl _ hlt
  exact hR p K T K₁ J hp hp2 ⟨i, hi, hi10, hRee, hMcL, hU, hJ4, ⟨e⟩⟩
    hZ hC2 hL2 hS3 hrank hΓ hK₁ hJs hJp hJ1 hJirr

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
