module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightComponents
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOf
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isTwoPrimeComponent {M J J₁ : Subgroup G}
    (hJ : IsTwoPrimeComponent M J) (hJ₁ : IsTwoPrimeComponent M J₁) :
    J₁ ≤ normalizer (J : Set G) := by
  by_cases h : J = J₁
  · subst h
    exact Subgroup.le_normalizer
  · refine hJ.le_normalizer (S := J₁) (fun x hx => ?_) hJ₁.le
    exact Subgroup.centralizer_le_normalizer _ (TenTenClaim.barM_le_centralizer hJ hJ₁ h hx)

theorem pCoreOf_ne_bot_of_three_dvd (hchar : IsCharTwoType G) {M J : Subgroup G}
    (hM : IsTwoLocal M) (hJ : IsTwoPrimeComponent M J) (h3 : 3 ∣ Nat.card J) :
    pCoreOf 2 J ≠ ⊥ := by
  intro hbot
  have hVJ : pCoreOf 2 M ≤ normalizer (J : Set G) :=
    TenTenNormI.pCoreOf_le_normalizer hJ.le hJ.subnormal hJ.perfect
  have hJ2 : J ⊓ pCoreOf 2 M = ⊥ := hJ.inf_twoCore.trans hbot
  have hcen : J ≤ M ⊓ centralizer (pCoreOf 2 M : Set G) := by
    intro j hj
    refine ⟨hJ.le hj, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 : v * j⁻¹ * v⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hVJ hv) j⁻¹).mp (J.inv_mem hj)
    have h2 : j * v * j⁻¹ * v⁻¹ ∈ pCoreOf 2 M :=
      (pCoreOf 2 M).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (localGroup_le_normalizer_pCoreOf 2 M (hJ.le hj)) v).mp hv) ((pCoreOf 2 M).inv_mem hv)
    have h3' : j * v * j⁻¹ * v⁻¹ ∈ J := by
      have := J.mul_mem hj h1
      rwa [show j * (v * j⁻¹ * v⁻¹) = j * v * j⁻¹ * v⁻¹ by group] at this
    have h4 : j * v * j⁻¹ * v⁻¹ ∈ J ⊓ pCoreOf 2 M := ⟨h3', h2⟩
    rw [hJ2, Subgroup.mem_bot] at h4
    have h5 := mul_inv_eq_one.mp h4
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm
  have hJle : J ≤ pCoreOf 2 M := hcen.trans (hchar M hM)
  have hJbot : J ≤ J ⊓ pCoreOf 2 M := le_inf le_rfl hJle
  rw [hJ2] at hJbot
  rw [le_bot_iff.mp hJbot, Subgroup.card_bot] at h3
  omega

theorem exists_isAGLQ_le_normalizer {p : ℕ} {P : Sylow p G} {M H₁ R₁ Q J : Subgroup G}
    (hS : Setting G) (he : D1Escape p P M H₁ R₁) (hQ : IsAGLQ p M Q)
    (hJ : IsTwoPrimeComponent M J) (h3 : 3 ∣ Nat.card J) :
    ∃ B : Subgroup G, IsAGLQ p M B ∧ B ≤ normalizer (J : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : p.Prime := he.prime
  have hp2 : p ≠ 2 := he.ne_two
  obtain ⟨e, heJ, he3, hnc⟩ := exists_noncentral_of_two_component hJ h3
  have hrkM : CFSG.Open.pRank 3 M ≤ 3 := by
    have h := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M he.maxTwoLocal_M.1
    rw [hS.rank] at h
    exact h
  have hQM : Q ≤ M := hQ.1
  have hQp : IsPGroup p Q := hQ.2.1
  have hVN : pCoreOf 2 M ≤ normalizer (J : Set G) :=
    TenTenNormI.pCoreOf_le_normalizer hJ.le hJ.subnormal hJ.perfect
  have hconjN : ∀ g ∈ M, J.map (MulAut.conj g).toMonoidHom ≤ normalizer (J : Set G) :=
    fun g hg => le_normalizer_of_isTwoPrimeComponent hJ (hJ.map_conj hg)
  have hconjM : ∀ g ∈ M, J.map (MulAut.conj g).toMonoidHom ≤ M :=
    fun g hg => (hJ.map_conj hg).le
  by_cases hall : ∀ q ∈ Q, J.map (MulAut.conj q).toMonoidHom = J
  · exact ⟨Q, hQ, fun q hq => mem_normalizer_iff_map_conj_eq.mpr (hall q hq)⟩
  push Not at hall
  obtain ⟨q, hq, hqJ⟩ := hall
  obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
  have hk' : q ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdist : ∀ {n : ℕ} (i j : Fin n), n ≤ p → i ≠ j →
      J.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom ≠
        J.map (MulAut.conj (q ^ (j : ℕ))).toMonoidHom := by
    intro n i j hn hij
    have hne' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · exact TenTenClaim.map_conj_pow_inj hp hk' hqJ h (lt_of_lt_of_le j.isLt hn)
    · exact (TenTenClaim.map_conj_pow_inj hp hk' hqJ h (lt_of_lt_of_le i.isLt hn)).symm
  have hg : ∀ {n : ℕ} (i : Fin n), q ^ (i : ℕ) ∈ M := fun i => M.pow_mem (hQM hq) _
  rcases eq_or_ne p 3 with rfl | hp3
  · obtain ⟨E, hEcl, hE, hEcard⟩ := TenTenClaim.exists_E_conj hJ heJ he3 hnc 3
      (fun i => q ^ (i : ℕ)) (fun i => hg i) (fun i j hij => hdist i j le_rfl hij)
    set W : Subgroup G :=
      (⨆ i : Fin 3, J.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom) ⊔ pCoreOf 2 M with hW
    have hWM : W ≤ M :=
      sup_le (iSup_le fun i => hconjM _ (hg i)) (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    have hWN : W ≤ normalizer (J : Set G) := sup_le (iSup_le fun i => hconjN _ (hg i)) hVN
    have hEW : E ≤ barM M W := by
      refine hEcl.trans ?_
      rw [closure_le]
      rintro _ ⟨i, rfl⟩
      exact barM_mono (le_sup_of_le_left (le_iSup _ i))
        (TenTenClaim.conj_noncentral heJ he3 hnc (hg i)).1
    obtain ⟨Q₀, hQ₀W, hQ₀, hQ₀card⟩ := TenTenClaim.exists_elemAbelian_lift hWM hE hEW
    refine ⟨Q₀, ⟨hQ₀W.trans hWM, fun x => ⟨1, Subtype.ext (by simpa using hQ₀.2 _ x.2)⟩,
      Or.inl ?_⟩, hQ₀W.trans hWN⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hQ₀ (hQ₀card.trans hEcard)
  · exfalso
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra h
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by decide)
    have h4 := TenTenClaim.le_pRank_of_conj hJ heJ he3 hnc 4 (fun i => q ^ (i : ℕ))
      (fun i => hg i) (fun i j hij => hdist i j (by omega) hij)
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
