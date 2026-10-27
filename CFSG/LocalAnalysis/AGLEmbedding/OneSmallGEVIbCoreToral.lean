module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSplit
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbCore

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem false_of_le_rPart_of_elem (hc : D1IbCore p P M H R Rbar K z) (hB : D1IbBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hR : R ≤ rPart M R (barM M L))
    {E₃ : Subgroup G} (hE₃R : E₃ ≤ R) (hEel : IsElemAbelian p (barM M E₃))
    (hEcard : Nat.card (barM M E₃) = p ^ 3) :
    False := by
  have hp := hc.prime
  have hp5 := hc.five_le
  have hRM := hc.phase.le_M
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set zb := mkM ⟨z, hc.mem_M⟩
  set PL := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)
  set E := barM M E₃
  have hEL : E ≤ barM M L := by
    rintro _ ⟨r, hr, rfl⟩
    have hrR := hE₃R (Subgroup.mem_subgroupOf.mp hr)
    exact (mem_rPart hRM hrR).mp (hR hrR)
  have hzbL : zb ∈ barM M L := (mem_rPart hRM hc.elt.1).mp (hR hc.elt.1)
  have hEC : E ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hc.le_centralizer (hE₃R (Subgroup.mem_subgroupOf.mp hr)))))
  have hEP : E ≤ PL := fun e he => hc.zbar_fixed_le L e (hEL he) (by
    show zb * e * zb⁻¹ = e
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEC he), mul_inv_cancel_right])
  have hPLs := hc.perf_block hL
  have hperf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ PL → ⁅V, V⁆ = V →
      ¬ p ^ 3 ∣ Nat.card V := fun V hV hVp h3 =>
    hPLs V hV hVp ((pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans h3)
  have hdvdP : p ^ 3 ∣ Nat.card PL := hEcard ▸ Subgroup.card_dvd_of_le hEP
  have hdvdL : p ^ 3 ∣ Nat.card (barM M L) := hEcard ▸ Subgroup.card_dvd_of_le hEL
  have hn1 := hc.phase.nineThree_not_one hB.h85 hB.hD2 hL
  rcases hc.phase.nineThree hB.h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1.1
  · obtain ⟨V, hVp, hVL, hVO, hzV⟩ := hc.exists_cover_block hL
    have hVO' : V ≤ Subgroup.normalizer (pCoreOf 2 PL : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [← h2.2.2]
      exact hVO
    exact hB.hTA _ (barM M L) PL hL.component h2.1 h2.2.1 (hc.phase.barM_ne_of_isWeakSBlock hL)
      (ne_inf_normalizer_of_nineThreeTwo h2 (hn1.2 h2)) p hp hp5 hPLs zb hzbL hc.zbar_pow
      (hc.zbar_not_mem_centralizer hL) ⟨V, hVp, hVL, hVO', hzV⟩ (hc.zbar_fixed_le L)
      ⟨E, le_inf hEL hEC, hEel, hEcard⟩
  · exact hB.hC3T G M (pCoreOf 2 H) L p hc.phase.isKGroup.1 hc.phase.asc81bHyp hL hn1.1
      (hc.phase.not_isSylowTwoOf_inf hB.h85 hB.hD2 hL) h3 hp hp5 hPLs E hEP hEel hEcard
  · obtain ⟨-, hZ, ⟨e⟩, -⟩ := h4
    have hcard : Nat.card (barM M L) = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(barM M L)), hZ,
        Nat.card_congr e.toEquiv]
      have := two_mul_card_alternatingGroup_fin (n := 6) (by norm_num)
      rw [show Nat.factorial 6 = 720 by rfl] at this
      omega
    exact (not_pow_three_dvd_of_five_le hp hp5).1 (hcard ▸ hdvdL)
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    have hcard : Nat.card (barM M L) = 2520 := by
      rw [Nat.card_congr e.toEquiv]
      have := two_mul_card_alternatingGroup_fin (n := 7) (by norm_num)
      rw [show Nat.factorial 7 = 5040 by rfl] at this
      omega
    exact (not_pow_three_dvd_of_five_le hp hp5).2 (hcard ▸ hdvdL)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact false_of_quotient_perm hp hp5 hperf e hdvdP
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact false_of_quotient_perm hp hp5 hperf e hdvdP
  · obtain ⟨-, N, r, -, -, -, -, -, -, φ, -⟩ := h8
    exact false_of_quotient_perm_prod hp hp5 hperf φ hdvdP

end D1IbCore

end CFSG.AGLEmbedding
