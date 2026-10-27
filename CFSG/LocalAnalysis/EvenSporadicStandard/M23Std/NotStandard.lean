module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NoFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23SquaresNoncomm
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.A7SylowProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarDichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarKGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23SetupFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.CentralFinal

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem not_dvd_card_of_isSporadic_M23 {Y : Type} [Group Y]
    (hY : IsSporadic Y .M23) :
    ¬ 256 ∣ Nat.card Y := by
  obtain ⟨e⟩ := hY
  have hM : Nat.card (Carrier .M23) = 10200960 := CFSG.Sporadic.Schreier.m23_card
  rw [Nat.card_congr e.toEquiv, hM]
  norm_num

theorem m23_not_standard_of_solomon
    (hSol : SolomonZ2A7)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) :
    ¬ IsSporadic L .M23 := by
  intro hL
  have := h.simple
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_M23 hL
  have hq : IsSporadic (L ⧸ center L) .M23 := isSporadic_quotient_of_center_eq_bot hZ hL
  have hfull := HypOne.M23.fullRowData_of_isSporadic hq
  have hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q :=
    HypOne.M23.allInner_of_isSporadic hq
  have hS := h.card_sylow_eq_two_of_inner hfull.rowData.hypothesisOne hinn
  obtain ⟨z, hz, hz2⟩ : ∃ z ∈ centralizer (L : Set G), orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 (centralizer (L : Set G))))
    have hdvd : 2 ∣ Nat.card (centralizer (L : Set G)) :=
      (hS Q) ▸ Subgroup.card_subgroup_dvd_card (Q : Subgroup (centralizer (L : Set G)))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  obtain ⟨t, F, L1, N, htL, S, hnc, -, hA7, hFix⟩ := m23_setupFix h hL hz hz2
  rcases S.xbar_dichotomy hSol (S.isKGroupCat_xbar h) hA7 with hcen |
      ⟨N1, N2, hN1, hN2, hcomm, hdisj, hnorm, hidx, hz0, hconj⟩
  · exact S.false_of_central h.nonabelian hFix hA7 (not_dvd_card_of_isSporadic_M23 hL) hnc hcen
  · have hL2 := not_dvd_card_of_isSporadic_M23 hL
    obtain ⟨P, hP, hzP, hT⟩ := S.exists_sylow_X hL2
    obtain ⟨g, hg⟩ := S.exists_conj_mem_preimage_of_wreath h.nonabelian hcomm hdisj hnorm hidx hz0
      hconj hP hzP hT
    have hzz : z * z = 1 := S.one.z_mul_self
    have hy2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
      calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hzz]; group
    exact S.false_of_isConj_mem_preimage hnc (m23_rankFour hL) hL2 hnorm
      (fun S' hS' => m23_sylow_squares_noncomm h hL hz hz2 hS')
      (fun T hT' y hy hy2' => sylow_prod_centralizer hN1 hN2 hcomm hdisj hT' hy hy2')
      (mem_inf.1 hg).2 hy2 (isConj_iff.2 ⟨g⁻¹, by group⟩)

end CFSG.EvenSporadicStandard.M23Std
