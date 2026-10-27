module

public import CFSG.Quasithin.Vol2.Ch12Sec2Thm
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec1Setup
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Cases
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

theorem stmt12_2_2_of_inputs_F4
    (h1001 : Stmt10_0_1_F4) (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4)
    (h328 : Stmt3_2_8) (h6220 : Stmt6_2_20_F4) (h701 : Stmt7_0_1_F4) (h1101 : Stmt11_0_1_F4)
    (h12111 : Stmt12_1_11_F4) (hG2 : G2ZornQuotientModel) : Stmt12_2_2_F4 := by
  intro G _ _ T hs hnab hQ hT
  by_cases hA : Alt12_2_2 G
  · exact Or.inl hA
  right
  intro L hmax hf hq
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h1001 G T L hs hnab hQ hT hmax hf hq
  have hL0 : conjClosure L T = L := conjClosure_eq_self_of_normalizes hTL
  obtain ⟨⟨hM, -⟩, -, hex⟩ := h323 G T L hs hnab hQ hT hmax hf hq
  rw [hL0] at hM hex
  refine ⟨hTL, ?_, fun V hV => ?_⟩
  · obtain ⟨I, hI⟩ := irrPlusBaseNonempty_of_a36 VolI.a36ForSQTK_holds G T L hs hnab hQ hT hmax hf
      hq hTL
    obtain ⟨V₀, hV₀, -, -⟩ := hex I hI
    exact ⟨V₀, hV₀⟩
  have hH : Hyp1223 G T L V := ⟨hs, hnab, hQ, hT, hA, hmax, hf, hq, hTL, hV⟩
  have hfsu : FSU G T L V := hH.fsu
  have hLV := le_normalizer_of_hyp1223 hH
  have hVLT := le_sup_of_hyp1223 hH
  have hVT : V ≤ T := (hV.1.trans (reducedAggregate_le_pCoreOf _)).trans
    (pCoreOf_le_of_le_normalizer hT (le_sup_right.trans Subgroup.le_normalizer))
  obtain ⟨-, -, hcases⟩ := h325 G T L V hfsu hL0.symm

  have key : V = conjClosure V T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧
      (∀ m ∈ Subgroup.normalizer (L : Set G),
        CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
      (Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) ∨
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥) := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, -, hTV, hC, hTI⟩ | ⟨hC, -, ⟨t, ht, htN⟩, hall⟩
    · have hTV : T ≤ Subgroup.normalizer (V : Set G) := by
        rw [h1]
        exact le_normalizer_conjClosure V T
      have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
        have := le_normalizer_conjClosure (conjClosure V T) (Subgroup.normalizer (L : Set G))
        rwa [← h2, ← h1] at this
      exact ⟨h1, hTV, fun m hm => Or.inl (conjugate_eq_self_of_mem_normalizer (hMV hm)),
        Or.inl hMV⟩
    · refine ⟨h1, hTV, fun m hm => ?_, Or.inr hC⟩
      by_cases hmV : m ∈ Subgroup.normalizer (V : Set G)
      · exact Or.inl (conjugate_eq_self_of_mem_normalizer hmV)
      · exact Or.inr (hTI m hm hmV)
    · exfalso
      obtain ⟨hVM, hVsum, hVinf, hniso⟩ := hall t ht htN
      have hVN : conjClosure V T ≤ Subgroup.normalizer (L : Set G) :=
        (conjClosure_le fun x hx v hv => (L ⊔ T).mul_mem ((L ⊔ T).mul_mem
          ((le_sup_right : T ≤ L ⊔ T) hx) (hVLT hv))
          ((L ⊔ T).inv_mem ((le_sup_right : T ≤ L ⊔ T) hx))).trans
          (sup_le Subgroup.le_normalizer hTL)
      rcases stmt12_1_setup_of_F4 h323 h325 h701 G T L V hfsu hL0.symm hC t ht htN hVM hVsum hVinf
          hniso with
        hJ4 | ⟨n, hn, ⟨e⟩, hred', ⟨eM⟩, hLVt, hnat1, hnat2⟩
      · exact hA (Or.inr (Or.inr (Or.inr (Or.inr hJ4))))
      · exact h12111 G T L hs hnab hQ hT hmax hf n hn ⟨e⟩ (conjClosure V T) V
          (CFSG.conjugate V t) hVN hred' ⟨eM⟩ hVinf hVsum.symm hLV hLVt hnat1 hnat2 hniso
  obtain ⟨hVeq, hTV, hTI, hMC⟩ := key
  have hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) := by
    have := (stmt3_2_2_eight_proved G T L V hfsu).2.1
    rwa [hL0, ← hVeq] at this
  refine ⟨⟨hVT, hTV, hred, hfsu⟩, hTI, hMC, ?_⟩

  obtain ⟨hab, -, -, h7⟩ := h701 G T L V hfsu
  rcases h7 with hFF | hJ4 | ⟨n, hn, hOrth⟩ | hFour
  ·
    obtain ⟨hab', hc⟩ := h328 G T L V hfsu hL0.symm hVeq (isFFModule_of_eq hVeq.symm hL0 hFF)
    refine ⟨hab', ?_⟩
    rcases hc with h1 | (h2a | h2b) | h3 | h4 | (⟨⟨e⟩, halt⟩ | ⟨⟨e⟩, halt⟩) | ⟨⟨e⟩, halt⟩ |
        ⟨⟨e⟩, hcard⟩ | ⟨hperf, hZ3, ⟨e⟩, hcard⟩ | ⟨n, hn, ⟨e⟩, hnat⟩ | ⟨⟨e⟩, hext⟩ |
        ⟨⟨e⟩, hcard⟩
    · exact (false_of_concl328_one_F4 h6220 naturalSL24NotA5Sum hH hred hM h1).elim
    · exact modules_of_concl328_two_a_F4 h1101 hH hred h2a
    · exact modules_of_concl328_two_b l32FourIndecomposable hH hred h2b
    · exact (false_of_concl328_three_F4 h1101 hH hred h3).elim
    · exact modules_of_concl328_four_F4 h1101 hG2 hH hred h4
    · exact modules_of_alternatingNatural_odd hH (Or.inl rfl) e halt
    · exact modules_of_alternatingNatural_odd hH (Or.inr rfl) e halt
    · exact modules_of_concl328_six hH e halt
    · exact modules_of_concl328_seven hH hTV e hcard
    · exact modules_of_concl328_eight hatA6SixIrreducible hH hred hperf hZ3 e hcard
    · exact modules_of_concl328_nine hH hred hTV hn e hnat
    · exact modules_of_concl328_ten extSqFourAltEight hH hred e hext
    · exact modules_of_concl328_eleven l52TenFixedPointFree hH hred hTV e hcard
  ·
    exact (hA (Or.inr (Or.inr (Or.inr (Or.inr hJ4.2.2.2.2.2))))).elim
  ·
    obtain ⟨hab', hO⟩ := binaryOrthogonalFour_of_eq hVeq.symm hL0 hOrth
    exact (false_of_concl701_orth_F4 h6220 hH hred hM hn hO).elim
  ·
    have h1 := hFour.1
    rw [show fsuL0 T L = L from hL0] at h1
    exact (lt_irrefl L h1).elim

end CFSG.Quasithin.H13
