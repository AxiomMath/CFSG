module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem516
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem516R
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem516TD
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Cases

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H D : Subgroup G} {n : ℕ}

namespace Hyp5_0_1

variable (h : Hyp5_0_1 G T M L n)
include h

theorem natQuot_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (hQuot : Fact516Quot) (hV : IsCh5Module T L V)
    (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hO : pCoreOf 2 (D ⊔ H) = ⊥)
    {N : Subgroup G} (hNR : N ≤ reducedAggregate (L ⊔ T))
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (N : Set G)) (hN : IsNatQuotCh5 L N n) :
    ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧
      reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ n ≤ 4 := by
  obtain ⟨W, -, hW, hq, hJ⟩ := hQuot G T L D _ N n (h.setting516 hD hV) h.two_le hNR hLTN hN
  have hI := h.caseI_D_F4 h331 hR1 hH hD
  rcases h.pCoreOf_ne_bot_or_center hC58 h317 hH hD.1 hW hI hJ with h1 | ⟨hZH, hZ⟩
  · exact absurd hO h1
  refine ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hZH.trans inf_le_right),
    inf_centralizer_eq_bot_of_center h.sylow.1 (hD.1.trans inf_le_left)
      h.reducedAggregate_le_T (le_sup_right.trans sup_le_normalizer_reducedAggregate)
      h.T_le_normalizer hZ, ?_⟩
  rcases h.pCoreOf_ne_bot_or_qhat_le_of_316 h316 hH hD.1 hW hI with h1 | h1
  · exact absurd hO h1
  · exact hq _ h1

theorem commutator_eq_bot_or_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (h512 : Stmt5_1_2_F4) (hQuot : Fact516Quot) (hV : IsCh5Module T L V)
    (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hO : pCoreOf 2 (D ⊔ H) = ⊥) :
    ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∨
      (n = 2 ∧ IsCommCentralSplit L T (reducedAggregate (L ⊔ T)) ∧
        IsBarS5 L T (reducedAggregate (L ⊔ T)) ∧
        IsS5ModCh5 L T ⁅reducedAggregate (L ⊔ T), L⁆) := by
  rcases h.dichotomy_F4 h331 hC58 h317 h512 hV.isCh5Module_reducedAggregate hH with ⟨hZH, -⟩ |
    ⟨-, hnat | hs5⟩
  · exact Or.inl hZH
  · exact Or.inl (h.natQuot_F4 h331 hC58 h316 h317 hR1 hQuot hV hH hD hO le_rfl
      sup_le_normalizer_reducedAggregate hnat).1
  · exact Or.inr hs5

theorem case_two_nat_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (h512 : Stmt5_1_2_F4) (hQuot : Fact516Quot) (hTwo : Fact516Two)
    (hV : IsCh5Module T L V) (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hO : pCoreOf 2 (D ⊔ H) = ⊥)
    (hsum : IsSumOfTwo L (reducedAggregate (L ⊔ T)) (fun W => IsNatModCh5 L W n)) :
    (n = 2 ∧ IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∧
        ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) ∨
      ((n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) := by
  have hRc := reducedAggregate_comm L T
  have hLR : L ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) :=
    le_sup_left.trans sup_le_normalizer_reducedAggregate
  have hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ := by
    rcases h.commutator_eq_bot_or_F4 h331 hC58 h316 h317 hR1 h512 hQuot hV hH
      hD hO with h1 | ⟨hn2, -, -, hS5⟩
    · exact h1
    · exfalso
      obtain ⟨W₁, W₂, -, -, hdisj, hsup, hW₁, hW₂⟩ := hsum
      have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
        hRc a ((le_sup_left.trans hsup.le) ha) b ((le_sup_right.trans hsup.le) hb)
      have hRL := commutator_eq_of_sum hLR hsup hW₁.commutator_eq hW₂.commutator_eq
      have h16 := (isA5ModuleUnder_of_isS5ModCh5 hS5 h.commutator_eq h.sylow.1
        h.T_le_normalizer).card_eq
      rw [hRL] at h16
      have hc := card_sup_eq_mul hdisj hcomm
      rw [hsup, h16, hW₁.card_eq, hW₂.card_eq, hn2] at hc
      norm_num at hc
  obtain ⟨W, -, hW, hq⟩ := hTwo G T L D _ n (h.setting516 hD hV) h.two_le hsum
  have hn : n ≤ 2 := by
    rcases h.pCoreOf_ne_bot_or_qhat_le_of_316 h316 hH hD.1 hW
      (h.caseI_D_F4 h331 hR1 hH hD) with h1 | h1
    · exact absurd hO h1
    · exact hq _ h1
  have hn2 : n = 2 := le_antisymm hn h.two_le
  have hVne : V ≠ ⊥ := by
    intro hb
    apply hV.2.2
    rw [hb]
    exact Subgroup.commutator_bot_left L
  rcases eq_or_isNatModCh5_of_le_sum hsum hRc hV.le_reducedAggregate
      (le_sup_left.trans hV.isTwoReducedIn.2.1) hVne with hVeq | hVnat
  · left
    refine ⟨hn2, ?_, hZH⟩
    rw [hVeq]
    exact hsum
  · right
    refine ⟨Or.inl hn2, ?_, hZH⟩
    rw [hVnat.commutator_eq]
    exact hVnat

theorem case_two_s5_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (h512 : Stmt5_1_2_F4) (hQuot : Fact516Quot)
    (hV : IsCh5Module T L V) (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hO : pCoreOf 2 (D ⊔ H) = ⊥)
    (hsum : IsSumOfTwo (L ⊔ T) (reducedAggregate (L ⊔ T)) (IsS5ModCh5 L T)) : False := by
  have hRc := reducedAggregate_comm L T
  have hLR : L ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) :=
    le_sup_left.trans sup_le_normalizer_reducedAggregate
  have hA5 : IsA5ModuleSum L (reducedAggregate (L ⊔ T)) :=
    isA5ModuleSum_of_s5 (Or.inr hsum) h.commutator_eq h.sylow.1 h.T_le_normalizer
  have hZ := h.centerOf_eq_bot_of_borel hH hD hO (h.borel_le_centralizer_of_sum hA5 le_rfl)
  have hne := h.commutator_ne_bot_of_centerOf_eq_bot hH hZ
  rcases h.commutator_eq_bot_or_F4 h331 hC58 h316 h317 hR1 h512 hQuot hV hH
    hD hO with h1 | ⟨-, -, -, hS5⟩
  · exact hne h1
  obtain ⟨W₁, W₂, -, -, hdisj, hsup, hW₁, hW₂⟩ := hsum
  have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
    hRc a ((le_sup_left.trans hsup.le) ha) b ((le_sup_right.trans hsup.le) hb)
  have hA₁ := isA5ModuleUnder_of_isS5ModCh5 hW₁ h.commutator_eq h.sylow.1 h.T_le_normalizer
  have hA₂ := isA5ModuleUnder_of_isS5ModCh5 hW₂ h.commutator_eq h.sylow.1 h.T_le_normalizer
  have hRL := commutator_eq_of_sum hLR hsup hA₁.commutator_eq hA₂.commutator_eq
  have h16 := (isA5ModuleUnder_of_isS5ModCh5 hS5 h.commutator_eq h.sylow.1
    h.T_le_normalizer).card_eq
  rw [hRL] at h16
  have hc := card_sup_eq_mul hdisj hcomm
  rw [hsup, h16, hA₁.card_eq, hA₂.card_eq] at hc
  norm_num at hc

theorem case_quot_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (hQuot : Fact516Quot)
    (hV : IsCh5Module T L V) (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hO : pCoreOf 2 (D ⊔ H) = ⊥) (heven : Even n)
    (hnat : IsNatQuotCh5 L ⁅reducedAggregate (L ⊔ T), L⁆ n) :
    (n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ := by
  have hLTR : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) :=
    sup_le_normalizer_reducedAggregate
  have hRLR : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ reducedAggregate (L ⊔ T) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hLTR)
  have hLTRL : L ⊔ T ≤ Subgroup.normalizer
      ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hLTR (sup_le Subgroup.le_normalizer h.T_le_normalizer)
  obtain ⟨hZH, hCR, hn4⟩ :=
    h.natQuot_F4 h331 hC58 h316 h317 hR1 hQuot hV hH hD hO hRLR hLTRL hnat
  have hnat' : IsNatModCh5 L ⁅reducedAggregate (L ⊔ T), L⁆ n :=
    hnat.isNatModCh5 (eq_bot_iff.mpr ((inf_le_inf_right _ hRLR).trans hCR.le))
  have hVL : ⁅V, L⁆ = ⁅reducedAggregate (L ⊔ T), L⁆ :=
    commutator_eq_of_irreducible (fun U hU hLU hU1 => (hnat'.irreducible U hU hLU).resolve_left hU1)
      hV.le_reducedAggregate (le_sup_left.trans hV.isTwoReducedIn.2.1) hV.2.2
  have h2 := h.two_le
  refine ⟨?_, ?_, hZH⟩
  · obtain ⟨k, hk⟩ := heven
    omega
  · rw [hVL]
    exact hnat'

theorem case_split_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (h512 : Stmt5_1_2_F4) (hQuot : Fact516Quot)
    (hV : IsCh5Module T L V) (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hO : pCoreOf 2 (D ⊔ H) = ⊥) (hsplit : IsCommCentralSplit L T (reducedAggregate (L ⊔ T)))
    (hbar : IsBarS5 L T (reducedAggregate (L ⊔ T)))
    (hS5 : IsS5ModCh5 L T ⁅reducedAggregate (L ⊔ T), L⁆) :
    n = 2 ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆ ∧ centerOf H = ⊥ := by
  have hA5 := isA5ModuleUnder_of_isS5ModCh5 hS5 h.commutator_eq h.sylow.1 h.T_le_normalizer
  have hZ := h.centerOf_eq_bot_of_borel hH hD hO
    (borel_le_centralizer_of_split h.isSylowTwoOf_inf hsplit hA5 (reducedAggregate_comm L T))
  have hne := h.commutator_ne_bot_of_centerOf_eq_bot hH hZ
  rcases h.commutator_eq_bot_or_F4 h331 hC58 h316 h317 hR1 h512 hQuot hV hH
    hD hO with h1 | ⟨hn2, -, -, -⟩
  · exact absurd h1 hne
  obtain ⟨h1, h2⟩ := h.isBarS5_and_s5 hV hbar hS5
  exact ⟨hn2, h1, h2, hZ⟩

theorem case_orth_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (h512 : Stmt5_1_2_F4) (hQuot : Fact516Quot) (hOrth : Fact516Orth)
    (hV : IsCh5Module T L V) (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hO : pCoreOf 2 (D ⊔ H) = ⊥) (horth : IsOrthCh5 L (reducedAggregate (L ⊔ T)) n) :
    (n = 2 ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆ ∧ centerOf H = ⊥) ∨
      (n % 4 = 0 ∧ IsOrthCh5 L V n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧
        ∀ Dp Dm : Subgroup G, Dp ≤ D → Dm ≤ D → Nat.card Dp = 2 ^ (n / 2) - 1 →
          Nat.card Dm = 2 ^ (n / 2) + 1 →
            quasithinOmegaOneCenter T ≤ centerOf (Dm ⊔ H) ∧
              (pCoreOf 2 (Dp ⊔ H) ≠ ⊥ ∨ n = 4 ∨ n = 8)) := by
  obtain ⟨m, hm, -⟩ := id horth
  subst hm
  have horth' : IsOrthCh5 L (reducedAggregate (L ⊔ T)) (2 * m) := horth
  have hVR : V = reducedAggregate (L ⊔ T) := h.eq_of_isOrthCh5 hV horth'
  have hm1 : 1 ≤ m := by have := h.two_le; omega
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    have hm1' : m = 1 := by omega
    subst hm1'
    left
    have hA5 : IsA5ModuleUnder L (reducedAggregate (L ⊔ T)) := horth'.isA5ModuleUnder
    have hZ := h.centerOf_eq_bot_of_borel hH hD hO
      (h.borel_le_centralizer_of_sum (Or.inl hA5) le_rfl)
    have hne := h.commutator_ne_bot_of_centerOf_eq_bot hH hZ
    rcases h.commutator_eq_bot_or_F4 h331 hC58 h316 h317 hR1 h512 hQuot hV hH
      hD hO with h1 | ⟨-, -, hbar, hS5⟩
    · exact absurd h1 hne
    obtain ⟨h1, h2⟩ := h.isBarS5_and_s5 hV hbar hS5
    exact ⟨rfl, h1, h2, hZ⟩
  · right
    have hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ := by
      rcases h.commutator_eq_bot_or_F4 h331 hC58 h316 h317 hR1 h512 hQuot hV hH
        hD hO with h1 | ⟨hn2, -⟩
      · exact h1
      · omega
    obtain ⟨-, hodd, hDp⟩ := hOrth G T L D _ m (h.setting516 hD hV) horth' hm1
    set U := reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)
      with hU
    have hmeven : Even m := by
      by_contra hme
      have hTU := hodd (Nat.not_even_iff_odd.mp hme)
      have hZU : quasithinOmegaOneCenter T = U := by
        apply le_antisymm h.omega_le_inf_centralizer
        rw [← h.inf_centralizer_T]
        exact le_inf inf_le_left (Subgroup.le_centralizer_iff.mp hTU)
      have hDU : D ≤ Subgroup.normalizer (U : Set G) := by
        intro d hd
        have hdL : d ∈ L := (Subgroup.mem_inf.mp (hD.1 hd)).1
        have hdN : d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
          (Subgroup.mem_inf.mp (hD.1 hd)).2
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_sup_left.trans sup_le_normalizer_reducedAggregate hdL,
            F7.normalizer_le_normalizer_centralizer _ hdN⟩
      rw [← hZU] at hDU
      exact h.pCoreOf_ne_bot_of_le_normalizer hH hDU hZH hO
    refine ⟨?_, ?_, hZH, fun Dp Dm hDp' hDm' hcp hcm => ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := hmeven
      omega
    · rw [hVR]
      exact horth
    ·
      have hm2' : 2 * m / 2 = m := by omega
      rw [hm2'] at hcm
      have hDmC := orthKernelFact G L _ (T ⊓ L) Dm m horth' h.isSylowTwoOf_inf
        (hDm'.trans hD.1) hcm
      have hZDm : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (Dm : Set G) :=
        h.omega_le_inf_centralizer.trans hDmC
      have hZH' : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
      refine le_inf ((quasithinOmegaOneCenter_le_self T).trans (hH.1.1.trans le_sup_right)) ?_
      rw [Subgroup.le_centralizer_iff]
      exact sup_le (Subgroup.le_centralizer_iff.mp hZDm) (Subgroup.le_centralizer_iff.mp hZH')
    ·
      have hm2' : 2 * m / 2 = m := by omega
      rw [hm2'] at hcp
      obtain ⟨hnorm, hTD, hq⟩ := hDp Dp hDp' hcp hm2
      have hI : H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (T ⊔ Dp) : Set G) :=
        h.caseI_of_normalizes (hnorm T h.T_le_normalizer_borel h.T_le_normalizer_inf)
          (hnorm _ (h.inf_le_normalizer_borel_F4 h331 hR1 hH) (h.inf_le_normalizer_inf_F4 h331 hR1 hH))
      rcases h.pCoreOf_ne_bot_or_qhat_le_of_316 h316 hH (hDp'.trans hD.1) hTD
        hI with h1 | h1
      · exact Or.inl h1
      · have hm4 := hq _ h1
        obtain ⟨k, hk⟩ := hmeven
        right
        omega

end Hyp5_0_1

theorem stmt5_1_6_cases_of_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (h512 : Stmt5_1_2_F4) (h513 : Stmt5_1_3_F4) (hQuot : Fact516Quot)
    (hTwo : Fact516Two) (hOrth : Fact516Orth) : Stmt5_1_6_cases_F4 := by
  intro G _ _ T M L V H D n h hV hH hD hO heven _
  rcases h513 G T M L _ n h hV.isCh5Module_reducedAggregate with h1 | ⟨hn2, -, h2⟩ | h3 | h4 |
    ⟨h5, h5', h5''⟩
  · rcases h.case_two_nat_F4 h331 hC58 h316 h317 hR1 h512 hQuot hTwo hV hH hD hO
      h1 with c | c
    · exact Or.inl c
    · exact Or.inr (Or.inl c)
  · exact (h.case_two_s5_F4 h331 hC58 h316 h317 hR1 h512 hQuot hV hH hD hO
      h2).elim
  · exact Or.inr (Or.inl (h.case_quot_F4 h331 hC58 h316 h317 hR1 hQuot hV hH hD
      hO heven h3))
  · rcases h.case_orth_F4 h331 hC58 h316 h317 hR1 h512 hQuot hOrth hV hH hD hO
      h4 with c | c
    · exact Or.inr (Or.inr (Or.inl c))
    · exact Or.inr (Or.inr (Or.inr c))
  · exact Or.inr (Or.inr (Or.inl (h.case_split_F4 h331 hC58 h316 h317 hR1 h512
      hQuot hV hH hD hO h5 h5' h5'')))

theorem stmt5_1_6_of_facts_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow)
    (hR1 : L2RankOneSylowFact) (h512 : Stmt5_1_2_F4) (h513 : Stmt5_1_3_F4) (hQuot : Fact516Quot)
    (hTwo : Fact516Two) (hOrth : Fact516Orth) : Stmt5_1_6_F4 :=
  stmt5_1_6_of_F4 h331 hC58 stmt5_1_6_odd
    (stmt5_1_6_cases_of_F4 h331 hC58 h316 h317 hR1 h512 h513 hQuot hTwo hOrth)

end CFSG.Quasithin.H13
