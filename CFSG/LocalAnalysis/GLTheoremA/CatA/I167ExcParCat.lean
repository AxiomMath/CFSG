module


import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.Adapters.TauCetiLieModels
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthPlus
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSylowTorus
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterRoots
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


private theorem exc_cat_twoPart_aux1 {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    Odd ((2 ^ k) ^ j - 1) :=
  CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hk hj

private theorem exc_cat_twoPart_aux2 {a x : ℕ} (hx : Odd x) :
    padicValNat 2 (2 ^ a * x) = a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) hx.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd
      (fun hd => Nat.not_even_iff_odd.2 hx (even_iff_two_dvd.2 hd)), Nat.add_zero]

private theorem exc_cat_twoPart_aux3 {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    padicValNat 2 (orderD n (2 ^ k)) = k * (n * (n - 1)) := by
  rw [← Nat.factorization_def (orderD n (2 ^ k)) Nat.prime_two]
  exact CFSG.SeitzReduction.OmegaPilot.factorization_two_ordD hk hn

private theorem exc_cat_twoPart_aux4 (k : ℕ) (hk : 1 ≤ k) :
    orderA 3 (2 ^ k) =
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * (((2 ^ k) ^ 3 - 1) * ((2 ^ k) ^ 4 - 1))) := by
  have hodd : Odd ((2 ^ k) - 1) := by
    simpa using exc_cat_twoPart_aux1 (k := k) (j := 1) hk le_rfl
  have hg : Nat.gcd 4 ((2 ^ k) - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  unfold orderA
  rw [hg, Nat.div_one]
  have hI : Finset.Icc 2 (3 + 1) = {2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]

private theorem exc_cat_twoPart_aux5 {k : ℕ} (hk : 1 ≤ k) :
    padicValNat 2 (orderA 3 (2 ^ k)) = k * (3 * (3 - 1)) := by
  rw [exc_cat_twoPart_aux4 k hk]
  have hpow : (2 ^ k) ^ 6 = 2 ^ (6 * k) := by
    rw [← pow_mul]
    ring
  rw [hpow]
  have hA : Odd ((2 ^ k) ^ 2 - 1) := exc_cat_twoPart_aux1 hk (by norm_num)
  have hB : Odd ((2 ^ k) ^ 3 - 1) := exc_cat_twoPart_aux1 hk (by norm_num)
  have hC : Odd ((2 ^ k) ^ 4 - 1) := exc_cat_twoPart_aux1 hk (by norm_num)
  rw [exc_cat_twoPart_aux2 (a := 6 * k) (hA.mul (hB.mul hC))]
  ring

private theorem exc_cat_twoPart_aux6 {G : Type} [Group G] [Finite G] {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) {i : TauCeti.CFSGIndex} (e : G ≃* i.Group) (h1 : isOmP n (2 ^ k) i) :
    padicValNat 2 (Nat.card G) = k * (n * (n - 1)) := by
  cases i with
  | cyclic pp hpp => simp [isOmP, onLie] at h1
  | alternating m hm => simp [isOmP, onLie] at h1
  | sporadic s => simp [isOmP, onLie] at h1
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D r q =>
      change r = n ∧ q.card = 2 ^ k at h1
      obtain ⟨hr, hq⟩ := h1
      subst r
      have hcard : Nat.card G = orderD n (2 ^ k) := by
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.D n q, hv⟩ G ⟨e⟩]
        change orderD n q.card = orderD n (2 ^ k)
        rw [hq]
      rw [hcard, exc_cat_twoPart_aux3 hn hk]
    | _ => simp [isOmP, onLie] at h1

private theorem exc_cat_twoPart_aux7 {G : Type} [Group G] [Finite G] {n k : ℕ} (hk : 1 ≤ k)
    (hk1 : k = 1 → 5 ≤ n) (hn3 : n = 3)
    {i : TauCeti.CFSGIndex} (e : G ≃* i.Group) (h2 : isLnA 4 (2 ^ k) i) :
    padicValNat 2 (Nat.card G) = k * (n * (n - 1)) := by
  subst hn3
  rcases h2 with h2a | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩
  · cases i with
    | cyclic pp hpp => simp [onLie, isLnEps] at h2a
    | alternating m hm => simp [onLie, isLnEps] at h2a
    | sporadic s => simp [onLie, isLnEps] at h2a
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        change r + 1 = 4 ∧ q.card = 2 ^ k at h2a
        obtain ⟨hr, hq⟩ := h2a
        have hr3 : r = 3 := by omega
        subst r
        have hcard : Nat.card G = orderA 3 (2 ^ k) := by
          rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 3 q, hv⟩ G ⟨e⟩]
          change orderA 3 q.card = orderA 3 (2 ^ k)
          rw [hq]
        rw [hcard, exc_cat_twoPart_aux5 hk]
      | _ => simp [onLie, isLnEps] at h2a
  · omega
  · omega
  · omega
  · have hk1' : k = 1 :=
      Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hq)
    have := hk1 hk1'
    omega

theorem exc_cat_twoPart {G : Type} [Group G] [Finite G] {n k : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hk : 1 ≤ k) (hk1 : k = 1 → 5 ≤ n) (h : catalogIs G (isOmPA n (2 ^ k))) :
    padicValNat 2 (Nat.card G) = k * (n * (n - 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hn3', h2⟩
  · exact exc_cat_twoPart_aux6 (by omega) hk e h1
  · exact exc_cat_twoPart_aux7 hk hk1 hn3' e h2

private theorem exc_cat_pRank_le_aux1 {q : TauCeti.PrimePower} {k : ℕ} (h : q.card = 2 ^ k) :
    q.p = 2 ∧ q.exponent = k := by
  have h' : q.p ^ q.exponent = 2 ^ k := q.card_def.symm.trans h
  have hp2 : q.p = 2 := by
    have hdvd : q.p ∣ 2 ^ k := by
      rw [← h']
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  have hexp : q.exponent = k := by
    rw [hp2] at h'
    exact Nat.pow_right_injective (a := 2) (by norm_num) h'
  exact ⟨hp2, hexp⟩

private theorem exc_cat_pRank_le_aux2 {G : Type} [Group G] [Finite G] {p n k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : Odd n) (hn4 : 4 ≤ n) (hpk : p ∣ 2 ^ k + 1)
    (hm : CFSG.Open.StatedClassicalModel G .POmegaPlus n 2 k) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ n - 1 := by
  obtain ⟨-, F, hF, hFin, hFcard, ⟨eModel⟩⟩ := hm
  letI : Field F := hF
  letI : Finite F := hFin
  have hpF1 : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hpk
  have hpF : ¬ p ∣ Nat.card F := by
    intro hd
    exact hp.not_dvd_one (by
      have := Nat.dvd_sub hpF1 hd
      simpa using this)
  have hpe : CFSG.Open.pRank p (⊤ : Subgroup G) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eModel
  rw [hpe, CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_OmegaPlus_formula
    hp hp2 hn4 hpF]
  have hcond : (p : ℤ) ∣ (Nat.card F : ℤ) ^ n + 1 := by
    have h2 : p ∣ (Nat.card F) ^ n + 1 :=
      hpF1.trans (by simpa using Odd.nat_add_dvd_pow_add_pow (Nat.card F) 1 hn)
    exact_mod_cast h2
  have hord : orderOf (Nat.card F : ZMod p) = 2 :=
    CFSG.StandardType.OrdPInnerExc.orderOf_natCast_eq_two_of_dvd_add_one hp hp2 hpF1
  rw [if_pos hcond, hord, if_pos (by norm_num : Even (2 : ℕ)),
    Nat.mul_div_cancel_left (n - 1) (by norm_num : 0 < 2)]

private theorem exc_cat_pRank_le_aux3 {G : Type} [Group G] [Finite G] {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ 2 ^ k + 1)
    (hm : CFSG.Open.StatedClassicalModel G .PSL 4 2 k) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2 := by
  obtain ⟨-, F, hF, hFin, hFcard, ⟨eModel⟩⟩ := hm
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF1 : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hpk
  have hnot4 : ¬ p ∣ 4 := by
    intro hd
    have h4 : p ∣ 2 ^ 2 := by simpa using hd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hle := CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSL_le_div_two
    (p := p) (K := F) (n := 4) (hp.odd_of_ne_two hp2) hnot4 hpF1
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eModel]
  simpa using hle

private theorem exc_cat_pRank_le_aux4 {G : Type} [Group G] [Finite G] {p n k r : ℕ}
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.D r q).Valid}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : Odd n) (hpk : p ∣ 2 ^ k + 1)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.D r q, hv⟩)
    (hi : isOmPA n (2 ^ k) (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D r q, hv⟩)) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ n - 1 := by
  simp only [isOmPA, isOmP, onLie, isLnEps, isAltN] at hi
  rcases hi with ⟨hrn, hq2k⟩ | hbad
  · subst r
    obtain ⟨hqp, hqk⟩ := exc_cat_pRank_le_aux1 hq2k
    have hn4 : 4 ≤ n := by
      simpa using ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hmodel : CFSG.Models.LieModel G .POmegaPlus n 2 k := by
      simpa [hqp, hqk] using CFSG.Models.lieModel_D n q hv e
    have hclass : CFSG.Open.StatedClassicalModel G .POmegaPlus n 2 k := by
      rcases hmodel.2 with hc | ⟨hn0, -⟩
      · exact hc
      · omega
    exact exc_cat_pRank_le_aux2 hp hp2 hn hn4 hpk hclass
  · exfalso
    rcases hbad with ⟨-, hln⟩
    simpa [isLnA, onLie, isLnEps, isAltN] using hln

private theorem exc_cat_pRank_le_aux5 {G : Type} [Group G] [Finite G] {p n k r : ℕ}
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.A r q).Valid}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ 2 ^ k + 1)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A r q, hv⟩)
    (hi : isOmPA n (2 ^ k) (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩)) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ n - 1 := by
  simp [isOmPA, isOmP, onLie, isLnEps, isAltN] at hi
  obtain ⟨hn3, hln⟩ := hi
  have hln' : r + 1 = 4 ∧ q.card = 2 ^ k := by
    simpa [isLnA, onLie, isLnEps, isAltN] using hln
  obtain ⟨hr, hq2k⟩ := hln'
  obtain ⟨hqp, hqk⟩ := exc_cat_pRank_le_aux1 hq2k
  have hmodel : CFSG.Models.LieModel G .PSL 4 2 k := by
    have h0 := CFSG.Models.lieModel_A r q hv e
    rw [hr, hqp, hqk] at h0
    exact h0
  have hclass : CFSG.Open.StatedClassicalModel G .PSL 4 2 k := by
    rcases hmodel.2 with hc | ⟨h40, -⟩
    · exact hc
    · omega
  have hle := exc_cat_pRank_le_aux3 hp hp2 hpk hclass
  simpa [hn3] using hle

private theorem exc_cat_pRank_le_aux6 {G : Type} [Group G] [Finite G] {p n k deg : ℕ}
    {hdeg : 5 ≤ deg} (hp : p.Prime) (hpk : p ∣ 2 ^ k + 1)
    (e : G ≃* (TauCeti.CFSGIndex.alternating deg hdeg).Group)
    (hi : isOmPA n (2 ^ k) (TauCeti.CFSGIndex.alternating deg hdeg)) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ n - 1 := by
  simp [isOmPA, isOmP, onLie, isLnEps, isAltN] at hi
  obtain ⟨hn3, hln⟩ := hi
  have hln' : 2 ^ k = 2 ∧ deg = 8 := by
    simpa [isLnA, onLie, isLnEps, isAltN] using hln
  obtain ⟨h2k, hdeg8⟩ := hln'
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by
      rw [h2k] at hpk
      norm_num at hpk
      exact hpk
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  subst deg
  have hcard : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hnotdvd : ¬ 3 ^ 3 ∣ Nat.card (alternatingGroup (Fin 8)) := by
    rw [hcard]
    norm_num
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 8))) ≤ 2 :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
      (p := 3) (k := 2) (by norm_num) hnotdvd
  have hpe : CFSG.Open.pRank 3 (⊤ : Subgroup G) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 8))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e
  rw [hp3, hn3, hpe]
  exact hle

theorem exc_cat_pRank_le {G : Type} [Group G] [Finite G] {p n k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : Odd n) (hn3 : 3 ≤ n) (hk : 1 ≤ k) (hpk : p ∣ 2 ^ k + 1)
    (h : catalogIs G (isOmPA n (2 ^ k))) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ n - 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    cases d with
    | D r q => exact exc_cat_pRank_le_aux4 hp hp2 hn hpk e hi
    | A r q => exact exc_cat_pRank_le_aux5 hp hp2 hpk e hi
    | _ => exfalso; simp_all [isOmPA, isOmP, onLie, isLnA, isLnEps, isAltN]
  | cyclic _ _ => exfalso; simp_all [isOmPA, isOmP, onLie, isLnA, isLnEps, isAltN]
  | alternating deg hdeg => exact exc_cat_pRank_le_aux6 hp hpk e hi
  | sporadic _ => exfalso; simp_all [isOmPA, isOmP, onLie, isLnA, isLnEps, isAltN]

end CFSG.LocalAnalysis.GLTheoremA.I167

end
