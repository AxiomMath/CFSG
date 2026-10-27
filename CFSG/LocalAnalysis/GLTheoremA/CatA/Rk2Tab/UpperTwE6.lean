module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U6Mult
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration


theorem pRank_twistedE6_le_four_of_orderOf_eq_one {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (he : orderOf (((2 ^ n : ℕ)) : ZMod p) = 1) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) ≤ 4 := by
  have hpq : ¬ p ∣ 2 ^ n := not_dvd_of_orderOf_pos hp he (by norm_num)
  exact pRank_le_of_sylowTorusDatum
    (CFSG.StandardType.ExcFrames.sylowTorus_twistedE6_one Nat.prime_two (by omega) F hF σ hσ hp hp5 hpq he) hp

theorem pRank_twistedE6_le_four_of_mem {F : Type} [Field F] [Finite F] {n m : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : m ∈ [3, 4, 6, 8, 10, 12, 18])
    (he : orderOf (((2 ^ n : ℕ)) : ZMod p) = m) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) ≤ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (pRank_le_of_sylowTorusDatum
      (sylowTorus_twistedE6_three Nat.prime_two (by omega) F hF σ hσ hp he) hp).trans (by norm_num)
  · exact (pRank_le_of_sylowTorusDatum
      (sylowTorus_twistedE6_four Nat.prime_two (by omega) F hF σ hσ hp he) hp).trans (by norm_num)
  · have hpq' : ¬ p ∣ 2 ^ n := fun hd =>
      (by omega : p ≠ 2) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
    have h6dvd : 6 ∣ p - 1 := by
      have hq0 : (((2 ^ n : ℕ)) : ZMod p) ≠ 0 := fun h =>
        hpq' ((ZMod.natCast_eq_zero_iff _ _).1 h)
      rw [← he]
      exact ZMod.orderOf_dvd_card_sub_one hq0
    have hp7 : 7 ≤ p := by
      have hle := Nat.le_of_dvd (by omega) h6dvd
      omega
    exact (pRank_le_of_sylowTorusDatum
      (CFSG.HardMathSupport.Lang.TwE6Step3.sylowTorus_twistedE6_six Nat.prime_two (by omega) F
        hF σ hσ hp hp7 hpq' he) hp).trans (by norm_num)
  · exact (pRank_le_of_sylowTorusDatum
      (sylowTorus_twistedE6_eight Nat.prime_two (by omega) F hF σ hσ hp he) hp).trans (by norm_num)
  · exact (pRank_le_of_sylowTorusDatum
      (sylowTorus_twistedE6_ten Nat.prime_two (by omega) F hF σ hσ hp he) hp).trans (by norm_num)
  · exact (pRank_le_of_sylowTorusDatum
      (sylowTorus_twistedE6_twelve Nat.prime_two (by omega) F hF σ hσ hp he) hp).trans (by norm_num)
  · exact (pRank_le_of_sylowTorusDatum
      (sylowTorus_twistedE6_eighteen Nat.prime_two (by omega) F hF σ hσ hp he) hp).trans
      (by norm_num)

theorem pRank_twistedE6_le_four_of_not_dvd_add_one {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) ≤ 4 := by
  by_cases hp3 : p = 3
  · subst hp3
    have hord : rk2Ord 3 n = 1 := by
      rcases rk2Ord_three_eq_one_or_two n with h | h
      · exact h
      · exact absurd ((rk2Ord_eq_two_iff Nat.prime_three (by norm_num)).mp h) hpq
    exact rk2TwE6ThreeOneFrontier F n σ hF hσ hord
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      have hle : p ≤ 4 := by omega
      interval_cases p <;>
        first | exact absurd rfl hp2 | exact absurd rfl hp3 | exact absurd hp (by norm_num)
    have hpn : ¬ p ∣ 2 ^ n := fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
    have he0 : orderOf (((2 ^ n : ℕ)) : ZMod p) ≠ 0 := orderOf_natCast_ne_zero hp hpn
    set e := orderOf (((2 ^ n : ℕ)) : ZMod p) with he_def
    have he : orderOf (((2 ^ n : ℕ)) : ZMod p) = e := rfl
    have he2 : e ≠ 2 := by
      intro h2
      have h2' : rk2Ord p n = 2 := by
        rw [rk2Ord,
          show ((2 : ZMod p) ^ n) = (((2 ^ n : ℕ)) : ZMod p) by push_cast; ring, he]
        exact h2
      exact hpq ((rk2Ord_eq_two_iff hp hp2).mp h2')
    by_cases he1 : e = 1
    · exact pRank_twistedE6_le_four_of_orderOf_eq_one (by omega) hF σ hσ hp hp5 (he.trans he1)
    · by_cases hmem : e ∈ [3, 4, 6, 8, 10, 12, 18]
      · exact pRank_twistedE6_le_four_of_mem (by omega) hF σ hσ hp hp5 hmem he
      · have hnot : e ∉ [1, 2, 3, 4, 6, 8, 10, 12, 18] := by
          intro h
          rcases List.mem_cons.mp h with h1 | h'
          · exact he1 h1
          rcases List.mem_cons.mp h' with h2 | h''
          · exact he2 h2
          · exact hmem h''
        have h0 : degCountTw e = 0 := by
          by_contra hne
          exact hnot (mem_twE6_orders_of_degCountTw_pos (Nat.pos_of_ne_zero hne))
        have hp3' : 3 < p := by omega
        have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) ≤ 1 := by
          refine CFSG.SectionRank.pRank_le hp.one_lt ?_
          intro E _ hE
          rw [elemAbelian_card_eq_one_of_degCountTw_zero Nat.prime_two hn F hF σ hσ hp hp3' hpn
            (he.trans rfl) h0 hE]
          exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 1 hp.ne_zero)
        exact h1.trans (by norm_num)

theorem exists_twistedE6RootGroup_of_isLabel {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (ht : lab.tag = .twE6) (hc : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ lab.n)) ∧
        Nonempty (K ≃* ↥(twistedE6RootGroup F σ)) := by
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hK
  obtain ⟨F, hField, hFin, σ, hcard, hσ, ⟨e3⟩⟩ :=
    exists_twistedE6RootGroup_of_marked (u6_model_twE6 ht hM)
  refine ⟨F, hField, hFin, σ, hcard, hσ, ?_⟩
  let eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq (by rw [hc]))
  exact ⟨eK.trans e3⟩

theorem rk2_twoLocalRank_twe6_le_four_of_not_dvd_add_one {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hK : Rk2IsLabel K lab) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (hc : Subgroup.center K = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ lab.n + 1) :
    CFSG.Open.twoLocalPrimeRank p K ≤ 4 := by
  obtain ⟨F, hField, hFin, σ, hcard, hσ, ⟨e⟩⟩ :=
    exists_twistedE6RootGroup_of_isLabel hK ht hc
  letI : Field F := hField
  letI : Finite F := hFin
  have hpK : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  refine (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp K).trans ?_
  rw [hpK]
  exact pRank_twistedE6_le_four_of_not_dvd_add_one (by omega) hcard σ hσ hp hp2 hpq

theorem twoLocalPrimeRank_twistedE6RootGroup_le_five {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (σ : F ≃+* F) (hF : Nat.card F = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hLev : Rk2TwE6LeviRankInputMaximal) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ 2 ^ n + 1) :
    CFSG.Open.twoLocalPrimeRank r ↥(twistedE6RootGroup F σ) ≤ 5 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := n * 2) (by omega) (by rw [hF, pow_mul])
  have hmodel : TwistedChevalleyModel ↥(twistedE6RootGroup F σ) .E6 (2 ^ n) :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.excTwistedModel_graphFixedRootGroup
      TwistTag.E6 Nat.prime_two (by omega) F hF σ hσ
  have hHolds : CFSG.LieType.BorelTits.Holds ↥(twistedE6RootGroup F σ) 2 :=
    CFSG.LieType.BorelTits.holds_of_twistedChevalleyModel (p := 2) (f := n)
      (by omega) hmodel
  exact twoLocalRank_le_of_graphFixedLevi (t := TwistTag.E6) (σ := σ.toRingHom) σ.surjective
    hHolds hr hr2 (fun J hJ E hE hEel =>
      (rk2TwE6LeviRankInput_of_maximal hLev) F n hF σ hσ r hr hr2 hrq J hJ E hE hEel)

theorem rk2_twoLocalRank_twe6_le_five_of_dvd_add_one {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hK : Rk2IsLabel K lab) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (hc : Subgroup.center K = ⊥) (hLev : Rk2TwE6LeviRankInputMaximal)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ∣ 2 ^ lab.n + 1) :
    CFSG.Open.twoLocalPrimeRank p K ≤ 5 := by
  obtain ⟨F, hField, hFin, σ, hcard, hσ, ⟨e⟩⟩ :=
    exists_twistedE6RootGroup_of_isLabel hK ht hc
  letI : Field F := hField
  letI : Finite F := hFin
  have hGL : CFSG.Open.twoLocalPrimeRank p K =
      CFSG.Open.twoLocalPrimeRank p ↥(twistedE6RootGroup F σ) := by
    have h := CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr
      (p := p) hp.one_lt e
    exact h.symm
  rw [hGL]
  exact twoLocalPrimeRank_twistedE6RootGroup_le_five (by omega) σ hcard hσ hLev hp hp2 hq

theorem rk2_up_twe6 {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n) (hc : Subgroup.center K = ⊥)
    (hLev : Rk2TwE6LeviRankInputMaximal) :
    evenRank K ≤ 5 := by
  rw [CFSG.RankThreeEvenClassification.Helpers.evenRank_eq_sup_twoLocalRanks]
  refine csSup_le' ?_
  rintro k ⟨p, hp, hp2, rfl⟩
  by_cases hq : p ∣ 2 ^ lab.n + 1
  · exact rk2_twoLocalRank_twe6_le_five_of_dvd_add_one hK ht hn hc hLev hp hp2 hq
  · exact (rk2_twoLocalRank_twe6_le_four_of_not_dvd_add_one hK ht hn hc hp hp2 hq).trans
      (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA
