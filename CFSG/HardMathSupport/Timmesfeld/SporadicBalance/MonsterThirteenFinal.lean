module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenCensus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMPairs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

open CFSG.Open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat

theorem factorization_Gmat_thirteen : (Nat.card Gmat).factorization 13 = 3 := by
  have h : monsterOrder = 13 ^ 3 * 367782168773105542051187940355808264454144000000000 := by
    norm_num [monsterOrder]
  rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, h,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_twoB_thirteen : twoBCentralizerOrder.factorization 13 = 1 := by
  have h : twoBCentralizerOrder = 13 * 10731679932795102167040000 := by
    norm_num [twoBCentralizerOrder]
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_twoA_thirteen : (2 * monsterBabyOrder).factorization 13 = 1 := by
  have h : 2 * monsterBabyOrder = 13 * 639197150957911721719627776000000 := by
    norm_num [monsterBabyOrder]
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_centralizer_involution_thirteen (u : Gmat) (hu : orderOf u = 2) :
    (Nat.card (Subgroup.centralizer ({u} : Set Gmat))).factorization 13 ≤ 1 := by
  rcases CFSG.Monster.Existence.Census.generated_group_two_involution_classes u hu with h | h
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [card_centralizer_conj_eq, twoB_xGmat₁₃.2.2.2.2.1, factorization_twoB_thirteen]
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [card_centralizer_conj_eq, MonsterFiveGmat.natCard_centralizer_tGmat,
      factorization_twoA_thirteen]

theorem odd_card_core_thirteen (s : Gmat) (hs : orderOf s = 13) :
    Odd (Nat.card (GLAPPrimeCoreOf 13 (Subgroup.centralizer ({s} : Set Gmat)))) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine odd_card_gLAPPrimeCoreOf_thirteen (t := xGmat) hs
    (exists_thirteen_subgroup_of_factorization factorization_Gmat_thirteen
      factorization_centralizer_involution_thirteen hs) exists_twoB_Gmat ?_
  intro x hx hxt
  have h := card_inf_centralizer_dvd (h := 1) (u := xGmat) (f := x)
    (by rw [one_mul, inv_one, mul_one]) hxt hx
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem census_thirteen (s : Gmat) (hs : orderOf s = 13) :
    ∃ m : Gmat, ∃ k : ℕ, k % 13 ≠ 0 ∧
      (m * s * m⁻¹ = gw genD13W1 ^ k ∨ m * s * m⁻¹ = gw thirteenX ^ k) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨hg13, hd13, hc13, hcg, hcd, hdg, hc1, -⟩ := d13_gw_facts
  refine census_generic factorization_Gmat_thirteen hg13 hd13 hc13 hc1 hcg hcd hdg ?_ hs
  intro e he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlines⟩ := thirteen_a_facts
  refine ⟨gw (lineConjW e), ?_⟩
  have h := hlines e he
  have hrep : gw (lineRepW e) = gw genD13W0 ^ e.a * gw genD13W2 ^ e.b := by
    rw [lineRepW, gw_append, gw_powL13, gw_powL13]
  have htgt : gw (lineTargetW e) = if e.toC then gw genD13W1 else gw thirteenX := by
    unfold lineTargetW
    split_ifs <;> rfl
  rw [← hrep, h, ← htgt, mul_inv_cancel_right]

theorem core_eq_bot_of_conj_pow {s t m : Gmat} {k : ℕ} (hto : orderOf t = 13) (hk : k % 13 ≠ 0)
    (h : m * s * m⁻¹ = t ^ k)
    (ht : GLAPPrimeCoreOf 13 (Subgroup.centralizer ({t} : Set Gmat)) = ⊥) :
    GLAPPrimeCoreOf 13 (Subgroup.centralizer ({s} : Set Gmat)) = ⊥ := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hk1 : t ^ k ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hto] at this
    exact hk (Nat.mod_eq_zero_of_dvd this)
  rw [eq_bot_iff]
  intro n hn
  have h1 := conj_mem_gLAPPrimeCoreOf_conj (m := m) (by norm_num : Nat.Prime 13) hn
  rw [h, centralizer_pow_eq_of_prime hto hk1, ht, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  have := congrArg (fun a => m⁻¹ * a * m) h1
  simpa [mul_assoc] using this

theorem oPrimeCoreTrivialAt_thirteen_Gmat_of (hB13 : BThirteenOddCore) :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 13 Gmat := by
  intro s hs
  obtain ⟨m, k, hk, h | h⟩ := census_thirteen s hs
  · exact core_eq_bot_of_conj_pow orderOf_c13 hk h
      (gLAPPrimeCoreOf_c13_eq_bot (odd_card_core_thirteen _ orderOf_c13))
  · exact core_eq_bot_of_conj_pow orderOf_xE hk h
      (gLAPPrimeCoreOf_xE_eq_bot hB13 odd_card_core_thirteen)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem sporadicOPrimeHolds_M_thirteen_of (hB13 : BThirteenOddCore) : SporadicOPrimeHolds .M 13 :=
  sporadicOPrimeHolds_M_of_gmat (MonsterThirteen.oPrimeCoreTrivialAt_thirteen_Gmat_of hB13)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
