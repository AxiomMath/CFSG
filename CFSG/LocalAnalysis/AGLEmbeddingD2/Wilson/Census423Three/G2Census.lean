module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.G2TypeA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.Dispatch
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartTwo.Sec4 (Census423)
open scoped MatrixGroups

theorem fieldData_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hK : Nat.card K = p) :
    Odd (Nat.card K) ∧ ringChar K ≠ 3 ∧ 5 ≤ Nat.card K ∧
      ∀ σ : K ≃+* K, σ ^ 3 = 1 → σ = 1 := by
  have hp' : p.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have hch : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp' (by norm_num)
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hK]; exact hp'.odd_of_ne_two (by omega)
  · have : ringChar K = p := ringChar.eq K p
    omega
  · rw [hK]; exact hp5
  · intro σ _
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp' K
      (n := 1) (by rw [hK, pow_one])).1
    have : Subsingleton (RingAut K) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim σ 1

section G2


theorem qRes_eq_short_of_long {K : Type} [Field K] [Finite K] (hchar : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) {m : adjointGroup .G2 K} (hm : m ∈ KS11Lie4Proof.g2LongSL2 K)
    (hm3 : m ^ 3 = 1) (hm1 : m ≠ 1) : qRes m = KS11Lie4Proof.g2ShortSL2 K := by
  have hcomm := (KS11Lie4Proof.g2ThreeBCent_holds K hchar hK4 m hm hm3 hm1).1
  have hSC : KS11Lie4Proof.g2ShortSL2 K ≤ Subgroup.centralizer ({m} : Set (adjointGroup .G2 K)) :=
    fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
      (KS11Lie4Proof.g2Short_commute_g2Long hs hm)
  have hperf : Group.IsPerfect ↥(KS11Lie4Proof.g2ShortSL2 K) :=
    (KS11Lie4Proof.isQuasisimple_g2ShortSL2 hK4).1
  have hS : ⁅KS11Lie4Proof.g2ShortSL2 K, KS11Lie4Proof.g2ShortSL2 K⁆ =
      KS11Lie4Proof.g2ShortSL2 K := Subgroup.commutator_eq_self
  exact CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof.inSubgroup_perfectResidual_eq_of_commutator
    hSC hS hcomm

theorem threeB_of_long {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hK : Nat.card K = p) {m : adjointGroup .G2 K} (hm : m ∈ KS11Lie4Proof.g2LongSL2 K)
    (hm3 : m ^ 3 = 1) (hm1 : m ≠ 1) : ThreeB m := by
  obtain ⟨hodd, h3, h5, hσ⟩ := fieldData_of_card_prime hp hK
  have hq := qRes_eq_short_of_long h3 (by omega) hm hm3 hm1
  obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
  exact ⟨_, inferInstance, GoodGroup.sl2 hodd h3 h5 hσ,
    ⟨(MulEquiv.subgroupCongr hq).trans e.symm⟩⟩

theorem threeA_of_short {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hK : Nat.card K = p) {z : adjointGroup .G2 K} (hz : z ∈ KS11Lie4Proof.g2ShortSL2 K)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ThreeA z := by
  have hp' : p.Prime := Fact.out
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp').mp h
      omega
    omega
  rcases hmod with h | h
  · exact threeA_of_split (by rw [hK]; omega) hz hz3 hz1
  · exact threeA_of_minus (p := p) (by rw [hK, pow_one]) (by rw [hK]; omega) (by omega) hz hz3 hz1

theorem g2_dichotomy {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hK : Nat.card K = p) :
    ∀ b : adjointGroup .G2 K, orderOf b = 3 →
      ThreeA b ∨ (ThreeB b ∧ ∀ e ∈ qRes b, orderOf e = 3 → ThreeA e) := by
  obtain ⟨hodd, h3, h5, hσ⟩ := fieldData_of_card_prime hp hK
  have hK4 : 4 ≤ Nat.card K := by omega
  have hord : ∀ {a : adjointGroup .G2 K}, orderOf a = 3 → a ^ 3 = 1 ∧ a ≠ 1 := by
    intro a ha
    refine ⟨by rw [← ha]; exact pow_orderOf_eq_one a, ?_⟩
    rintro rfl
    rw [orderOf_one] at ha
    omega
  have hord' : ∀ {a : adjointGroup .G2 K}, a ^ 3 = 1 → a ≠ 1 → orderOf a = 3 := fun h1 h2 =>
    orderOf_eq_prime h1 h2
  intro b hb
  obtain ⟨hb3, hb1⟩ := hord hb
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds K h3 hK4 b hb3 hb1
  have hconj3 : (g * b * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hb3, mul_one, mul_inv_cancel]
  have hconj1 : g * b * g⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have : g * b * g⁻¹ = 1 := h
    simpa [mul_inv_eq_one] using this
  have hback : ∀ a : adjointGroup .G2 K, g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := fun a => by group
  rcases hg with hS | hM
  · left
    have := (threeA_of_short hp hK hS hconj3 hconj1).conj g⁻¹
    rwa [hback] at this
  · right
    have hB := threeB_of_long hp hK hM hconj3 hconj1
    have hq := qRes_eq_short_of_long h3 hK4 hM hconj3 hconj1
    refine ⟨?_, ?_⟩
    · have := hB.conj g⁻¹
      rwa [hback] at this
    · intro e he he3
      obtain ⟨he3', he1⟩ := hord he3
      have heS : g * e * g⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 K := by
        rw [← hq]
        exact qRes_conj g he
      have e3 : (g * e * g⁻¹) ^ 3 = 1 := by rw [conj_pow, he3', mul_one, mul_inv_cancel]
      have e1 : g * e * g⁻¹ ≠ 1 := by
        intro h
        apply he1
        have : g * e * g⁻¹ = 1 := h
        simpa [mul_inv_eq_one] using this
      have := (threeA_of_short hp hK heS e3 e1).conj g⁻¹
      rwa [hback] at this

theorem g2_out_trivial {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hK : Nat.card K = p) (α : MulAut (adjointGroup .G2 K)) :
    ∃ g : adjointGroup .G2 K, α = MulAut.conj g := by
  obtain ⟨hodd, h3, h5, hσ⟩ := fieldData_of_card_prime hp hK
  obtain ⟨g, σ, hα⟩ := (CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form h3
    (by omega : 4 ≤ Nat.card K)).1 α
  have hσ1 : σ = 1 := by
    have hp' : p.Prime := Fact.out
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp' K
      (n := 1) (by rw [hK, pow_one])).1
    have : Subsingleton (RingAut K) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim σ 1
  exact ⟨g, by rw [hα, hσ1, map_one, mul_one]⟩

theorem g2Census423 : G2Census423 := by
  intro p _ hp3 X _ _ hX hq hZ
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hX.2
  rw [pow_one] at hK
  have hZC : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hR : Rank2 ↥(adjointGroup .G2 K) :=
    rank2_of_mulEquiv e (rank2_of_pRank (CFSG.RankThree.PartTwo.Sec4.Res417Four.pRank_g2_le_two hp3 X hX))
  exact census423_of_equiv_alpha e fun D hDc hDexp hD9 =>
    alphaVanishes_of_dichotomy hZC (g2_out_trivial hp3 hK) hR (g2_dichotomy hp3 hK) hDc hDexp hD9

theorem k423Inner46Three_holds : CFSG.RankThree.PartTwo.Sec4.K423Inner46Three :=
  k423Inner46Three_of_g2 g2Census423

end G2

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
