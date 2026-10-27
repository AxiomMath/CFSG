module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOUCore
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenOrthRank
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.GroupTheory.WeirSylow

theorem orthMinus_three_dvd_two_pow_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f
  simpa using this

theorem orthMinus_three_dvd_ordTwistedD {f m : ℕ} (hf : 1 ≤ f) (hm : 1 ≤ m) :
    3 ∣ CFSG.Open.ordTwistedD (m + 1) (2 ^ f) := by
  rw [CFSG.Open.ordTwistedD, CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one
    (CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hf (by omega)), Nat.div_one]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 (m + 1 - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  refine (?_ : 3 ∣ (2 ^ f) ^ (2 * 1) - 1).trans
    (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) h1)
  rw [mul_one]
  exact orthMinus_three_dvd_two_pow_sq_sub_one f

theorem orthMinus_not_dvd_card_of_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : ¬ ℓ ∣ Nat.card K := by
  rw [hK]
  intro h
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h))

section Index

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem orthMinus_card_orthogonalGroup_tail_eq {f m : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 1 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))) =
      2 * Nat.card ↥(orthResDer K b c m) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  obtain ⟨-, -, hcard⟩ := orthResDer_facts hK hm hirr
  let ψ : (quadTail m (minusTailForm K b c)).IsometryEquiv (quadMinus (m + 1) K b c) :=
    minusTailIsometry (m + 1) K b c
  have hψ := natCard_orthogonalGroup_congr ψ
  have hO := natCard_orthogonalGroup_quadMinus hirr m
  rw [← hψ] at hO
  rw [hcard, CFSG.Open.ordTwistedD,
    CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one
      (CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hf (by omega)), Nat.div_one]
  apply Nat.cast_injective (R := ℤ)
  have hpow : ∀ i : ℕ, ((Nat.card K : ℤ) ^ 2) ^ i = (Nat.card K : ℤ) ^ (2 * i) :=
    fun i => (pow_mul _ 2 i).symm
  simp only [hpow] at hO
  rw [hO, hK]
  push_cast [CFSG.Timmesfeld.ClassicalOrders.cast_prod_pow_sub_one
    (Nat.one_le_pow f 2 (by norm_num))]
  try simp only [Nat.add_sub_cancel]
  ring

theorem orthMinus_index_orthResDer_subgroupOf {f m : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 1 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((orthResDer K b c m).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))).index = 2 := by
  haveI : Finite (((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin m ⊕ Fin m → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have hΩO : orthResDer K b c m ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)) :=
    Subgroup.commutator_le_of_le le_rfl le_rfl
  have h1 := Subgroup.card_mul_index ((orthResDer K b c m).subgroupOf
    (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))))
  have h2 : Nat.card ↥((orthResDer K b c m).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))) =
        Nat.card ↥(orthResDer K b c m) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩO).toEquiv
  rw [h2, orthMinus_card_orthogonalGroup_tail_eq hK hm hirr] at h1
  have hpos : 0 < Nat.card ↥(orthResDer K b c m) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h1, mul_comm]

theorem orthMinus_mem_orthResDer_of_pow_eq_one {f m : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 1 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {x : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))}
    (hx : x ^ ℓ = 1) : (x : ((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin m ⊕ Fin m → K) × (Fin 2 → K))) ∈ orthResDer K b c m :=
  Subgroup.mem_subgroupOf.1
    (mem_of_pow_eq_one_of_index_two (orthMinus_index_orthResDer_subgroupOf hK hm hirr) hℓ hℓ2 hx)

end Index

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem orthMinus_pRank_top_le_orthResDer {f m : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 1 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    CFSG.Open.pRank ℓ (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadTail m (minusTailForm K b c)))) ≤
        CFSG.Open.pRank ℓ (⊤ : Subgroup ↥(orthResDer K b c m)) := by
  haveI : Finite (((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin m ⊕ Fin m → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have hΩO : orthResDer K b c m ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)) :=
    Subgroup.commutator_le_of_le le_rfl le_rfl
  have hN := orthMinus_index_orthResDer_subgroupOf hK hm hirr
  obtain ⟨E', -, hE', hcard⟩ := CFSG.SectionRank.exists_pRank hℓ.one_lt (⊤ : Subgroup
    ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))))
  have hEN : E' ≤ (orthResDer K b c m).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))) :=
    fun x hx => mem_of_pow_eq_one_of_index_two hN hℓ hℓ2 (hE'.2 x hx)
  have h1 := CFSG.SectionRank.le_pRank hℓ.one_lt hEN hE' hcard
  have h2 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := ℓ) ((orthResDer K b c m).subgroupOf
    (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))))
  have h3 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt
    (Subgroup.subgroupOfEquivOfLe hΩO)
  exact h1.trans (h2.le.trans h3.le)

theorem orthMinus_two_le_pRank {r f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hdvd : ℓ ∣ Nat.card K ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup
      ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have hQ : (QuadraticMap.polarBilin (quadTail r (minusTailForm K b c))).Nondegenerate :=
    nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)
  have hfin : Module.finrank K ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) = 2 * r + 2 := by
    rw [finrank_tailSpace, finrank_fin_two_fun]
  have h2 : 2 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadTail r (minusTailForm K b c)))) :=
    CFSG.LocalAnalysis.RankFourTheoremC.BCDEven.le_pRank_orth hℓ2
      (orthMinus_not_dvd_card_of_two_pow hK hℓ hℓ2) (e := 2) (by norm_num) even_two hdvd
      (quadTail r (minusTailForm K b c)) hQ (k := 2) (Or.inl (by rw [hfin]; omega))
  have h3 := h2.trans (orthMinus_pRank_top_le_orthResDer hK (by omega : 1 ≤ r) hirr hℓ hℓ2)
  have hE : orthResDer K b c r = orthElementaryGroup (quadTail r (minusTailForm K b c)) :=
    commutator_orthogonalGroup_quadTail_minus hr hirr
  exact h3.trans (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt
    (MulEquiv.subgroupCongr hE)).le

theorem orthMinus_two_le_pRank_three {r f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup
      ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :=
  orthMinus_two_le_pRank hr hK hirr Nat.prime_three (by norm_num)
    (by rw [hK]; exact orthMinus_three_dvd_two_pow_sq_sub_one f)

end Rank

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
