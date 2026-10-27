module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Lemma4

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_of_forall_isSylowOf {K : Subgroup G} {m : ℕ} (hm : m ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → ∃ Q, IsSylowOf q Q K ∧ Nat.card Q ∣ m) :
    Nat.card K ∣ m := by
  rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' hm, Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  · have : Fact q.Prime := ⟨hq⟩
    by_cases hqK : q ∣ Nat.card K
    · obtain ⟨Q, hQ, hQm⟩ := h q hq hqK
      rw [hQ.card_eq] at hQm
      exact (hq.pow_dvd_iff_le_factorization hm).mp hQm
    · rw [Nat.factorization_eq_zero_of_not_dvd hqK]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
    exact Nat.zero_le _

theorem eq_of_forall_exists_isSylowOf_le {A X : Subgroup G} (hAX : A ≤ X)
    (h : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → ∃ Q, IsSylowOf q Q X ∧ Q ≤ A) : A = X := by
  refine Subgroup.eq_of_le_of_card_ge hAX (Nat.le_of_dvd Nat.card_pos ?_)
  refine card_dvd_of_forall_isSylowOf Nat.card_pos.ne' fun q hq hqX => ?_
  obtain ⟨Q, hQ, hQA⟩ := h q hq hqX
  exact ⟨Q, hQ, Subgroup.card_dvd_of_le hQA⟩

omit [Finite G] in
theorem card_mul_of_inf_eq_bot {R Y : Subgroup G} (hRY : R ⊓ Y = ⊥) :
    Nat.card ((R : Set G) * (Y : Set G)) = Nat.card R * Nat.card Y := by
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient, mul_comm]
  congr 1
  rw [Nat.card_image_of_injOn]
  · rfl
  · intro a ha b hb hab
    have h := QuotientGroup.eq.mp hab
    have hmem : a⁻¹ * b ∈ R ⊓ Y := ⟨R.mul_mem (R.inv_mem ha) hb, h⟩
    rw [hRY, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem

theorem coe_eq_mul_of_card_dvd {K R Y : Subgroup G} (hRK : R ≤ K) (hYK : Y ≤ K)
    (hRY : R ⊓ Y = ⊥) (hdvd : Nat.card K ∣ Nat.card R * Nat.card Y) :
    (K : Set G) = (R : Set G) * Y := by
  have hsub : (R : Set G) * Y ⊆ K := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem (hRK ha) (hYK hb)
  symm
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_mul_of_inf_eq_bot hRY]
  exact Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) hdvd

theorem coe_eq_mul_of_isSylowOf {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {K R Y : Subgroup G} (hR : IsSylowOf p R K) (hY : IsSylowOf q Y K)
    (hK : ∀ d : ℕ, d.Prime → d ∣ Nat.card K → d = p ∨ d = q) :
    (K : Set G) = (R : Set G) * Y ∧ (K : Set G) = (Y : Set G) * R := by
  have hRY : R ⊓ Y = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hR.card_eq, hY.card_eq]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Fact.out).mpr hpq)
  have hdvd : Nat.card K ∣ Nat.card R * Nat.card Y := by
    refine card_dvd_of_forall_isSylowOf (Nat.mul_pos Nat.card_pos Nat.card_pos).ne' ?_
    intro d hd hdK
    rcases hK d hd hdK with rfl | rfl
    · exact ⟨R, hR, Dvd.intro _ rfl⟩
    · exact ⟨Y, hY, Dvd.intro_left _ rfl⟩
  refine ⟨coe_eq_mul_of_card_dvd hR.le hY.le hRY hdvd,
    coe_eq_mul_of_card_dvd hY.le hR.le (by rw [inf_comm, hRY]) (by rwa [mul_comm])⟩

theorem exists_invariant_hall {A X U : Subgroup G} (hA : IsPGroup 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX : Odd (Nat.card X)) (hUX : U ≤ X)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (π : Set Nat.Primes)
    (hUπ : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card U → q ∈ π) :
    ∃ P : Subgroup G, P ≤ X ∧ U ≤ P ∧ A ≤ Subgroup.normalizer (P : Set G) ∧
      (∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card P → q ∈ π) ∧
      (∀ q : Nat.Primes, q ∈ π → ¬ (q : ℕ) ∣ P.relIndex X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := Omnibus.conjActOn A X hAX
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hX
  have hUπ' : CFSG.IsPiSubgroup π (U.subgroupOf X) := by
    intro q hq
    apply hUπ q
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv] at hq
  have hU' : ∀ a : A, ∀ x ∈ U.subgroupOf X, a • x ∈ U.subgroupOf X := by
    intro a x hx
    exact (Subgroup.mem_normalizer_iff.mp (hAU a.2) x).mp hx
  obtain ⟨P₀, hP₀, hP₀inv, hUP₀⟩ := CFSG.SolvableHall.coprime_invariant_hall_containment
    hA hX.not_two_dvd_nat hsolv π (U.subgroupOf X) hUπ' hU'
  refine ⟨P₀.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hUX]
    exact Subgroup.map_mono hUP₀
  · intro a ha
    apply DataConstruction.mem_normalizer_of_conj_mem
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, hP₀inv ⟨a, ha⟩ z hz, rfl⟩
  · intro q hq
    rw [Subgroup.card_map_of_injective X.subtype_injective] at hq
    exact hP₀.p_in_pi_of_p_dvd_card q hq
  · intro q hqπ hq
    have : (P₀.map X.subtype).subgroupOf X = P₀ := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    rw [Subgroup.relIndex, this] at hq
    exact hP₀.p_in_pi_of_p_dvd_index q hq hqπ

theorem exists_inv_mul_mem_normalizer_of_complement {p : ℕ} [Fact p.Prime] {P₀ W : Subgroup G}
    (hP₀ : IsPGroup p P₀) (hWP : W ≤ Subgroup.normalizer (P₀ : Set G)) (hW : ¬ p ∣ Nat.card W)
    (hodd : Odd (Nat.card (P₀ ⊔ W : Subgroup G))) {y : G}
    (hy : y ∈ Subgroup.normalizer ((P₀ ⊔ W : Subgroup G) : Set G)) :
    ∃ v ∈ P₀, v⁻¹ * y ∈ Subgroup.normalizer (W : Set G) := by
  set B : Subgroup G := P₀ ⊔ W with hB
  have hsolv : Group.IsSolvable B := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hWB : W ≤ B := le_sup_right
  have hyW : conjSub y W ≤ B := by
    rw [← DataConstruction.conjSub_eq_self_of_mem hy]
    exact DataConstruction.conjSub_mono hWB
  have hPW : (P₀ : Set G) * W = W * P₀ := (Omnibus.mul_comm_of_le_normalizer hWP).symm
  have hBdvd : Nat.card B ∣ Nat.card P₀ * Nat.card W := card_sup_dvd_of_mul_comm hPW
  have hhall : ∀ W' : Subgroup G, W' ≤ B → Nat.card W' = Nat.card W →
      CFSG.IsHallSubgroup (primesNe p) (W'.subgroupOf B) := by
    intro W' hW'B hcard
    have hc : Nat.card (W'.subgroupOf B) = Nat.card W := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'B).toEquiv, hcard]
    refine ⟨fun q hq => ?_, fun q hq hqπ => ?_⟩
    · rw [hc] at hq
      intro hqp
      exact hW (hqp ▸ hq)
    · have hidx := (W'.subgroupOf B).card_mul_index
      rw [hc] at hidx
      have hidxdvd : (W'.subgroupOf B).index ∣ Nat.card P₀ := by
        have h1 : Nat.card W * (W'.subgroupOf B).index ∣ Nat.card W * Nat.card P₀ := by
          rw [hidx, mul_comm]
          exact hBdvd
        exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP₀
      rw [ha] at hidxdvd
      have := (Nat.prime_dvd_prime_iff_eq q.2 Fact.out).mp (q.2.dvd_of_dvd_pow (hq.trans hidxdvd))
      exact hqπ this
  obtain ⟨c, hc⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hsolv
    (hhall W hWB rfl) (hhall (conjSub y W) hyW (DataConstruction.card_conjSub y W))
  have hyc : conjSub y W = conjSub (c : G) W := by
    have h1 := congrArg (Subgroup.map B.subtype) hc
    rw [Subgroup.map_subgroupOf_eq_of_le hyW, Subgroup.map_map] at h1
    rw [h1]
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le hWB, TotallyInverted.conjSub,
      Subgroup.map_map]
    congr 1
  obtain ⟨v, hv, w, hw, hcvw⟩ := (mem_sup_iff_of_le_normalizer' hWP).mp c.2
  refine ⟨v, hv, ?_⟩
  rw [← DataConstruction.conjSub_eq_self_iff, ← DataConstruction.conjSub_conjSub, hyc, ← hcvw,
    ← DataConstruction.conjSub_conjSub, DataConstruction.conjSub_eq_self_of_mem
      (Subgroup.le_normalizer hw), DataConstruction.conjSub_inv_conjSub]

end CFSG.ABGTheoremB.V4
