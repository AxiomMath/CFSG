module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitnessCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitnessSelection

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped MatrixGroups

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_mul_flip {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t x : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (htord : orderOf t = 2) (hxB : x ∈ pairPointStabilizer H beta) (hxx : x * x = 1)
    (hxt : Commute x t) : orderOf (x * t) = 2 := by
  have htt : t * t = 1 := by rw [← pow_two, ← htord, pow_orderOf_eq_one]
  apply orderOf_eq_prime
  · rw [pow_two, mul_assoc, ← mul_assoc t, ← hxt.eq, mul_assoc, htt, mul_one, hxx]
  · intro h1
    have : t = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    apply pair_flip_not_mem_point hbeta ht
    rw [this]
    exact H.inv_mem (pairPointStabilizer_le_point H beta hxB)

theorem exists_odd_prime_dvd_two_pow_add_one {a : ℕ} (ha : 1 ≤ a) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ a + 1 := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ a + 1 ≠ 1 by omega)
  refine ⟨p, hp, ?_, hpd⟩
  rintro rfl
  have hodd : Odd (2 ^ a + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  exact hodd.not_two_dvd_nat hpd


theorem high_rank_pair_witness_tail {H : Subgroup G} {z₀ : G}
    (h₀ : MinimalInvolutionPointLocalFailure H z₀)
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z₀ beta)
    {u v : G} (huB : u ∈ pairPointStabilizer H beta) (hvB : v ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (hcuv : Commute u v)
    (huz : Commute u z₀) (hvz : Commute v z₀) (hut : Commute u t) (hvt : Commute v t)
    {a ε : ℕ} (ha : 1 ≤ a)
    (hm : Nat.card (conjugacyWithin H z₀) = (2 ^ a - 1) * (2 ^ a + 1) ^ ε)
    (hΔu : Nat.card (pointRoots H z₀ u) = 2 ^ (2 * a) - 1)
    (hΔv : Nat.card (pointRoots H z₀ v) = 2 ^ (2 * a) - 1)
    {x r f y : G}
    (hcase : ε = 2 ∧ x = u * v ∧ r = u ∧ f = v ∧ y = u ∧
        Nat.card (pointRoots H z₀ (u * v)) = 2 ^ a - 1 ∨
      ε = 3 ∧ x = u ∧ r = v ∧ f = u ∧ y = 1 ∧
        Nat.card (pointRoots H z₀ (u * v)) = 2 ^ (2 * a) - 1)
    (hF : FieldInvolutionOn (localInvolutionPointHull z₀ r) f a) :
    orderOf (x * t) = 2 ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ a + 1 →
        WitnessPrimeData H z₀ beta t u v (x * t) r a p) ∧
      ∀ γ : rightCosetSpace H, rightCosetTranslate H γ t = γ →
        ¬ Subgroup.centralizer ({x * t} : Set G) ≤ rightCosetStabilizer H γ ∧
        localInvolutionPointHull z₀ r ⊓ Subgroup.centralizer ({x * t} : Set G) ≤
          localInvolutionPointHull z₀ (x * t) ∧
        SubfieldCentralizer (localInvolutionPointHull z₀ r) (x * t) a ∧
        Nat.card (involutionPointClass z₀ ∩ (rightCosetStabilizer H γ : Set G) ∩
          (Subgroup.centralizer ({r} : Set G) : Set G) ∩
          (Subgroup.centralizer ({x * t} : Set G) : Set G) : Set G) = 2 ^ a - 1 ∧
        (4 ≤ 2 ^ a → 2 ≤ twoRank (localInvolutionPointHull z₀ (x * t))) := by
  have htord : orderOf t = 2 := order_two_of_mem_pointClass h₀.local_datum.distinguished_order ht.1
  have hsq : ∀ g : G, orderOf g = 2 → g * g = 1 := fun g hg => by
    rw [← pow_two, ← hg, pow_orderOf_eq_one]
  have hyfx : y * f = x := by
    rcases hcase with ⟨-, hx, -, hf, hy, -⟩ | ⟨-, hx, -, hf, hy, -⟩
    · rw [hx, hf, hy]
    · rw [hx, hf, hy, one_mul]
  have hxB : x ∈ pairPointStabilizer H beta := by
    rcases hcase with ⟨-, hx, -⟩ | ⟨-, hx, -⟩
    · rw [hx]; exact (pairPointStabilizer H beta).mul_mem huB hvB
    · rw [hx]; exact huB
  have hxx : x * x = 1 := by
    rcases hcase with ⟨-, hx, -⟩ | ⟨-, hx, -⟩
    · rw [hx, show u * v * (u * v) = (u * u) * (v * v) by
        rw [mul_assoc, ← mul_assoc v u v, ← hcuv.eq]; group, hsq u hu, hsq v hv, one_mul]
    · rw [hx]; exact hsq u hu
  have hxt : Commute x t := by
    rcases hcase with ⟨-, hx, -⟩ | ⟨-, hx, -⟩
    · rw [hx]; exact hut.mul_left hvt
    · rw [hx]; exact hut
  have hsord : orderOf (x * t) = 2 := orderOf_mul_flip hbeta ht htord hxB hxx hxt
  have hprime := fun (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ a + 1) =>
    high_rank_pair_prime_subgroup h₀ hcomm hR1 hbeta ht huB hvB hu hv huv hcuv huz hvz hut hvt
      ha hm hΔu hΔv (x := x) (by
        rcases hcase with ⟨h1, h2, -, -, -, h6⟩ | ⟨h1, h2, -, -, -, h6⟩
        · exact Or.inl ⟨h1, h2, h6⟩
        · exact Or.inr ⟨h1, h2, h6⟩) hp hp2 hpq
  have hrB : r ∈ pairPointStabilizer H beta := by
    rcases hcase with ⟨-, -, hr, -⟩ | ⟨-, -, hr, -⟩
    · rw [hr]; exact huB
    · rw [hr]; exact hvB
  have hrord : orderOf r = 2 := by
    rcases hcase with ⟨-, -, hr, -⟩ | ⟨-, -, hr, -⟩
    · rw [hr]; exact hu
    · rw [hr]; exact hv
  have hrz : Commute r z₀ := by
    rcases hcase with ⟨-, -, hr, -⟩ | ⟨-, -, hr, -⟩
    · rw [hr]; exact huz
    · rw [hr]; exact hvz
  have hrt : Commute r t := by
    rcases hcase with ⟨-, -, hr, -⟩ | ⟨-, -, hr, -⟩
    · rw [hr]; exact hut
    · rw [hr]; exact hvt
  have hfr : Commute f r := by
    rcases hcase with ⟨-, -, hr, hf, -⟩ | ⟨-, -, hr, hf, -⟩
    · rw [hr, hf]; exact hcuv.symm
    · rw [hr, hf]; exact hcuv
  have hft : Commute f t := by
    rcases hcase with ⟨-, -, -, hf, -⟩ | ⟨-, -, -, hf, -⟩
    · rw [hf]; exact hvt
    · rw [hf]; exact hut
  have hy : y = r ∨ y = 1 := by
    rcases hcase with ⟨-, -, hr, -, hy, -⟩ | ⟨-, -, -, -, hy, -⟩
    · exact Or.inl (hy.trans hr.symm)
    · exact Or.inr hy
  have hyft : y * f * t = x * t := by rw [hyfx]
  obtain ⟨p₀, hp₀, hp₀2, hp₀q⟩ := exists_odd_prime_dvd_two_pow_add_one ha
  obtain ⟨A₀, hA₀I, -, -, -, -, -, hA₀t, hA₀rel, hA₀s, -⟩ := hprime p₀ hp₀ hp₀2 hp₀q
  have hA₀B : A₀ ≤ pairPointStabilizer H beta := hA₀I.trans (pairOddCore_le H beta t).1
  have hA₀1 : A₀ ≠ ⊥ := by
    rintro rfl
    have h1 : ((⊥ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)).relIndex ⊥ = 1 :=
      Subgroup.relIndex_bot_right _
    rw [h1] at hA₀rel
    have : 1 < (p₀ ^ (Nat.factorization (2 ^ a + 1) p₀)) ^ 2 := by
      have hf := CFSG.ProperTwoGeneratedCore.HighRankPair.one_le_factorization hp₀ hp₀q
      have : 1 < p₀ ^ (Nat.factorization (2 ^ a + 1) p₀) :=
        Nat.one_lt_pow (by omega) hp₀.one_lt
      nlinarith
    omega
  rw [← hyft] at hA₀s ⊢
  have hpoint := high_rank_pair_point_data h₀ hcomm hR1 hbeta ht hrB hrord hrz hrt hfr hft hy
    (by rw [hyft]; exact hsord) ha hF ⟨A₀, hA₀B, hA₀s, hA₀t, hA₀1⟩
  obtain ⟨hLsM, hγ⟩ := hpoint
  refine ⟨by rw [hyft]; exact hsord, fun p hp hp2 hpq => ?_, hγ⟩
  obtain ⟨A, hAI, huA, hvA, htA, hAp, hAcyc, hAt, hArel, hAs, hAkey⟩ := hprime p hp hp2 hpq
  rw [← hyft] at hAs
  have hAB : A ≤ pairPointStabilizer H beta := hAI.trans (pairOddCore_le H beta t).1
  have hA1 : ⁅A, Subgroup.zpowers t⁆ ≠ ⊥ := by
    rw [hAt]
    rintro rfl
    have h1 : ((⊥ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)).relIndex ⊥ = 1 :=
      Subgroup.relIndex_bot_right _
    rw [h1] at hArel
    have : 1 < (p ^ (Nat.factorization (2 ^ a + 1) p)) ^ 2 := by
      have hf := CFSG.ProperTwoGeneratedCore.HighRankPair.one_le_factorization hp hpq
      have : 1 < p ^ (Nat.factorization (2 ^ a + 1) p) := Nat.one_lt_pow (by omega) hp.one_lt
      nlinarith
    omega
  have hAr : ¬ A ≤ Subgroup.centralizer ({r} : Set G) := by
    rcases hcase with ⟨-, -, hr, -⟩ | ⟨-, -, hr, -⟩
    · exact hAkey r (Or.inl hr)
    · exact hAkey r (Or.inr (Or.inl hr))
  exact ⟨A, hAI, huA, hvA, htA, hAp, hAcyc, hAt, hArel, hAs, hAr,
    moves_class_flip_fixed_points h₀ hcomm hR1 hbeta ht hAB hA1, hLsM A hAs hAt⟩


omit [Finite G] in
theorem witnessPrimeData_congr {H : Subgroup G} {z z₀ : G}
    (hhull : ∀ w : G, localInvolutionPointHull z₀ w = localInvolutionPointHull z w)
    {beta : rightCosetSpace H} {t u v s r : G} {a p : ℕ} :
    WitnessPrimeData H z₀ beta t u v s r a p ↔ WitnessPrimeData H z beta t u v s r a p := by
  unfold WitnessPrimeData
  rw [hhull]

theorem high_rank_pair_witness {G : Type u} [Group G] [Finite G]
    (hgen : PairGenerationTheorem G) (hNC : NoncentralPairActionTheorem G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    HighRankPairWitness H z beta t := by
  obtain ⟨z₀, u, v, a, ha, hz₀, h₀, hpoint, ht₀, huB, hvB, hu, hv, huv, hcuv, huz, hvz, hut,
    hvt, hFu, hFv, hΔu, hΔv, hΔW, huvcase⟩ :=
    high_rank_pair_square_field_selection h hgen hNC hbeta ht hrank
  have hroots := distinguishedRoots_eq_pointRoots h hpoint
  have hz₀D : z₀ ∈ involutionPointClass z := by
    rw [← original_point_class_intersection_eq_conjugacyWithin h.local_datum] at hz₀
    exact hz₀.1
  have hclass : involutionPointClass z₀ = involutionPointClass z :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime.pointClass_eq_of_mem hz₀D
  have hhull : ∀ w : G, localInvolutionPointHull z₀ w = localInvolutionPointHull z w := by
    intro w
    unfold localInvolutionPointHull
    rw [hclass]
  have hid := high_rank_pair_class_identity h₀ hbeta ht₀ huB hvB hu hv huv hcuv huz hvz hut hvt
  rw [hΔu, hΔv, hΔW] at hid
  have hFu₀ : FieldInvolutionOn (localInvolutionPointHull z₀ u) v a := by rw [hhull]; exact hFu
  have hFv₀ : FieldInvolutionOn (localInvolutionPointHull z₀ v) u a := by rw [hhull]; exact hFv
  rcases huvcase with hsub | ⟨hΔuv, hFuv⟩
  · have hΔuv_eq : pointRoots H z₀ (u * v) = pointRoots H z₀ u ∩ pointRoots H z₀ v := by
      rw [← pointRoots_mul_inter, Set.inter_eq_left.mpr hsub]
    have hΔuv : Nat.card (pointRoots H z₀ (u * v)) = 2 ^ a - 1 := by rw [hΔuv_eq, hΔW]
    rw [hΔuv] at hid
    have hm := class_size_eq_square ha hid
    obtain ⟨hsord, hprime, hγ⟩ := high_rank_pair_witness_tail h₀ hcomm hR1 hbeta ht₀ huB hvB
      hu hv huv hcuv huz hvz hut hvt ha hm hΔu hΔv (x := u * v) (r := u) (f := v) (y := u)
      (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hΔuv⟩) hFu₀
    refine ⟨z₀, u, v, a, 2, ha, Or.inl rfl, hz₀, huB, hvB, hu, hv, huv, hcuv, huz, hvz, hut,
      hvt, hFu, fieldInvolutionOn_nonInnerOn ha hFu, hFv, fieldInvolutionOn_nonInnerOn ha hFv,
      by rw [hroots]; exact hΔu, by rw [hroots]; exact hΔv,
      by rw [hroots, hroots]; exact hΔW, by rw [← hpoint]; exact hm,
      fun _ => by rw [hroots, hroots, hroots]; exact hΔuv_eq, fun h3 => absurd h3 (by norm_num),
      u * v * t, u, Or.inl ⟨rfl, rfl, rfl⟩, hsord,
      fun p hp hp2 hpq => (witnessPrimeData_congr hhull).mp (hprime p hp hp2 hpq), ?_⟩
    intro γ hγt
    obtain ⟨h1, h2, h3, h4, h5⟩ := hγ γ hγt
    rw [hhull, hhull] at h2
    rw [hhull] at h3 h5
    rw [hclass] at h4
    exact ⟨h1, h2, h3, h4, h5⟩
  · rw [hΔuv] at hid
    have hm := class_size_eq_cube ha hid
    obtain ⟨hsord, hprime, hγ⟩ := high_rank_pair_witness_tail h₀ hcomm hR1 hbeta ht₀ huB hvB
      hu hv huv hcuv huz hvz hut hvt ha hm hΔu hΔv (x := u) (r := v) (f := u) (y := 1)
      (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, hΔuv⟩) hFv₀
    obtain ⟨F, _, hF, φ, -⟩ := hFuv
    refine ⟨z₀, u, v, a, 3, ha, Or.inr rfl, hz₀, huB, hvB, hu, hv, huv, hcuv, huz, hvz, hut,
      hvt, hFu, fieldInvolutionOn_nonInnerOn ha hFu, hFv, fieldInvolutionOn_nonInnerOn ha hFv,
      by rw [hroots]; exact hΔu, by rw [hroots]; exact hΔv,
      by rw [hroots, hroots]; exact hΔW, by rw [← hpoint]; exact hm,
      fun h2 => absurd h2 (by norm_num), fun _ => ⟨by rw [hroots]; exact hΔuv, F, inferInstance,
        hF, ⟨φ⟩⟩,
      u * t, v, Or.inr ⟨rfl, rfl, rfl⟩, hsord,
      fun p hp hp2 hpq => (witnessPrimeData_congr hhull).mp (hprime p hp hp2 hpq), ?_⟩
    intro γ hγt
    obtain ⟨h1, h2, h3, h4, h5⟩ := hγ γ hγt
    rw [hhull, hhull] at h2
    rw [hhull] at h3 h5
    rw [hclass] at h4
    exact ⟨h1, h2, h3, h4, h5⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
