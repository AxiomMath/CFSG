module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HeisThirteen
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersTools
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ElevenSteps

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {N : Subgroup G} [Finite N] {a : G}
    (h : ∀ n ∈ N, a * n * a⁻¹ ∈ N) : a ∈ Subgroup.normalizer (N : Set G) := by
  let φ : N → N := fun n => ⟨a * n * a⁻¹, h n n.2⟩
  have hφ : Function.Injective φ := by
    intro m n hmn
    have := congrArg Subtype.val hmn
    simp only [φ, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact h g
  · intro hg
    obtain ⟨n, hn⟩ := hsurj ⟨a * g * a⁻¹, hg⟩
    have := congrArg Subtype.val hn
    simp only [φ, mul_left_inj, mul_right_inj] at this
    rw [← this]
    exact n.2

theorem centralizes_of_inverts {G : Type*} [Group G] {N : Subgroup G} {v a : G}
    (hv : ∀ n ∈ N, v * n * v⁻¹ = n⁻¹) (ha : ∀ n ∈ N, a⁻¹ * n * a⁻¹⁻¹ ∈ N) {n : G} (hn : n ∈ N) :
    (v * (a * v * a⁻¹)) * n * (v * (a * v * a⁻¹))⁻¹ = n := by
  have h1 : (a * v * a⁻¹) * n * (a * v * a⁻¹)⁻¹ = n⁻¹ := by
    have := hv _ (ha n hn)
    rw [inv_inv] at this
    calc (a * v * a⁻¹) * n * (a * v * a⁻¹)⁻¹ = a * (v * (a⁻¹ * n * a) * v⁻¹) * a⁻¹ := by group
      _ = a * (a⁻¹ * n * a)⁻¹ * a⁻¹ := by rw [this]
      _ = n⁻¹ := by group
  calc (v * (a * v * a⁻¹)) * n * (v * (a * v * a⁻¹))⁻¹ =
      v * ((a * v * a⁻¹) * n * (a * v * a⁻¹)⁻¹) * v⁻¹ := by group
    _ = v * n⁻¹ * v⁻¹ := by rw [h1]
    _ = (v * n * v⁻¹)⁻¹ := by group
    _ = n := by rw [hv n hn, inv_inv]

theorem gw_vW13_eq : gw vW13 = xGmat := rhoG_z_eq_xGmat

theorem vW13_mul_self : gw vW13 * gw vW13 = 1 := by
  show rhoG (true, 0, 0) * rhoG (true, 0, 0) = 1
  rw [← rhoG_mul, show Model.Pauli.mul (true, 0, 0) (true, 0, 0) = (false, 0, 0) by decide, rhoG_one]


theorem conj_mem_core {a : Gmat} {k : ℕ} (ha : a * gw genD13W1 * a⁻¹ = gw genD13W1 ^ k)
    (hk : gw genD13W1 ^ k ≠ 1) {n : Gmat}
    (hn : n ∈ GLAPPrimeCoreOf 13 (Subgroup.centralizer ({gw genD13W1} : Set Gmat))) :
    a * n * a⁻¹ ∈ GLAPPrimeCoreOf 13 (Subgroup.centralizer ({gw genD13W1} : Set Gmat)) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h := conj_mem_gLAPPrimeCoreOf_conj (m := a) (by norm_num : Nat.Prime 13) hn
  rwa [ha, centralizer_pow_eq_of_prime orderOf_c13 hk] at h

theorem gLAPPrimeCoreOf_c13_eq_bot
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 13
      (Subgroup.centralizer ({gw genD13W1} : Set Gmat))))) :
    GLAPPrimeCoreOf 13 (Subgroup.centralizer ({gw genD13W1} : Set Gmat)) = ⊥ := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set N := GLAPPrimeCoreOf 13 (Subgroup.centralizer ({gw genD13W1} : Set Gmat)) with hNdef
  obtain ⟨f0, f1, f2, f3, f4, f5, f7, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, n1, n2, n3, n4, n5, n6, n7⟩ := thirteen_b_facts
  obtain ⟨hg13, hd13, hc13, hcg, hcc2, hdg, hc1, -⟩ := d13_gw_facts
  have f6 : gw bW13 ^ 13 = 1 := by
    have h := heis_pow_thirteen hcg hcc2 hdg hc13 hg13 hd13 1 9 5
    rwa [pow_one, ← gw_bW13] at h
  have f8 : gw bpW13 ^ 13 = 1 := by
    have h := heis_pow_thirteen hcg hcc2 hdg hc13 hg13 hd13 1 5 10
    rwa [pow_one, ← gw_bpW13] at h
  have hco := orderOf_c13
  have hv2 := vW13_mul_self
  have hvinv : (gw vW13)⁻¹ = gw vW13 := inv_eq_of_mul_eq_one_right hv2
  have htinv : (gw tW13)⁻¹ = gw tW13 := inv_eq_of_mul_eq_one_right f3
  have hNc : N ≤ Subgroup.centralizer ({gw genD13W1} : Set Gmat) := GLAPPrimeCoreOf_le _
  have h13N : ¬ 13 ∣ Nat.card N := fun h =>
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).1
      (coprime_card_GLAPPrimeCoreOf (by norm_num) _) h
  have hpow : ∀ k : ℕ, k % 13 ≠ 0 → gw genD13W1 ^ k ≠ 1 := by
    intro k hk h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hco] at this
    exact hk (Nat.mod_eq_zero_of_dvd this)
  have hCc : ∀ a : Gmat, a * gw genD13W1 = gw genD13W1 * a → ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
    intro a ha n hn
    exact GLAPPrimeCoreOf_conj_mem a (Subgroup.mem_centralizer_singleton_iff.2 ha) n hn
  have hNv : N ⊓ Subgroup.centralizer ({gw vW13} : Set Gmat) = ⊥ := by
    refine inf_centralizer_eq_bot_of_twoB (h := 1) (by rw [one_mul, inv_one, mul_one, gw_vW13_eq])
      f0.symm hco hNc hodd h13N f11.symm f12.symm (hCc _ f12.symm) f10 ?_
    rw [pow_two]; exact n5
  have hvN : ∀ n ∈ N, gw vW13 * n * (gw vW13)⁻¹ ∈ N := hCc _ f0
  have hvinvN : ∀ {n : Gmat}, n ∈ N → gw vW13 * n * (gw vW13)⁻¹ = n⁻¹ := fun hn =>
    CFSG.Wreathed.OriginalAllPrime.ModelSignalizers.conj_eq_inv_of_inf_centralizer_eq_bot
      hv2 (mem_normalizer_of_conj_mem hvN) hNv hn
  have hgN : ∀ n ∈ N, gw genD13W0 * n * (gw genD13W0)⁻¹ = n := by
    intro n hn
    have ha : ∀ m ∈ N, (gw genD13W0 ^ 6)⁻¹ * m * (gw genD13W0 ^ 6)⁻¹⁻¹ ∈ N := by
      intro m hm
      refine hCc _ ?_ m hm
      exact (((Commute.symm hcg).pow_left 6).inv_left).eq
    have h := centralizes_of_inverts (fun m hm => hvinvN hm) ha hn
    have hg : gw vW13 * (gw genD13W0 ^ 6 * gw vW13 * (gw genD13W0 ^ 6)⁻¹) = gw genD13W0 := by
      have h7 : (gw genD13W0 ^ 6)⁻¹ = gw genD13W0 ^ 7 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, hg13]
      rw [h7, ← mul_assoc, ← mul_assoc]
      exact f1
    rwa [hg] at h
  have hc2N : ∀ n ∈ N, (gw genD13W2 * gw genD13W1 ^ 4) * n *
      (gw genD13W2 * gw genD13W1 ^ 4)⁻¹ = n := by
    intro n hn
    have ha : ∀ m ∈ N, (gw genD13W2 ^ 6)⁻¹ * m * (gw genD13W2 ^ 6)⁻¹⁻¹ ∈ N := by
      intro m hm
      refine hCc _ ?_ m hm
      exact (((Commute.symm hcc2).pow_left 6).inv_left).eq
    have h := centralizes_of_inverts (fun m hm => hvinvN hm) ha hn
    have hg : gw vW13 * (gw genD13W2 ^ 6 * gw vW13 * (gw genD13W2 ^ 6)⁻¹) =
        gw genD13W2 * gw genD13W1 ^ 4 := by
      have h7 : (gw genD13W2 ^ 6)⁻¹ = gw genD13W2 ^ 7 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, d13_gw_facts.2.1]
      rw [h7, ← mul_assoc, ← mul_assoc]
      exact f2
    rwa [hg] at h
  have hcent : ∀ x ∈ Subgroup.closure ({gw genD13W0, gw genD13W2 * gw genD13W1 ^ 4,
      gw genD13W1} : Set Gmat), ∀ n ∈ N, x * n = n * x := by
    intro x hx
    have hle : Subgroup.closure ({gw genD13W0, gw genD13W2 * gw genD13W1 ^ 4,
        gw genD13W1} : Set Gmat) ≤ Subgroup.centralizer (N : Set Gmat) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro n hn
      rcases hy with rfl | rfl | rfl
      · have := hgN n hn
        calc n * gw genD13W0 = gw genD13W0 * n * (gw genD13W0)⁻¹ * gw genD13W0 := by rw [this]
          _ = gw genD13W0 * n := by group
      · have := hc2N n hn
        calc n * (gw genD13W2 * gw genD13W1 ^ 4) = (gw genD13W2 * gw genD13W1 ^ 4) * n *
              (gw genD13W2 * gw genD13W1 ^ 4)⁻¹ * (gw genD13W2 * gw genD13W1 ^ 4) := by rw [this]
          _ = (gw genD13W2 * gw genD13W1 ^ 4) * n := by group
      · exact (Subgroup.mem_centralizer_singleton_iff.1 (hNc hn))
    intro n hn
    exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) n hn).symm
  have hmemS : ∀ a b k : ℕ, gw genD13W1 ^ a * gw genD13W2 ^ b * gw genD13W0 ^ k ∈
      Subgroup.closure ({gw genD13W0, gw genD13W2 * gw genD13W1 ^ 4,
        gw genD13W1} : Set Gmat) := by
    intro a b k
    have hg : gw genD13W0 ∈ Subgroup.closure ({gw genD13W0, gw genD13W2 * gw genD13W1 ^ 4,
        gw genD13W1} : Set Gmat) := Subgroup.subset_closure (by simp)
    have hc : gw genD13W1 ∈ Subgroup.closure ({gw genD13W0, gw genD13W2 * gw genD13W1 ^ 4,
        gw genD13W1} : Set Gmat) := Subgroup.subset_closure (by simp)
    have hc2c : gw genD13W2 * gw genD13W1 ^ 4 ∈ Subgroup.closure ({gw genD13W0,
        gw genD13W2 * gw genD13W1 ^ 4, gw genD13W1} : Set Gmat) := Subgroup.subset_closure (by simp)
    have hc2 : gw genD13W2 ∈ Subgroup.closure ({gw genD13W0, gw genD13W2 * gw genD13W1 ^ 4,
        gw genD13W1} : Set Gmat) := by
      have := Subgroup.mul_mem _ hc2c (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc 4))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hc a)
      (Subgroup.pow_mem _ hc2 b)) (Subgroup.pow_mem _ hg k)
  have hNb : N ≤ Subgroup.centralizer ({gw bW13} : Set Gmat) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff, gw_bW13]
    have := hcent _ (by simpa using hmemS 5 9 1) n hn
    simpa using this.symm
  have hNb' : N ≤ Subgroup.centralizer ({gw bpW13} : Set Gmat) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff, gw_bpW13]
    have := hcent _ (by simpa using hmemS 10 5 1) n hn
    simpa using this.symm
  have hbo : orderOf (gw bW13) = 13 := orderOf_eq_prime f6 n3
  have hbo' : orderOf (gw bpW13) = 13 := orderOf_eq_prime f8 n4
  have htc : gw tW13 * gw genD13W1 * (gw tW13)⁻¹ = gw genD13W1 ^ 12 := by
    rw [htinv]
    have h12 : gw genD13W1 ^ 12 = (gw genD13W1)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hc13]
    rw [h12, eq_inv_iff_mul_eq_one]
    exact f5
  have hvtv : gw vtW13 = gw tW13 * gw vW13 := gw_vtW13
  have hvtc : gw vtW13 * gw genD13W1 * (gw vtW13)⁻¹ = gw genD13W1 ^ 12 := by
    rw [hvtv, mul_inv_rev, hvinv]
    calc gw tW13 * gw vW13 * gw genD13W1 * (gw vW13 * (gw tW13)⁻¹) =
        gw tW13 * (gw vW13 * gw genD13W1 * gw vW13) * (gw tW13)⁻¹ := by group
      _ = gw tW13 * gw genD13W1 * (gw tW13)⁻¹ := by
          rw [f0, mul_assoc (gw genD13W1), hv2, mul_one]
      _ = gw genD13W1 ^ 12 := htc
  have hwtc : gw wtW13 * gw genD13W1 * (gw wtW13)⁻¹ = gw genD13W1 ^ 8 := by
    rw [f16, mul_inv_cancel_right]
  have hwvtc : gw wvtW13 * gw genD13W1 * (gw wvtW13)⁻¹ = gw genD13W1 ^ 8 := by
    rw [f20, mul_inv_cancel_right]
  have hNt : N ⊓ Subgroup.centralizer ({gw tW13} : Set Gmat) = ⊥ := by
    refine inf_centralizer_eq_bot_of_twoB (h := gw htW13) ?_ f7 hbo hNb hodd h13N f14.symm
      f15.symm (fun n hn => conj_mem_core hwtc (hpow 8 (by norm_num)) hn) f13 ?_
    · rw [f21, mul_inv_cancel_right, gw_vW13_eq]
    · rw [pow_two]; exact n6
  have hNvt : N ⊓ Subgroup.centralizer ({gw vtW13} : Set Gmat) = ⊥ := by
    refine inf_centralizer_eq_bot_of_twoB (h := gw hvtW13) ?_ f9 hbo' hNb' hodd h13N f18.symm
      f19.symm (fun n hn => conj_mem_core hwvtc (hpow 8 (by norm_num)) hn) f17 ?_
    · rw [f22, mul_inv_cancel_right, gw_vW13_eq]
    · rw [pow_two]; exact n7
  have htN : ∀ {n : Gmat}, n ∈ N → gw tW13 * n * (gw tW13)⁻¹ = n⁻¹ := fun hn =>
    CFSG.Wreathed.OriginalAllPrime.ModelSignalizers.conj_eq_inv_of_inf_centralizer_eq_bot
      f3 (mem_normalizer_of_conj_mem fun n hn => conj_mem_core htc (hpow 12 (by norm_num)) hn)
      hNt hn
  have hvt2 : gw vtW13 * gw vtW13 = 1 := by
    rw [hvtv]
    calc gw tW13 * gw vW13 * (gw tW13 * gw vW13) = gw tW13 * (gw vW13 * gw tW13) * gw vW13 := by
          group
      _ = gw tW13 * (gw tW13 * gw vW13) * gw vW13 := by rw [f4]
      _ = (gw tW13 * gw tW13) * (gw vW13 * gw vW13) := by group
      _ = 1 := by rw [f3, hv2, one_mul]
  have hvtN : ∀ {n : Gmat}, n ∈ N → gw vtW13 * n * (gw vtW13)⁻¹ = n⁻¹ := fun hn =>
    CFSG.Wreathed.OriginalAllPrime.ModelSignalizers.conj_eq_inv_of_inf_centralizer_eq_bot
      hvt2 (mem_normalizer_of_conj_mem fun n hn => conj_mem_core hvtc (hpow 12 (by norm_num)) hn)
      hNvt hn
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hcen : gw vW13 * n * (gw vW13)⁻¹ = n := by
    have hv : gw vW13 = gw tW13 * gw vtW13 := by
      rw [hvtv, ← mul_assoc, f3, one_mul]
    rw [hv]
    calc gw tW13 * gw vtW13 * n * (gw tW13 * gw vtW13)⁻¹ =
        gw tW13 * (gw vtW13 * n * (gw vtW13)⁻¹) * (gw tW13)⁻¹ := by group
      _ = gw tW13 * n⁻¹ * (gw tW13)⁻¹ := by rw [hvtN hn]
      _ = (gw tW13 * n * (gw tW13)⁻¹)⁻¹ := by group
      _ = n := by rw [htN hn, inv_inv]
  have hinv := hvinvN hn
  rw [hcen] at hinv
  have h2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two]; nth_rewrite 2 [hinv]; exact mul_inv_cancel n)
  have hodd' : Odd (orderOf n) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hn)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd'; exact absurd hodd' (by decide)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
