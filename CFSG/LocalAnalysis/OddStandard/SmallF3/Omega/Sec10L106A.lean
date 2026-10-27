module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sl23_centralizer_Q8 (a : SL23)
    (ha : ∀ q : SL23, q ^ 4 = 1 → a * q = q * a) : a = 1 ∨ a = -1 :=
  (by decide : ∀ a : SL23, (∀ q : SL23, q ^ 4 = 1 → a * q = q * a) → a = 1 ∨ a = -1) a ha

private theorem oddCoreIn_le_X (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.oddCore X)

private theorem odd_card_oddCoreIn_X [Finite G] (X : Subgroup G) :
    Odd (Nat.card (oddCoreIn X)) :=
  CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X

private theorem twoCoreIn_le_X (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem conj_mem_twoCoreIn {X : Subgroup G} {x y : G} (hx : x ∈ X)
    (hy : y ∈ twoCoreIn X) : x * y * x⁻¹ ∈ twoCoreIn X := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * m * ⟨x, hx⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem m hm ⟨x, hx⟩
  · simp

theorem sec10KS_cent_Qi [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ a ∈ K1, (∀ b ∈ twoCoreIn K1, a * b = b * a) → a ∈ zpowers z := by
  obtain ⟨e⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  intro a ha hacentral
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  let eps : ↥K1 := ⟨z, hzK1⟩
  let al : ↥K1 := ⟨a, ha⟩
  have hzsq : eps * eps = 1 := by
    apply Subtype.ext
    change z * z = 1
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have heps : e eps * e eps = 1 := by rw [← map_mul, hzsq, map_one]
  have heps_ne : e eps ≠ 1 := by
    intro h
    have h1 : eps = 1 := e.injective (by rw [h, map_one])
    have hz1 : z = 1 := congrArg Subtype.val h1
    rw [hz1, orderOf_one] at hz2
    norm_num at hz2
  have hcomm_pcore : ∀ q ∈ CFSG.pCore 2 SL23, e al * q = q * e al := by
    intro q hq
    rw [← CFSG.pCore_map_iso 2 e] at hq
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hq
    have hm_two : K1.subtype m ∈ twoCoreIn K1 := Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
    have hcomm := hacentral (K1.subtype m) hm_two
    have hcomm' : al * m = m * al := by
      apply Subtype.ext
      change a * (m : G) = (m : G) * a
      exact hcomm
    calc e al * e m = e (al * m) := (map_mul e al m).symm
      _ = e (m * al) := by rw [hcomm']
      _ = e m * e al := map_mul e m al
  have hcommQ8 : ∀ q : SL23, q ^ 4 = 1 → e al * q = q * e al := by
    intro q hq
    exact hcomm_pcore q (by rw [sl23_pCore_eq_Q8, mem_sl23Q8]; exact hq)
  rcases sl23_centralizer_Q8 (e al) hcommQ8 with h1 | hneg
  · have hal : al = 1 := e.injective (by rw [h1, map_one])
    have ha1 : a = 1 := congrArg Subtype.val hal
    rw [ha1]
    exact Subgroup.one_mem _
  · have heps_neg : e eps = -1 := by
      rcases sl23_unique_involution (e eps) heps with h | h
      · exact absurd h heps_ne
      · exact h
    have hal_eps : al = eps := e.injective (hneg.trans heps_neg.symm)
    have haz : a = z := congrArg Subtype.val hal_eps
    rw [haz]
    exact Subgroup.mem_zpowers z

private theorem sec10_oddCore_sup_fst [Finite G] (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) {n a1 a2 : G}
    (hn : n ∈ oddCoreIn (K1 ⊔ K2)) (ha1 : a1 ∈ K1) (ha2 : a2 ∈ K2) (hna : n = a1 * a2) :
    a1 ∈ zpowers z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  have hQ2 : IsPGroup 2 (twoCoreIn K1) := by
    unfold twoCoreIn CFSG.inSubgroup
    exact (CFSG.pCore_isPGroup (G := ↥K1) (p := 2)).map K1.subtype
  have hKle : twoCoreIn K1 ≤ K1 := twoCoreIn_le_X K1
  have hnc : ∀ q ∈ twoCoreIn K1, n * q = q * n := by
    intro q hq
    have hqK : q ∈ K1 := hKle hq
    have hthird : n * q * n⁻¹ = a1 * q * a1⁻¹ := by
      rw [hna]
      have hq2 : a2 * q * a2⁻¹ = q := by
        rw [(hcomm12 q hqK a2 ha2).symm]
        group
      calc (a1 * a2) * q * (a1 * a2)⁻¹ = a1 * (a2 * q * a2⁻¹) * a1⁻¹ := by group
        _ = a1 * q * a1⁻¹ := by rw [hq2]
    have hcQ : n * q * n⁻¹ * q⁻¹ ∈ twoCoreIn K1 := by
      have h1 : n * q * n⁻¹ ∈ twoCoreIn K1 := by
        rw [hthird]
        exact conj_mem_twoCoreIn ha1 hq
      have h2 : q⁻¹ ∈ twoCoreIn K1 := Subgroup.inv_mem _ hq
      exact Subgroup.mul_mem _ h1 h2
    have hcN : n * q * n⁻¹ * q⁻¹ ∈ oddCoreIn (K1 ⊔ K2) := by
      have hqK' : q ∈ K1 ⊔ K2 := Subgroup.mem_sup_left hqK
      have hin : n⁻¹ ∈ oddCoreIn (K1 ⊔ K2) := Subgroup.inv_mem _ hn
      have hconj := Subgroup.mul_mem _ hn
        (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hqK' hin)
      simpa only [mul_assoc] using hconj
    have hodd : Odd (orderOf (n * q * n⁻¹ * q⁻¹)) :=
      Odd.of_dvd_nat (odd_card_oddCoreIn_X (K1 ⊔ K2))
        (Subgroup.orderOf_dvd_natCard _ hcN)
    have h2n : ¬ (2 ∣ orderOf (n * q * n⁻¹ * q⁻¹)) := fun h =>
      (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h)) hodd
    obtain ⟨k, hk⟩ := hQ2.exists_orderOf_eq_pow
      (⟨n * q * n⁻¹ * q⁻¹, hcQ⟩ : twoCoreIn K1)
    have hk' : orderOf (n * q * n⁻¹ * q⁻¹) = 2 ^ k := by
      change orderOf ((⟨n * q * n⁻¹ * q⁻¹, hcQ⟩ : twoCoreIn K1) : G) = 2 ^ k
      rw [Subgroup.orderOf_coe]
      exact hk
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact h
      · exfalso
        have h2k : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        exact h2n (by rw [hk']; exact h2k)
    have hone : orderOf (n * q * n⁻¹ * q⁻¹) = 1 := by
      rw [hk', hk0]
      norm_num
    have hc1 : n * q * n⁻¹ * q⁻¹ = 1 := orderOf_eq_one_iff.mp hone
    calc n * q = (n * q * n⁻¹ * q⁻¹) * (q * n) := by group
      _ = 1 * (q * n) := by rw [hc1]
      _ = q * n := one_mul _
  refine sec10KS_cent_Qi hP5 hC5 hpsp hctx a1 ha1 ?_
  intro q hq
  have hqK : q ∈ K1 := hKle hq
  have hnq : n * q = q * n := hnc q hq
  have ha2q : a2 * q = q * a2 := (hcomm12 q hqK a2 ha2).symm
  have key : a1 * q * a2 = q * a1 * a2 := by
    calc a1 * q * a2 = a1 * (q * a2) := by group
      _ = a1 * (a2 * q) := by rw [ha2q]
      _ = (a1 * a2) * q := by group
      _ = n * q := by rw [← hna]
      _ = q * n := hnq
      _ = q * (a1 * a2) := by rw [hna]
      _ = q * a1 * a2 := by group
  exact mul_right_cancel key

theorem sec10_oddCoreIn_sup_pockets [Finite G] (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) : oddCoreIn (K1 ⊔ K2) = ⊥ := by
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hcomm12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  refine le_antisymm ?_ bot_le
  intro n hn
  rw [Subgroup.mem_bot]
  have hnK : n ∈ K1 ⊔ K2 := oddCoreIn_le_X (K1 ⊔ K2) hn
  obtain ⟨a1, ha1, a2, ha2, hna⟩ := exists_mul_of_mem_sup_of_commute hcomm12 hnK
  have hq1 : a1 ∈ zpowers z := sec10_oddCore_sup_fst hP5 hC5 hpsp hctx hn ha1 ha2 hna
  have hna' : n = a2 * a1 := by rw [hna]; exact hcomm12 a1 ha1 a2 ha2
  have hnswap : n ∈ oddCoreIn (K2 ⊔ K1) := by rwa [sup_comm]
  have hq2 : a2 ∈ zpowers z :=
    sec10_oddCore_sup_fst hP5 hC5 hpsp hctx.swap hnswap ha2 ha1 hna'
  have hnz : n ∈ zpowers z := by
    rw [hna]
    exact Subgroup.mul_mem _ hq1 hq2
  have hdvd2 : orderOf n ∣ 2 := by
    have h := orderOf_dvd_of_mem_zpowers hnz
    rwa [hz2] at h
  have hmemN : n ∈ oddCoreIn (K1 ⊔ K2) := hn
  have hone : orderOf n = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · exfalso
      have h2dvd : 2 ∣ Nat.card (oddCoreIn (K1 ⊔ K2)) :=
        h ▸ Subgroup.orderOf_dvd_natCard _ hmemN
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2dvd))
        (odd_card_oddCoreIn_X (K1 ⊔ K2))
  exact orderOf_eq_one_iff.mp hone

end CFSG.OddStandard.SmallF3.Omega
