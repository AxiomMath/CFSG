module

public import CFSG.ClassicalInvolution.Q3.M11Exact
public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Generic Equiv

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_of_normal_odd_of_card_eq_48 {C N : Subgroup G} (hC : Nat.card C = 48)
    (hNC : N ≤ C) (hodd : Odd (Nat.card N)) (hnorm : ∀ c ∈ C, ∀ y ∈ N, c * y * c⁻¹ ∈ N)
    {a b : G} (ha : a ∈ C) (hb : b ∈ C) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hab : b ∉ Subgroup.zpowers a) : N = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card N ∣ 48 := hC ▸ Subgroup.card_dvd_of_le hNC
  have hcases : Nat.card N = 1 ∨ Nat.card N = 3 := by
    have h := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hall : ∀ d ∈ Nat.divisors 48, Odd d → d = 1 ∨ d = 3 := by decide
    exact hall _ h hodd
  rcases hcases with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq N h1
  exfalso
  have hN' : (N.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  have hcardN' : Nat.card (N.subgroupOf C) = 3 := by
    rw [← h3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
  have hpN' : IsPGroup 3 (N.subgroupOf C) := IsPGroup.of_card (n := 1) (by rw [hcardN', pow_one])
  have hmem : ∀ g ∈ C, orderOf g = 3 → g ∈ N := by
    intro g hg hg3
    set g' : ↥C := ⟨g, hg⟩ with hg'
    have hog' : orderOf g' = 3 := by rw [hg', Subgroup.orderOf_mk]; exact hg3
    have hpA : IsPGroup 3 (Subgroup.zpowers g') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hog', pow_one])
    obtain ⟨P, hP⟩ := hpA.exists_le_sylow
    have hNP : N.subgroupOf C ≤ P := hpN'.le_sylow_of_normal P
    have hPcard : Nat.card P ≤ 3 := by
      obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
      have hdP : Nat.card P ∣ 48 := hC ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup ↥C)
      rw [hk] at hdP ⊢
      by_contra hlt
      have hk2 : 2 ≤ k := by
        by_contra hk2
        exact hlt ((Nat.pow_le_pow_right (by norm_num) (by omega : k ≤ 1)).trans_eq (pow_one 3))
      have : 9 ∣ 48 := (pow_dvd_pow 3 hk2).trans hdP
      omega
    have hEq : N.subgroupOf C = (P : Subgroup ↥C) :=
      Subgroup.eq_of_le_of_card_ge hNP (by rw [hcardN']; exact hPcard)
    have : g' ∈ N.subgroupOf C := by
      rw [hEq]
      exact hP (Subgroup.mem_zpowers g')
    exact Subgroup.mem_subgroupOf.mp this
  have hza : Subgroup.zpowers a = N := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hmem a ha ha3
    · rw [Nat.card_zpowers, ha3, h3]
  have hzb : Subgroup.zpowers b ≤ N := by
    rw [Subgroup.zpowers_le]
    exact hmem b hb hb3
  exact hab (hza ▸ hzb (Subgroup.mem_zpowers b))

end Abstract

section M11

private def m11N1Word : List ℕ := [1, 0, 1, 1, 0, 3, 0, 1, 1, 0, 1, 1]

private def m11N2Word : List ℕ := [1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1]

private theorem m11SdX_comm : m11SdX * m11SdX ^ 4 = m11SdX ^ 4 * m11SdX := by
  rw [← pow_succ', pow_succ]

private theorem m11SdY_comm : m11SdY * m11SdX ^ 4 = m11SdX ^ 4 * m11SdY := by decide +kernel

private theorem m11SdZ_ne_one : m11SdX ^ 4 ≠ 1 := by decide +kernel

private theorem m11SdZ_sq : (m11SdX ^ 4) ^ 2 = 1 := by decide +kernel

private theorem m11N1_comm :
    m11Eval m11N1Word * m11SdX ^ 4 = m11SdX ^ 4 * m11Eval m11N1Word := by decide +kernel

private theorem m11N2_comm :
    m11Eval m11N2Word * m11SdX ^ 4 = m11SdX ^ 4 * m11Eval m11N2Word := by decide +kernel

private theorem m11N1_cube : m11Eval m11N1Word ^ 3 = 1 := by decide +kernel

private theorem m11N2_cube : m11Eval m11N2Word ^ 3 = 1 := by decide +kernel

private theorem m11N1_ne_one : m11Eval m11N1Word ≠ 1 := by decide +kernel

private theorem m11N2_ne_one : m11Eval m11N2Word ≠ 1 := by decide +kernel

private theorem m11N2_ne_pow : ∀ k : Fin 3, m11Eval m11N2Word ≠ m11Eval m11N1Word ^ k.val := by
  decide +kernel

private theorem orderOf_m11SdZ : orderOf m11SdZ = 2 := by
  rw [m11SdZ, Subgroup.orderOf_mk]
  exact orderOf_eq_prime m11SdZ_sq m11SdZ_ne_one

private theorem orderOf_m11N1 : orderOf (m11Conj m11N1Word) = 3 := by
  rw [m11Conj, Subgroup.orderOf_mk]
  exact orderOf_eq_prime m11N1_cube m11N1_ne_one

private theorem orderOf_m11N2 : orderOf (m11Conj m11N2Word) = 3 := by
  rw [m11Conj, Subgroup.orderOf_mk]
  exact orderOf_eq_prime m11N2_cube m11N2_ne_one

private theorem m11N2_not_mem_zpowers :
    m11Conj m11N2Word ∉ Subgroup.zpowers (m11Conj m11N1Word) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hk3 : m11Conj m11N1Word ^ k = m11Conj m11N1Word ^ (k % 3) := by
    have := zpow_mod_orderOf (m11Conj m11N1Word) k
    rw [orderOf_m11N1] at this
    simpa using this.symm
  have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have hlt : (k % 3).toNat < 3 := by omega
  have hj : m11Conj m11N1Word ^ (k % 3).toNat = m11Conj m11N2Word := by
    rw [← hk, hk3, ← zpow_natCast, Int.toNat_of_nonneg hnn]
  exact m11N2_ne_pow ⟨(k % 3).toNat, hlt⟩ (by simpa using (congrArg Subtype.val hj).symm)

private theorem m11SdS_le_centralizer :
    m11SdS ≤ Subgroup.centralizer ({m11SdZ} : Set ↥NativeSporadic.M11) := by
  rw [m11SdS, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext m11SdX_comm)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext m11SdY_comm)

private theorem m11N1_mem :
    m11Conj m11N1Word ∈ Subgroup.centralizer ({m11SdZ} : Set ↥NativeSporadic.M11) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext m11N1_comm)

private theorem m11N2_mem :
    m11Conj m11N2Word ∈ Subgroup.centralizer ({m11SdZ} : Set ↥NativeSporadic.M11) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext m11N2_comm)

private theorem card_centralizer_m11SdZ :
    Nat.card (Subgroup.centralizer ({m11SdZ} : Set ↥NativeSporadic.M11)) = 48 := by
  have h16 := Subgroup.card_dvd_of_le m11SdS_le_centralizer
  rw [card_m11SdS] at h16
  have h3 := Subgroup.orderOf_dvd_natCard _ m11N1_mem
  rw [orderOf_m11N1] at h3
  have hle := card_centralizer_le_of_orderOf_eq_two orderOf_m11SdZ
  have hpos := Nat.card_pos (α := Subgroup.centralizer ({m11SdZ} : Set ↥NativeSporadic.M11))
  omega

private theorem oddCoreIn_centralizer_m11SdZ :
    oddCoreIn (Subgroup.centralizer ({m11SdZ} : Set ↥NativeSporadic.M11)) = ⊥ :=
  eq_bot_of_normal_odd_of_card_eq_48 card_centralizer_m11SdZ (oddCoreIn_le _)
    (odd_card_oddCoreIn _) (fun _ hc _ hy => conj_mem_oddCoreIn hc hy) m11N1_mem m11N2_mem
    orderOf_m11N1 orderOf_m11N2 m11N2_not_mem_zpowers

theorem m11OddCentralizerFree : M11OddCentralizerFree := by
  intro t ht
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_m11SdZ_of_orderOf_eq_two ht)
  have hz : g⁻¹ * t * g⁻¹⁻¹ = m11SdZ := by rw [← hg]; group
  have hmap := CFSG.ClassicalInvolution.map_conj_centralizer_singleton g⁻¹ t
  rw [hz] at hmap
  have hle := map_oddCoreIn_le (MulAut.conj g⁻¹).toMonoidHom hmap
  rw [oddCoreIn_centralizer_m11SdZ, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp hle

theorem lieSystemOddCentralizer3_of_modelFacts (h0 : ModelClauseZero)
    (h1 : ModelOddCentralizerFree3) : LieSystemOddCentralizer3 :=
  lieSystemOddCentralizer3_of_models h0 h1 m11Facts m11OddCentralizerFree

end M11

end CFSG.ClassicalInvolution.Q3
