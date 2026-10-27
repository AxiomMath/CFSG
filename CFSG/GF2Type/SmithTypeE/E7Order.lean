module

public import CFSG.LargeExtraspecial.S14C12TOrd
public import CFSG.LargeExtraspecial.S14C13Model
public import CFSG.LargeExtraspecial.S12DWCount
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import all CFSG.Timmesfeld.Orders.Distinct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup Module CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.GroupTheory.WeirSylow

theorem card_timmesfeldOmegaPlus_six :
    Nat.card (timmesfeldOmegaPlus 6) = 2 ^ 30 * 46591793325 := by
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)
  have h12 : finrank (ZMod 2) (Fin 6 ⊕ Fin 6 → ZMod 2) = 2 * 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨e⟩ := nonempty_omegaGroup_equiv_omegaPlus hQ h12 (by norm_num)
    (isPlusType_quadPlus (ZMod 2) 6)
  rw [← Nat.card_congr e.toEquiv]
  have h2 := S12DW.card_orthogonalGroup_eq hQ
  have h1 := natCard_orthogonalGroup_quadPlus (K := ZMod 2) 5
  rw [Nat.card_zmod] at h1
  have h3 : ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2))) : ℕ) : ℤ) =
      2 * (2 ^ 30 * 46591793325) := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, h1]
    decide
  omega

theorem ordE7_two : ordE7 2 = 2 ^ 63 * (262143 * 16383 * 4095 * 1023 * 255 * 63 * 3) := by
  decide

variable {G : Type} [Group G] [Finite G]

theorem card_M_of_E7 (S : Setting G) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) :
    Nat.card S.M = 2 ^ 63 * 46591793325 := by
  obtain ⟨e⟩ := hO
  rw [card_M_eq_card_Q_mul, S.card_Q_eq, hw, Nat.card_congr e.toEquiv,
    card_timmesfeldOmegaPlus_six]
  ring

theorem factorization_card_of_E7 (S : Setting G) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) :
    (Nat.card G).factorization 2 = 63 := by
  have hodd : Odd S.M.index := Nat.odd_iff.mpr (by have := not_two_dvd_index_M S; omega)
  rw [← S.M.card_mul_index, card_M_of_E7 S hw hO,
    show 2 ^ 63 * 46591793325 * S.M.index = 2 ^ 63 * (46591793325 * S.M.index) by ring]
  exact factorization_two_pow_mul_odd ((by decide : Odd 46591793325).mul hodd)

theorem seventeen_dvd_card_of_E7 (S : Setting G) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) : 17 ∣ Nat.card G := by
  refine dvd_trans ?_ (card_subgroup_dvd_card S.M)
  rw [card_M_of_E7 S hw hO]
  norm_num

theorem card_M_of_E8
    (S : Setting G) (hw : S.width = 28) (hE : LieModel S.Mbar .E7 0 2 1) :
    Nat.card S.M = 2 ^ 120 * (262143 * 16383 * 4095 * 1023 * 255 * 63 * 3) := by
  rw [card_M_eq_card_Q_mul, S.card_Q_eq, hw, A2Mod.Ord.card_of_lieModel_E7 hE, ordE7_two]
  ring

theorem factorization_card_of_E8
    (S : Setting G) (hw : S.width = 28) (hE : LieModel S.Mbar .E7 0 2 1) :
    (Nat.card G).factorization 2 = 120 := by
  have hodd : Odd S.M.index := Nat.odd_iff.mpr (by have := not_two_dvd_index_M S; omega)
  rw [← S.M.card_mul_index, card_M_of_E8 S hw hE,
    show 2 ^ 120 * (262143 * 16383 * 4095 * 1023 * 255 * 63 * 3) * S.M.index =
      2 ^ 120 * ((262143 * 16383 * 4095 * 1023 * 255 * 63 * 3) * S.M.index) by ring]
  exact factorization_two_pow_mul_odd ((by decide :
    Odd (262143 * 16383 * 4095 * 1023 * 255 * 63 * 3)).mul hodd)

theorem dvd_card_of_E8
    (S : Setting G) (hw : S.width = 28) (hE : LieModel S.Mbar .E7 0 2 1) :
    19 ∣ Nat.card G ∧ 127 ∣ Nat.card G := by
  have h := card_subgroup_dvd_card S.M
  rw [card_M_of_E8 S hw hE] at h
  exact ⟨dvd_trans (by norm_num) h, dvd_trans (by norm_num) h⟩

theorem not_thirteen_dvd_card_M_of_E7 (S : Setting G) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) : ¬ 13 ∣ Nat.card S.M := by
  rw [card_M_of_E7 S hw hO]
  norm_num

theorem not_twentythree_dvd_card_M_of_E8
    (S : Setting G) (hw : S.width = 28) (hE : LieModel S.Mbar .E7 0 2 1) :
    ¬ 23 ∣ Nat.card S.M := by
  rw [card_M_of_E8 S hw hE]
  norm_num

theorem isPrimitivePrimeDivisor_seventeen : Timmesfeld.IsPrimitivePrimeDivisor 17 8 :=
  ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩

theorem isPrimitivePrimeDivisor_127 : Timmesfeld.IsPrimitivePrimeDivisor 127 7 :=
  ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩

theorem isPrimitivePrimeDivisor_nineteen : Timmesfeld.IsPrimitivePrimeDivisor 19 18 :=
  ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩

theorem profile_facts {m N N₀ p k : ℕ} {Z : ℕ → Prop}
    (hP : Timmesfeld.Orders.Profile m N Z) (h2 : m.factorization 2 = N₀)
    (hp : Timmesfeld.IsPrimitivePrimeDivisor p k) (hk : 0 < k) (hpm : p ∣ m) : N = N₀ ∧ Z k := by
  refine ⟨?_, (hP.prim p k hp hk).mp hpm⟩
  obtain ⟨r, hr, rfl⟩ := hP.two
  rwa [factorization_two_pow_mul_odd hr] at h2

theorem le_of_mul_eq' {f T N : ℕ} (hN : f * T = N) (h0 : 0 < N) : T ≤ N :=
  Nat.le_of_dvd h0 ⟨f, by rw [← hN, mul_comm]⟩

theorem even_mul_mul_pred (f n : ℕ) : Even (f * (n * (n - 1))) :=
  (Nat.even_mul_pred_self n).mul_left f

theorem not_profile_A_17 {k f : ℕ} (hk : 2 ≤ k) (hN : f * (k * (k + 1) / 2) = 63)
    (hZ : Timmesfeld.Orders.zA k f 8) : False := by
  have hT : k * (k + 1) / 2 ≤ 63 := by
    have := le_of_mul_eq' hN (by norm_num)
    omega
  have hk11 : k < 11 := by
    by_contra hk11
    have : 11 * 12 ≤ k * (k + 1) := Nat.mul_le_mul (show 11 ≤ k by omega) (show 12 ≤ k + 1 by omega)
    omega
  revert hZ
  unfold Timmesfeld.Orders.zA
  interval_cases k
  · obtain rfl : f = 21 := by omega
    decide
  · exact fun _ => absurd hN (by omega)
  · exact fun _ => absurd hN (by omega)
  · exact fun _ => absurd hN (by omega)
  · obtain rfl : f = 3 := by omega
    decide
  all_goals exact fun _ => absurd hN (by omega)

theorem not_profile_BC_17 {n f : ℕ} (hn : 3 ≤ n) (hN : f * (n * n) = 63)
    (hZ : Timmesfeld.Orders.zBC n f 8) : False := by
  have hT : n * n ≤ 63 := by
    have := le_of_mul_eq' hN (by norm_num)
    omega
  have hn8 : n < 8 := by
    by_contra hn8
    have : 8 * 8 ≤ n * n := Nat.mul_le_mul (show 8 ≤ n by omega) (show 8 ≤ n by omega)
    omega
  revert hZ
  unfold Timmesfeld.Orders.zBC
  interval_cases n
  · obtain rfl : f = 7 := by omega
    decide
  all_goals exact fun _ => absurd hN (by omega)


theorem not_profile_D_63 {n f : ℕ} (hN : f * (n * (n - 1)) = 63) : False := by
  have h := even_mul_mul_pred f n
  rw [hN] at h
  exact absurd h (by decide)

theorem outcome_E7
    {H : Type} [Group H] (h : Timmesfeld.Outcome H)
    (h2 : (Nat.card H).factorization 2 = 63) (h17 : 17 ∣ Nat.card H) :
    LieModel H .E7 0 2 1 := by
  rcases h with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, t, ht, h⟩ | h | h | h
  ·
    exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hm : Nat.card H = ordA k (2 ^ f) := by
      simpa using (Timmesfeld.card_statedClassicalModel_two hc).1 rfl
    rw [hm] at h2 h17
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordA (by omega) hf) h2
      isPrimitivePrimeDivisor_seventeen (by norm_num) h17
    exact not_profile_A_17 (by omega) hN hZ
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl] at h2 h17
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordBC hf) h2
      isPrimitivePrimeDivisor_seventeen (by norm_num) h17
    exact not_profile_BC_17 hn hN hZ
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl] at h2
    obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordD (by omega) hf) h2
      isPrimitivePrimeDivisor_seventeen (by norm_num) (by
        rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl] at h17; exact h17)
    exact not_profile_D_63 hN
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.2 rfl] at h2
    obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordTwistedD (by omega) hf) h2
      isPrimitivePrimeDivisor_seventeen (by norm_num) (by
        rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.2 rfl] at h17; exact h17)
    exact not_profile_D_63 hN
  ·
    exfalso
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) h
    rw [Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hc.2] at h2 h17
    obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordG2 (by omega)) h2
      isPrimitivePrimeDivisor_seventeen (by norm_num) h17
    omega
  ·
    have hct : t ∈ chevalleyExceptionalTags := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel hct h
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have hm : Nat.card H = ordTrialityD4 (2 ^ f) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h17
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordTrialityD4 hf) h2
        isPrimitivePrimeDivisor_seventeen (by norm_num) h17
      omega
    · exfalso
      have hm : Nat.card H = ordF4 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h17
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordF4 hf) h2
        isPrimitivePrimeDivisor_seventeen (by norm_num) h17
      omega
    · exfalso
      have hm : Nat.card H = ordE6 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h17
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordE6 hf) h2
        isPrimitivePrimeDivisor_seventeen (by norm_num) h17
      omega
    · exfalso
      have hm : Nat.card H = ordTwistedE6 (2 ^ f) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h17
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordTwistedE6 hf) h2
        isPrimitivePrimeDivisor_seventeen (by norm_num) h17
      omega
    · have hm : Nat.card H = ordE7 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h17
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordE7 hf) h2
        isPrimitivePrimeDivisor_seventeen (by norm_num) h17
      obtain rfl : f = 1 := by omega
      exact h
    · exfalso
      have hm : Nat.card H = ordE8 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h17
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordE8 hf) h2
        isPrimitivePrimeDivisor_seventeen (by norm_num) h17
      omega
  ·
    exfalso
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [Nat.card_congr e.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSU
      Nat.prime_three le_rfl hK (by norm_num)] at h17
    revert h17
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h17
    revert h17
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    have hm : Nat.card H = 604800 := (Nat.card_congr e.toEquiv).trans Sporadic.J2.card_J2
    rw [hm] at h17
    revert h17
    decide

theorem chevalleyExceptionalModel_E7_of_outcome
    {H : Type} [Group H]
    (h : Timmesfeld.Outcome H) (h2 : (Nat.card H).factorization 2 = 63) (h17 : 17 ∣ Nat.card H) :
    ChevalleyExceptionalModel H .E7 2 1 :=
  Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) (outcome_E7 h h2 h17)

theorem not_profile_A_E8 {k f : ℕ} (hk : 2 ≤ k) (hN : f * (k * (k + 1) / 2) = 120)
    (h127 : Timmesfeld.Orders.zA k f 7) (h19 : Timmesfeld.Orders.zA k f 18) : False := by
  have hT : k * (k + 1) / 2 ≤ 120 := by
    have := le_of_mul_eq' hN (by norm_num)
    omega
  have hk16 : k < 16 := by
    by_contra hk16
    have : 16 * 17 ≤ k * (k + 1) :=
      Nat.mul_le_mul (show 16 ≤ k by omega) (show 17 ≤ k + 1 by omega)
    omega
  revert h127 h19
  unfold Timmesfeld.Orders.zA
  interval_cases k
  · obtain rfl : f = 40 := by omega
    decide
  · obtain rfl : f = 20 := by omega
    decide
  · obtain rfl : f = 12 := by omega
    decide
  · obtain rfl : f = 8 := by omega
    decide
  all_goals first
    | exact fun _ _ => absurd hN (by omega)
    | (obtain rfl : f = 1 := by omega
       decide)

theorem not_profile_BC_E8 {n f : ℕ} (hn : 3 ≤ n) (hN : f * (n * n) = 120) : False := by
  have hT : n * n ≤ 120 := le_of_mul_eq' hN (by norm_num)
  have hn11 : n < 11 := by
    by_contra hn11
    have : 11 * 11 ≤ n * n := Nat.mul_le_mul (show 11 ≤ n by omega) (show 11 ≤ n by omega)
    omega
  interval_cases n <;> omega

theorem not_profile_D_E8 {n f : ℕ} (hn : 4 ≤ n) (hN : f * (n * (n - 1)) = 120)
    (hZ : Timmesfeld.Orders.zD n f 7 ∨ Timmesfeld.Orders.z2D n f 7) : False := by
  have hT : n * (n - 1) ≤ 120 := le_of_mul_eq' hN (by norm_num)
  have hn12 : n < 12 := by
    by_contra hn12
    have : 12 * 11 ≤ n * (n - 1) :=
      Nat.mul_le_mul (show 12 ≤ n by omega) (show 11 ≤ n - 1 by omega)
    omega
  revert hZ
  unfold Timmesfeld.Orders.zD Timmesfeld.Orders.z2D
  interval_cases n
  · obtain rfl : f = 10 := by omega
    decide
  · obtain rfl : f = 6 := by omega
    decide
  · obtain rfl : f = 4 := by omega
    decide
  all_goals exact fun _ => absurd hN (by omega)

theorem outcome_E8
    {H : Type} [Group H] (h : Timmesfeld.Outcome H)
    (h2 : (Nat.card H).factorization 2 = 120) (h19 : 19 ∣ Nat.card H)
    (h127 : 127 ∣ Nat.card H) : LieModel H .E8 0 2 1 := by
  rcases h with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, t, ht, h⟩ | h | h | h
  ·
    exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hm : Nat.card H = ordA k (2 ^ f) := by
      simpa using (Timmesfeld.card_statedClassicalModel_two hc).1 rfl
    rw [hm] at h2 h19 h127
    obtain ⟨hN, hZ7⟩ := profile_facts (Timmesfeld.Orders.profile_ordA (by omega) hf) h2
      isPrimitivePrimeDivisor_127 (by norm_num) h127
    obtain ⟨-, hZ18⟩ := profile_facts (Timmesfeld.Orders.profile_ordA (by omega) hf) h2
      isPrimitivePrimeDivisor_nineteen (by norm_num) h19
    exact not_profile_A_E8 (by omega) hN hZ7 hZ18
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl] at h2
    obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordBC hf) h2
      isPrimitivePrimeDivisor_127 (by norm_num) (by
        rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl] at h127; exact h127)
    exact not_profile_BC_E8 hn hN
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl] at h2 h127
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordD (by omega) hf) h2
      isPrimitivePrimeDivisor_127 (by norm_num) h127
    exact not_profile_D_E8 hn hN (.inl hZ)
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.2 rfl] at h2 h127
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordTwistedD (by omega) hf) h2
      isPrimitivePrimeDivisor_127 (by norm_num) h127
    exact not_profile_D_E8 hn hN (.inr hZ)
  ·
    exfalso
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) h
    rw [Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hc.2] at h2 h127
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordG2 (by omega)) h2
      isPrimitivePrimeDivisor_127 (by norm_num) h127
    obtain rfl : f = 20 := by omega
    revert hZ
    unfold Timmesfeld.Orders.zG2 Timmesfeld.Orders.zList
    decide
  ·
    have hct : t ∈ chevalleyExceptionalTags := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel hct h
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have hm : Nat.card H = ordTrialityD4 (2 ^ f) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h127
      obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordTrialityD4 hf) h2
        isPrimitivePrimeDivisor_127 (by norm_num) h127
      obtain rfl : f = 10 := by omega
      revert hZ
      unfold Timmesfeld.Orders.zD4
      decide
    · exfalso
      have hm : Nat.card H = ordF4 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h127
      obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordF4 hf) h2
        isPrimitivePrimeDivisor_127 (by norm_num) h127
      obtain rfl : f = 5 := by omega
      revert hZ
      unfold Timmesfeld.Orders.zF4 Timmesfeld.Orders.zList
      decide
    · exfalso
      have hm : Nat.card H = ordE6 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h127
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordE6 hf) h2
        isPrimitivePrimeDivisor_127 (by norm_num) h127
      omega
    · exfalso
      have hm : Nat.card H = ordTwistedE6 (2 ^ f) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h127
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordTwistedE6 hf) h2
        isPrimitivePrimeDivisor_127 (by norm_num) h127
      omega
    · exfalso
      have hm : Nat.card H = ordE7 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h127
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordE7 hf) h2
        isPrimitivePrimeDivisor_127 (by norm_num) h127
      omega
    · have hm : Nat.card H = ordE8 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h127
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordE8 hf) h2
        isPrimitivePrimeDivisor_127 (by norm_num) h127
      obtain rfl : f = 1 := by omega
      exact h
  ·
    exfalso
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [Nat.card_congr e.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSU
      Nat.prime_three le_rfl hK (by norm_num)] at h127
    revert h127
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h127
    revert h127
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    have hm : Nat.card H = 604800 := (Nat.card_congr e.toEquiv).trans Sporadic.J2.card_J2
    rw [hm] at h127
    revert h127
    decide

theorem chevalleyExceptionalModel_E8_of_outcome
    {H : Type} [Group H]
    (h : Timmesfeld.Outcome H) (h2 : (Nat.card H).factorization 2 = 120)
    (h19 : 19 ∣ Nat.card H) (h127 : 127 ∣ Nat.card H) :
    ChevalleyExceptionalModel H .E8 2 1 :=
  Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) (outcome_E8 h h2 h19 h127)

end CFSG.GF2Type.SmithTypeE
