module

public import CFSG.LargeExtraspecial.S14C12TOrd
import all CFSG.Timmesfeld.Orders.Distinct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem card_PSL_six_two : Nat.card (PSL(6, ZMod 2)) = 20158709760 := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hZ : Nat.card (LinearFlag.scalars 6 (ZMod 2)) = 1 := by
    have h := LinearFlag.card_scalars_dvd (K := ZMod 2) (n := 6) (by norm_num)
    rw [hK] at h
    exact Nat.dvd_one.mp h
  rw [Nat.card_congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL 6 (ZMod 2)).toEquiv,
    LinearFlag.card_projectiveSL, hZ, Nat.div_one, LinearFlag.card_SL_eq (by norm_num), hK]
  decide

variable {G : Type} [Group G] [Finite G]

theorem card_M_eq_of_L6 (S : Setting G) (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) :
    Nat.card S.M = Nat.card S.Q * 20158709760 * (Mbar0 S).index := by
  obtain ⟨e⟩ := hL
  rw [card_M_eq_card_Q_mul, ← (Mbar0 S).card_mul_index, Nat.card_congr e.toEquiv,
    card_PSL_six_two, mul_assoc]

theorem card_M_of_L6 (S : Setting G) (hw : S.width = 10)
    (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) :
    (Mbar0 S).index ∣ 2 ∧ Nat.card S.M = 2 ^ 21 * 20158709760 * (Mbar0 S).index := by
  have := Bridge.finite_Mbar S
  have : (Mbar0 S).Normal := timmesfeldFStar_normal S.Mbar
  have hcent : centralizer (Mbar0 S : Set S.Mbar) ≤ Mbar0 S :=
    CFSG.Adapters.generalized_fitting_self_centralizing S.Mbar
  obtain ⟨e⟩ := hL
  refine ⟨index_dvd_two_of_mulEquiv_psl (by norm_num) (Mbar0 S) e hcent, ?_⟩
  rw [card_M_eq_of_L6 S ⟨e⟩, S.card_Q_eq, hw]

theorem factorization_card_of_L6 (S : Setting G) (hw : S.width = 10)
    (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) :
    (Nat.card G).factorization 2 = 36 ∨ (Nat.card G).factorization 2 = 37 := by
  obtain ⟨hk, hM⟩ := card_M_of_L6 S hw hL
  have hodd : Odd S.M.index := Nat.odd_iff.mpr (by have := not_two_dvd_index_M S; omega)
  rw [← S.M.card_mul_index, hM]
  rcases (Nat.dvd_prime Nat.prime_two).mp hk with hk | hk <;> rw [hk]
  · left
    rw [show 2 ^ 21 * 20158709760 * 1 * S.M.index = 2 ^ 36 * (615195 * S.M.index) by ring]
    exact factorization_two_pow_mul_odd ((by decide : Odd 615195).mul hodd)
  · right
    rw [show 2 ^ 21 * 20158709760 * 2 * S.M.index = 2 ^ 37 * (615195 * S.M.index) by ring]
    exact factorization_two_pow_mul_odd ((by decide : Odd 615195).mul hodd)

theorem thirtyOne_dvd_card_of_L6 (S : Setting G) (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) :
    31 ∣ Nat.card G := by
  refine dvd_trans ?_ (card_subgroup_dvd_card S.M)
  rw [card_M_eq_of_L6 S hL]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by norm_num) _) _

theorem not_seventeen_dvd_card_M_of_L6 (S : Setting G) (hw : S.width = 10)
    (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) : ¬ 17 ∣ Nat.card S.M := by
  obtain ⟨hk, hM⟩ := card_M_of_L6 S hw hL
  rw [hM]
  rcases (Nat.dvd_prime Nat.prime_two).mp hk with hk | hk <;> rw [hk] <;> norm_num

theorem not_dvd_card_M_of_L6_127 (S : Setting G) (hw : S.width = 10)
    (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) : ¬ 127 ∣ Nat.card S.M := by
  obtain ⟨hk, hM⟩ := card_M_of_L6 S hw hL
  rw [hM]
  rcases (Nat.dvd_prime Nat.prime_two).mp hk with hk | hk <;> rw [hk] <;> norm_num

theorem isPrimitivePrimeDivisor_thirtyOne : Timmesfeld.IsPrimitivePrimeDivisor 31 5 :=
  ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩

theorem profile_facts_thirtyOne {m N : ℕ} {Z : ℕ → Prop}
    (hP : Timmesfeld.Orders.Profile m N Z)
    (h2 : m.factorization 2 = 36 ∨ m.factorization 2 = 37) (h31 : 31 ∣ m) :
    (N = 36 ∨ N = 37) ∧ Z 5 := by
  refine ⟨?_, (hP.prim 31 5 isPrimitivePrimeDivisor_thirtyOne (by norm_num)).mp h31⟩
  obtain ⟨r, hr, rfl⟩ := hP.two
  rwa [factorization_two_pow_mul_odd hr] at h2

theorem eq_of_profile_A_31 {k f : ℕ} (hk : 2 ≤ k)
    (hN : f * (k * (k + 1) / 2) = 36 ∨ f * (k * (k + 1) / 2) = 37)
    (hZ : Timmesfeld.Orders.zA k f 5) : k = 8 ∧ f = 1 := by
  have hT : k * (k + 1) / 2 ≤ 37 := by
    rcases hN with hN | hN <;> have := (le_of_mul_eq hN (by norm_num)).2 <;> omega
  have hk9 : k < 9 := by
    by_contra hk9
    have : 9 * 10 ≤ k * (k + 1) := Nat.mul_le_mul (show 9 ≤ k by omega) (show 10 ≤ k + 1 by omega)
    omega
  revert hZ
  unfold Timmesfeld.Orders.zA
  interval_cases k
  · obtain rfl : f = 12 := by omega
    decide
  · obtain rfl : f = 6 := by omega
    decide
  all_goals try exact fun _ => absurd hN (by omega)
  obtain rfl : f = 1 := by omega
  exact fun _ => ⟨rfl, rfl⟩

theorem eq_of_profile_BC_31 {n f : ℕ} (hn : 3 ≤ n) (hN : f * (n * n) = 36 ∨ f * (n * n) = 37)
    (hZ : Timmesfeld.Orders.zBC n f 5) : n = 6 ∧ f = 1 := by
  have hT : n * n ≤ 37 := by
    rcases hN with hN | hN <;> have := (le_of_mul_eq hN (by norm_num)).2 <;> omega
  have hn7 : n < 7 := by
    by_contra hn7
    have : 7 * 7 ≤ n * n := Nat.mul_le_mul (show 7 ≤ n by omega) (show 7 ≤ n by omega)
    omega
  revert hZ
  unfold Timmesfeld.Orders.zBC
  interval_cases n
  · obtain rfl : f = 4 := by omega
    decide
  · exact fun _ => absurd hN (by omega)
  · exact fun _ => absurd hN (by omega)
  · obtain rfl : f = 1 := by omega
    exact fun _ => ⟨rfl, rfl⟩

theorem not_profile_D_31 {n f : ℕ} (hn : 4 ≤ n)
    (hN : f * (n * (n - 1)) = 36 ∨ f * (n * (n - 1)) = 37)
    (hZ : Timmesfeld.Orders.zD n f 5 ∨ Timmesfeld.Orders.z2D n f 5) : False := by
  have hT : n * (n - 1) ≤ 37 := by
    rcases hN with hN | hN <;> have := (le_of_mul_eq hN (by norm_num)).2 <;> omega
  have hn7 : n < 7 := by
    by_contra hn7
    have : 7 * 6 ≤ n * (n - 1) := Nat.mul_le_mul (show 7 ≤ n by omega) (show 6 ≤ n - 1 by omega)
    omega
  revert hZ
  unfold Timmesfeld.Orders.zD Timmesfeld.Orders.z2D
  interval_cases n
  · obtain rfl : f = 3 := by omega
    decide
  all_goals exact fun _ => absurd hN (by omega)

theorem outcome_PSL9_or_PSp12_or_E6
    {H : Type} [Group H] (h : Timmesfeld.Outcome H)
    (h2 : (Nat.card H).factorization 2 = 36 ∨ (Nat.card H).factorization 2 = 37)
    (h31 : 31 ∣ Nat.card H) :
    LieModel H .PSL 9 2 1 ∨ LieModel H .PSp 6 2 1 ∨ LieModel H .E6 0 2 1 := by
  rcases h with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, t, ht, h⟩ | h | h | h
  ·
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hm : Nat.card H = ordA k (2 ^ f) := by
      simpa using (Timmesfeld.card_statedClassicalModel_two hc).1 rfl
    rw [hm] at h2 h31
    obtain ⟨hN, hZ⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordA (by omega) hf) h2
      h31
    obtain ⟨rfl, rfl⟩ := eq_of_profile_A_31 (by omega) hN hZ
    exact .inl h
  ·
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl] at h2 h31
    obtain ⟨hN, hZ⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordBC hf) h2 h31
    obtain ⟨rfl, rfl⟩ := eq_of_profile_BC_31 hn hN hZ
    exact .inr (.inl h)
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl] at h2 h31
    obtain ⟨hN, hZ⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordD (by omega) hf) h2
      h31
    exact not_profile_D_31 hn hN (.inl hZ)
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.2 rfl] at h2 h31
    obtain ⟨hN, hZ⟩ :=
      profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordTwistedD (by omega) hf) h2 h31
    exact not_profile_D_31 hn hN (.inr hZ)
  ·
    exfalso
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) h
    rw [Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hc.2] at h2 h31
    obtain ⟨hN, hZ⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordG2 (by omega)) h2 h31
    obtain rfl : f = 6 := by omega
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
      rw [hm] at h2 h31
      obtain ⟨hN, hZ⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordTrialityD4 hf) h2
        h31
      obtain rfl : f = 3 := by omega
      revert hZ
      unfold Timmesfeld.Orders.zD4
      decide
    · exfalso
      have hm : Nat.card H = ordF4 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h31
      obtain ⟨hN, -⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordF4 hf) h2 h31
      omega
    · have hm : Nat.card H = ordE6 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h31
      obtain ⟨hN, -⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordE6 hf) h2 h31
      obtain rfl : f = 1 := by omega
      exact .inr (.inr h)
    · exfalso
      have hm : Nat.card H = ordTwistedE6 (2 ^ f) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h31
      obtain ⟨hN, hZ⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordTwistedE6 hf) h2
        h31
      obtain rfl : f = 1 := by omega
      revert hZ
      unfold Timmesfeld.Orders.z2E6
      decide
    · exfalso
      have hm : Nat.card H = ordE7 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h31
      obtain ⟨hN, -⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordE7 hf) h2 h31
      omega
    · exfalso
      have hm : Nat.card H = ordE8 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h31
      obtain ⟨hN, -⟩ := profile_facts_thirtyOne (Timmesfeld.Orders.profile_ordE8 hf) h2 h31
      omega
  ·
    exfalso
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [Nat.card_congr e.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSU
      Nat.prime_three le_rfl hK (by norm_num)] at h31
    revert h31
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h31
    revert h31
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    have hm : Nat.card H = 604800 := (Nat.card_congr e.toEquiv).trans Sporadic.J2.card_J2
    rw [hm] at h31
    revert h31
    decide

end CFSG.GF2Type.SmithTypeE
