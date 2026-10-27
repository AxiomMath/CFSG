module

public import CFSG.LargeExtraspecial.OutSix
public import CFSG.LargeExtraspecial.GLRElimSylow
import all CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.J2
public import CFSG.Timmesfeld.Final.Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.Blueprint

theorem card_timmesfeldPSU_six : Nat.card (timmesfeldPSU 6) = 9196830720 := by
  rw [Nat.card_congr ((timmesfeldPSUEquiv (n := 6) (by norm_num)).trans
    (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv unitaryFieldData_two_one
      (n := 6) (by norm_num))).toEquiv,
    Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl
      (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num) (by norm_num)]
  decide

variable {G : Type} [Group G] [Finite G]

theorem card_M_eq_card_Q_mul (S : Setting G) :
    Nat.card S.M = Nat.card S.Q * Nat.card S.Mbar := by
  rw [card_eq_card_quotient_mul_card_subgroup S.ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange S.ρ).toEquiv, S.ker_ρ, mul_comm]
  rfl

theorem card_M_eq_of_U6 (S : Setting G) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    Nat.card S.M = Nat.card S.Q * 9196830720 * (Mbar0 S).index := by
  obtain ⟨e⟩ := hU
  rw [card_M_eq_card_Q_mul, ← (Mbar0 S).card_mul_index, Nat.card_congr e.toEquiv,
    card_timmesfeldPSU_six, mul_assoc]

theorem card_M_of_U6 (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    (Mbar0 S).index ∣ 6 ∧ Nat.card S.M = 2 ^ 21 * 9196830720 * (Mbar0 S).index := by
  have := Bridge.finite_Mbar S
  have hcent : centralizer (Mbar0 S : Set S.Mbar) ≤ Mbar0 S :=
    CFSG.Adapters.generalized_fitting_self_centralizing S.Mbar
  refine ⟨outU62Input S.Mbar (Mbar0 S) (timmesfeldFStar_normal S.Mbar) hU hcent, ?_⟩
  rw [card_M_eq_of_U6 S hU, S.card_Q_eq, hw]

theorem exists_sylow_le_M (S : Setting G) : ∃ P : Sylow 2 G, (P : Subgroup G) ≤ S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, -, hT⟩ := GLR.exists_isSylowIn_le (bot_le : (⊥ : Subgroup G) ≤ S.M)
    IsPGroup.of_bot
  obtain ⟨-, hTp, hTi⟩ := GLR.Config.sylowIn_top hT
  rw [relIndex_top_right] at hTi
  exact ⟨hTp.toSylow hTi, by rw [IsPGroup.toSylow_coe]; exact hT.1⟩

theorem not_two_dvd_index_M (S : Setting G) : ¬ 2 ∣ S.M.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_le_M S
  intro h
  exact P.not_dvd_index ((relIndex_mul_index hP) ▸ dvd_mul_of_dvd_right h _)

theorem factorization_two_pow_mul_odd {N r : ℕ} (hr : Odd r) : (2 ^ N * r).factorization 2 = N := by
  have hr2 : ¬ 2 ∣ r := by rintro ⟨k, rfl⟩; exact (Nat.not_even_iff_odd.mpr hr) (even_two_mul k)
  rw [Nat.factorization_mul (by positivity) hr.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hr2, add_zero]

theorem eq_of_dvd_six {k : ℕ} (hk : k ∣ 6) : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6 :=
  (by decide : ∀ k, k ≤ 6 → k ∣ 6 → k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6) k
    (Nat.le_of_dvd (by norm_num) hk) hk

theorem factorization_card_of_U6 (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    (Nat.card G).factorization 2 = 36 ∨ (Nat.card G).factorization 2 = 37 := by
  obtain ⟨hk, hM⟩ := card_M_of_U6 S hw hU
  have hodd : Odd S.M.index := Nat.odd_iff.mpr (by have := not_two_dvd_index_M S; omega)
  rw [← S.M.card_mul_index, hM]
  rcases eq_of_dvd_six hk with hk | hk | hk | hk <;> rw [hk]
  · left
    rw [show 2 ^ 21 * 9196830720 * 1 * S.M.index = 2 ^ 36 * (280665 * S.M.index) by ring]
    exact factorization_two_pow_mul_odd ((by decide : Odd 280665).mul hodd)
  · right
    rw [show 2 ^ 21 * 9196830720 * 2 * S.M.index = 2 ^ 37 * (280665 * S.M.index) by ring]
    exact factorization_two_pow_mul_odd ((by decide : Odd 280665).mul hodd)
  · left
    rw [show 2 ^ 21 * 9196830720 * 3 * S.M.index = 2 ^ 36 * (841995 * S.M.index) by ring]
    exact factorization_two_pow_mul_odd ((by decide : Odd 841995).mul hodd)
  · right
    rw [show 2 ^ 21 * 9196830720 * 6 * S.M.index = 2 ^ 37 * (841995 * S.M.index) by ring]
    exact factorization_two_pow_mul_odd ((by decide : Odd 841995).mul hodd)

theorem eleven_dvd_card_of_U6 (S : Setting G) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    11 ∣ Nat.card G := by
  refine dvd_trans ?_ (card_subgroup_dvd_card S.M)
  rw [card_M_eq_of_U6 S hU]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by norm_num) _) _

theorem not_seventeen_dvd_card_M (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) : ¬ 17 ∣ Nat.card S.M := by
  obtain ⟨hk, hM⟩ := card_M_of_U6 S hw hU
  rw [hM]
  rcases eq_of_dvd_six hk with hk | hk | hk | hk <;> rw [hk] <;> norm_num

theorem isPrimitivePrimeDivisor_eleven : Timmesfeld.IsPrimitivePrimeDivisor 11 10 :=
  ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩

theorem profile_facts {m N : ℕ} {Z : ℕ → Prop} (hP : Timmesfeld.Orders.Profile m N Z)
    (h2 : m.factorization 2 = 36 ∨ m.factorization 2 = 37) (h11 : 11 ∣ m) :
    (N = 36 ∨ N = 37) ∧ Z 10 := by
  refine ⟨?_, (hP.prim 11 10 isPrimitivePrimeDivisor_eleven (by norm_num)).mp h11⟩
  obtain ⟨r, hr, rfl⟩ := hP.two
  rwa [factorization_two_pow_mul_odd hr] at h2

theorem le_of_mul_eq {a b c : ℕ} (h : a * b = c) (hc : 0 < c) : a ≤ c ∧ b ≤ c :=
  ⟨Nat.le_of_dvd hc (Dvd.intro _ h), Nat.le_of_dvd hc (Dvd.intro_left _ h)⟩

theorem not_profile_A {k f : ℕ} (hk : 2 ≤ k) (hf : 1 ≤ f)
    (hN : f * (k * (k + 1) / 2) = 36 ∨ f * (k * (k + 1) / 2) = 37)
    (hZ : Timmesfeld.Orders.zA k f 10) : False := by
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
  decide

theorem eq_of_profile_BC {n f : ℕ} (hn : 3 ≤ n) (hN : f * (n * n) = 36 ∨ f * (n * n) = 37)
    (hZ : Timmesfeld.Orders.zBC n f 10) : n = 6 ∧ f = 1 := by
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

theorem not_profile_D {n f : ℕ} (hn : 4 ≤ n)
    (hN : f * (n * (n - 1)) = 36 ∨ f * (n * (n - 1)) = 37)
    (hZ : Timmesfeld.Orders.zD n f 10 ∨ Timmesfeld.Orders.z2D n f 10) : False := by
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

theorem outcome_PSp12_or_twistedE6
    {H : Type} [Group H] (h : Timmesfeld.Outcome H)
    (h2 : (Nat.card H).factorization 2 = 36 ∨ (Nat.card H).factorization 2 = 37)
    (h11 : 11 ∣ Nat.card H) :
    LieModel H .PSp 6 2 1 ∨ LieModel H .twistedE6 0 2 1 := by
  rcases h with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, t, ht, h⟩ | h | h | h
  ·
    exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hm : Nat.card H = ordA k (2 ^ f) := by
      simpa using (Timmesfeld.card_statedClassicalModel_two hc).1 rfl
    rw [hm] at h2 h11
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordA (by omega) hf) h2 h11
    exact not_profile_A (by omega) hf hN hZ
  ·
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl] at h2 h11
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordBC hf) h2 h11
    obtain ⟨rfl, rfl⟩ := eq_of_profile_BC hn hN hZ
    exact .inl h
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl] at h2 h11
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordD (by omega) hf) h2 h11
    exact not_profile_D hn hN (.inl hZ)
  ·
    exfalso
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.2 rfl] at h2 h11
    obtain ⟨hN, hZ⟩ :=
      profile_facts (Timmesfeld.Orders.profile_ordTwistedD (by omega) hf) h2 h11
    exact not_profile_D hn hN (.inr hZ)
  ·
    exfalso
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) h
    rw [Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hc.2] at h2 h11
    obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordG2 (by omega)) h2 h11
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
      rw [hm] at h2 h11
      obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordTrialityD4 hf) h2 h11
      obtain rfl : f = 3 := by omega
      revert hZ
      unfold Timmesfeld.Orders.zD4
      decide
    · exfalso
      have hm : Nat.card H = ordF4 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h11
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordF4 hf) h2 h11
      omega
    · exfalso
      have hm : Nat.card H = ordE6 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h11
      obtain ⟨hN, hZ⟩ := profile_facts (Timmesfeld.Orders.profile_ordE6 hf) h2 h11
      obtain rfl : f = 1 := by omega
      revert hZ
      unfold Timmesfeld.Orders.zE6 Timmesfeld.Orders.zList
      decide
    · have hm : Nat.card H = ordTwistedE6 (2 ^ f) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h11
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordTwistedE6 hf) h2 h11
      obtain rfl : f = 1 := by omega
      exact .inr h
    · exfalso
      have hm : Nat.card H = ordE7 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h11
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordE7 hf) h2 h11
      omega
    · exfalso
      have hm : Nat.card H = ordE8 (2 ^ f) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      rw [hm] at h2 h11
      obtain ⟨hN, -⟩ := profile_facts (Timmesfeld.Orders.profile_ordE8 hf) h2 h11
      omega
  ·
    exfalso
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [Nat.card_congr e.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSU
      Nat.prime_three le_rfl hK (by norm_num)] at h11
    revert h11
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h11
    revert h11
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    have hm : Nat.card H = 604800 := (Nat.card_congr e.toEquiv).trans Sporadic.J2.card_J2
    rw [hm] at h11
    revert h11
    decide

end CFSG.LargeExtraspecial.S14
