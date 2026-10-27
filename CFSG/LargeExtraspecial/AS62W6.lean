module

public import CFSG.LargeExtraspecial.AS62Conf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions

namespace AS62

theorem pCore_ne_bot_of_card_eq_three_mul {K : Type*} [Group K] [Finite K] {n : ℕ}
    (hn : Nat.card K = 3 * 2 ^ n) (hn2 : 2 ≤ n) : CFSG.pCore 2 K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := n)
    (by rw [hn]; exact Dvd.intro_left 3 rfl)
  have hpos : 0 < 2 ^ n := by positivity
  have hPi : P.index = 3 := by
    have h := P.card_mul_index
    rw [hP, hn] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (h.trans (mul_comm 3 (2 ^ n)))
  have hcore : P.normalCore.index ∣ Nat.factorial 3 := hPi ▸ P.index_normalCore_dvd_factorial_index
  have hp : IsPGroup 2 P.normalCore := (IsPGroup.of_card hP).to_le P.normalCore_le
  intro h0
  have hle : P.normalCore ≤ CFSG.pCore 2 K := le_sSup ⟨inferInstance, hp⟩
  rw [h0, le_bot_iff] at hle
  rw [hle, index_bot, hn] at hcore
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have h6 := Nat.le_of_dvd (by decide) hcore
  have : Nat.factorial 3 = 6 := rfl
  omega

variable {G : Type} [Group G] [Finite G]

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem isPlusType (hc : ConfHyp S H) : CFSG.GroupTheory.WeirSylow.IsPlusType S.q := by
  obtain ⟨p, hp, hpz⟩ :=
    Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  obtain ⟨hA, -, -⟩ := hc.fiveOne hp hpz
  exact ⟨commSpace (S.rhoL (hc.mem_M_of_mem hp)), by rw [hA.2.2.2.1, hc.finrank_Qt],
    hA.2.2.2.2⟩

theorem card_O (hc : ConfHyp S H) : Nat.card S.O = 72 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hdim : finrank (ZMod 2) S.Qt = 2 * (1 + 1) := by rw [hc.finrank_Qt]
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
    (ε := 1) (Or.inl ⟨rfl, hc.isPlusType⟩)
  have h2 : (Nat.card (ZMod 2) : ℤ) = 2 := by rw [Nat.card_zmod]; rfl
  rw [h2] at h
  have h' : (Nat.card S.O : ℤ) = 72 := by rw [h]; decide
  exact_mod_cast h'

theorem card_map_ρ (hc : ConfHyp S H) : Nat.card ((H.subgroupOf S.M).map S.ρ) = 6 := by
  have hB : Nat.card (H.subgroupOf S.M) = 192 := by
    rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,
      hc.card_inf_M]
  have hQB : S.Q ≤ H.subgroupOf S.M := fun q hq => by
    rw [mem_subgroupOf]
    exact hc.QG_le ⟨q, hq, rfl⟩
  have hker : H.subgroupOf S.M ⊓ S.ρ.ker = S.Q := by
    rw [S.ker_ρ]
    exact inf_eq_right.mpr hQB
  have h1 := Setting.card_eq_relIndex_mul (H.subgroupOf S.M) S.ρ.ker
  rw [Subgroup.relIndex_ker, hker, hB, ← S.card_QG_eq_card_Q, hc.card_QG] at h1
  omega

theorem ρ_conj_eq (hc : ConfHyp S H) {t : G} (ht : t ∈ S.zConj H) (htz : t ≠ S.z) {m : S.M}
    (hm : (m : G) ∈ H) :
    S.ρ m * S.ρ ⟨t, hc.mem_M_of_mem ht⟩ * (S.ρ m)⁻¹ = S.ρ ⟨t, hc.mem_M_of_mem ht⟩ := by
  set tM : S.M := ⟨t, hc.mem_M_of_mem ht⟩
  have hmt : (m : G) * t * (m : G)⁻¹ ∈ S.zConj H := conj_mem_conjIn_of_mem hm ht
  have hmtz : (m : G) * t * (m : G)⁻¹ ≠ S.z := by
    intro h
    apply htz
    calc t = (m : G)⁻¹ * ((m : G) * t * (m : G)⁻¹) * m := by group
      _ = S.z := by rw [h, mul_assoc, ← S.z_comm m.2]; group
  have h1 : S.ρ (m * tM * m⁻¹ * tM) = 1 :=
    (S.ρ_eq_one_iff _).mpr (hc.mul_mem_QG hmt hmtz ht htz)
  have htt : S.ρ tM * S.ρ tM = 1 := by
    rw [← map_mul, show tM * tM = 1 from Subtype.ext (zConj_mul_self S ht), map_one]
  rw [map_mul, map_mul, map_mul, map_inv] at h1
  calc S.ρ m * S.ρ tM * (S.ρ m)⁻¹ = S.ρ m * S.ρ tM * (S.ρ m)⁻¹ * S.ρ tM * S.ρ tM := by
        rw [mul_assoc _ (S.ρ tM) (S.ρ tM), htt, mul_one]
    _ = S.ρ tM := by rw [h1, one_mul]

theorem card_Mbar_ne_six (hc : ConfHyp S H) : Nat.card S.Mbar ≠ 6 := by
  intro h6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htz⟩ :=
    Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  have htM := hc.mem_M_of_mem ht
  have hle : (H.subgroupOf S.M).map S.ρ ≤ S.Mbar := map_le_range S.ρ _
  have heq : (H.subgroupOf S.M).map S.ρ = S.Mbar :=
    eq_of_le_of_card_ge hle (by rw [h6, hc.card_map_ρ])
  set τ : S.Mbar := ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ with hτ
  have hτ1 : τ ≠ 1 := by
    intro h
    exact hc.not_mem_QG ht htz ((S.ρ_eq_one_iff ⟨t, htM⟩).mp (congrArg Subtype.val h))
  have hτ2 : τ ^ 2 = 1 := by
    apply Subtype.ext
    change S.ρ ⟨t, htM⟩ ^ 2 = 1
    rw [← map_pow, show (⟨t, htM⟩ : S.M) ^ 2 = 1 from
      Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_two]; exact zConj_mul_self S ht), map_one]
  have hcomm : ∀ g : S.Mbar, g * τ * g⁻¹ = τ := by
    intro g
    have hg : (g : S.O) ∈ (H.subgroupOf S.M).map S.ρ := by
      rw [heq]
      exact g.2
    obtain ⟨b, hb, hbg⟩ := hg
    apply Subtype.ext
    change (g : S.O) * S.ρ ⟨t, htM⟩ * (g : S.O)⁻¹ = S.ρ ⟨t, htM⟩
    rw [← hbg]
    exact hc.ρ_conj_eq ht htz (mem_subgroupOf.mp hb)
  have hX : (zpowers τ).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [← conj_zpow, hcomm g]
    exact zpow_mem_zpowers τ k⟩
  have hXp : IsPGroup 2 (zpowers τ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hτ2 hτ1, pow_one])
  have hle2 : zpowers τ ≤ CFSG.pCore 2 S.Mbar := le_sSup ⟨hX, hXp⟩
  rw [S.pCore_Mbar_eq_bot, le_bot_iff, zpowers_eq_bot] at hle2
  exact hτ1 hle2

theorem card_Mbar_mem (hc : ConfHyp S H) : Nat.card S.Mbar ∈ ({18, 36, 72} : Set ℕ) := by
  have h6 : 6 ∣ Nat.card S.Mbar := by
    rw [← hc.card_map_ρ]
    exact card_dvd_of_le (map_le_range S.ρ _)
  have h72 : Nat.card S.Mbar ∣ 72 := by
    rw [← hc.card_O]
    exact card_subgroup_dvd_card S.Mbar
  have hne12 : Nat.card S.Mbar ≠ 12 := fun h =>
    pCore_ne_bot_of_card_eq_three_mul (n := 2) (by rw [h]; norm_num) le_rfl S.pCore_Mbar_eq_bot
  have hne24 : Nat.card S.Mbar ≠ 24 := fun h =>
    pCore_ne_bot_of_card_eq_three_mul (n := 3) (by rw [h]; norm_num) (by norm_num)
      S.pCore_Mbar_eq_bot
  have hne6 := hc.card_Mbar_ne_six
  have hle72 : Nat.card S.Mbar ≤ 72 := Nat.le_of_dvd (by norm_num) h72
  obtain ⟨k, hk⟩ := h6
  rw [hk] at h72 hne6 hne12 hne24 hle72 ⊢
  have hk12 : k ≤ 12 := by omega
  interval_cases k <;> first | omega | (norm_num at h72; done) | simp

end ConfHyp

end AS62

end CFSG.LargeExtraspecial
