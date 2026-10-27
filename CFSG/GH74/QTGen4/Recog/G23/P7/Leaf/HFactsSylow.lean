module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HFactsAux

open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_conj_of_card_nine {H P S : Subgroup G} (hH : Nat.card H = 576) (hPH : P ≤ H)
    (hSH : S ≤ H) (hP : Nat.card P = 9) (hS : Nat.card S = 9) :
    ∃ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ S := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ T : Subgroup G, T ≤ H → Nat.card T = 9 →
      ∃ Tsyl : Sylow 3 H, (Tsyl : Subgroup H) = T.subgroupOf H := by
    intro T hTH hT
    have hT' : Nat.card (T.subgroupOf H) = 9 := by
      rw [← hT]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
    have hT3 : IsPGroup 3 (T.subgroupOf H) := IsPGroup.of_card (n := 2) (by rw [hT']; norm_num)
    have hidx : ¬ 3 ∣ (T.subgroupOf H).index := by
      have h := (T.subgroupOf H).index_mul_card
      rw [hT', hH] at h
      have : (T.subgroupOf H).index = 64 := by omega
      rw [this]; norm_num
    exact ⟨hT3.toSylow hidx, rfl⟩
  obtain ⟨Psyl, hPsyl⟩ := key P hPH hP
  obtain ⟨Ssyl, hSsyl⟩ := key S hSH hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Psyl Ssyl
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hx' : (⟨x, hPH hx⟩ : H) ∈ (Psyl : Subgroup H) := by
    rw [hPsyl]; exact hx
  have hmem : MulAut.conj g • (⟨x, hPH hx⟩ : H) ∈ MulAut.conj g • (Psyl : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hx'
  have h2 : (↑(g • Psyl) : Subgroup H) = MulAut.conj g • (Psyl : Subgroup H) :=
    Sylow.coe_subgroup_smul
  rw [← h2, hg, hSsyl] at hmem
  have : MulAut.conj g • (⟨x, hPH hx⟩ : H) = g * ⟨x, hPH hx⟩ * g⁻¹ := rfl
  rw [this] at hmem
  exact hmem

theorem exists_conj_into_of_pow_three {H P : Subgroup G} (hH : Nat.card H = 576) (hPH : P ≤ H)
    (hP : Nat.card P = 9) {x : G} (hx : x ∈ H) (hx3 : x ^ 3 = 1) :
    ∃ h ∈ H, h * x * h⁻¹ ∈ P := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' : Nat.card (P.subgroupOf H) = 9 := by
    rw [← hP]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  have hP3 : IsPGroup 3 (P.subgroupOf H) := IsPGroup.of_card (n := 2) (by rw [hP']; norm_num)
  have hidx : ¬ 3 ∣ (P.subgroupOf H).index := by
    have h := (P.subgroupOf H).index_mul_card
    rw [hP', hH] at h
    have : (P.subgroupOf H).index = 64 := by omega
    rw [this]; norm_num
  let Psyl : Sylow 3 H := hP3.toSylow hidx
  set x' : H := ⟨x, hx⟩ with hx'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hz : IsPGroup 3 (Subgroup.zpowers x') := by
    intro y
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx'3, one_zpow]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Psyl Q
  have hxQ : x' ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers x')
  rw [← hg] at hxQ
  have h2 : (↑(g • Psyl) : Subgroup H) = MulAut.conj g • (Psyl : Subgroup H) :=
    Sylow.coe_subgroup_smul
  rw [h2, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  refine ⟨(g⁻¹ : H), (g⁻¹ : H).2, ?_⟩
  have hs' : s ∈ P.subgroupOf H := hs
  have e1 : g * s * g⁻¹ = x' := hsx
  have e2 : ((g⁻¹ : H) : G) * x * ((g⁻¹ : H) : G)⁻¹ = (s : G) := by
    have h3 : (g : G) * s * (g : G)⁻¹ = x := congrArg Subtype.val e1
    simp only [Subgroup.coe_inv, inv_inv]
    rw [← h3]
    group
  rw [e2]
  exact hs'

theorem odd_sub_of_card {H P : Subgroup G} (hH : Nat.card H = 576) (hPH : P ≤ H)
    (hP : Nat.card P = 9) (S : Subgroup G) (hSH : S ≤ H) (hS : Odd (Nat.card S)) :
    Nat.card S ∣ 9 ∧ (Nat.card S = 9 → ∃ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ S) := by
  refine ⟨?_, fun h9 => exists_conj_of_card_nine hH hPH hSH hP h9⟩
  have hdvd : Nat.card S ∣ 576 := by
    rw [← hH]
    have := Subgroup.card_dvd_of_le hSH
    exact this
  have hcop : Nat.Coprime (Nat.card S) 64 := by
    have h2 : Nat.Coprime (Nat.card S) 2 := Nat.coprime_two_right.mpr hS
    simpa using Nat.Coprime.pow_right 6 h2
  exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)

end CFSG.GH74.QTGen4.Recog.G23.P7.HFactsAux
