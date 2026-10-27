module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mem_inf_of_four_dvd {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {x : G} (hxK : x ∈ K) (hxJ : x ∈ J)
    (hx : 4 ∣ orderOf x) : K = J := by
  by_contra hne
  have h1 := (hΩ.omega4 K hK J hJ hne).1
  have hle : Subgroup.zpowers x ≤ K ⊓ J := Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hxK, hxJ⟩)
  have hdvd : orderOf x ∣ Nat.card ↥(K ⊓ J) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have h4 : 2 ^ 2 ∣ Nat.card ↥(K ⊓ J) := (show (2 : ℕ) ^ 2 = 4 by norm_num) ▸ hx.trans hdvd
  have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
    (padicValNat_dvd_iff_le (Nat.card_pos).ne').mp h4
  omega

private theorem eq_one_of_odd_of_isPGroup {O P : Subgroup G} (hOodd : Odd (Nat.card ↥O))
    (hP : IsPGroup 2 ↥P) {g : G} (hgO : g ∈ O) (hgP : g ∈ P) : g = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g, hgP⟩
  have h1 : orderOf g ∣ 2 ^ k := by
    have h := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at h
  have h2 : Odd (orderOf g) := Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hgO)
  have h3 : Nat.Coprime (orderOf g) (2 ^ k) :=
    Nat.Coprime.pow_right k (Odd.coprime_two_right h2)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h1)

theorem exists_conj_eq_of_normal_complement {K O P : Subgroup G} (hOK : O ≤ K)
    (hOn : ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O) (hOodd : Odd (Nat.card ↥O))
    (hP : IsPGroup 2 ↥P) (hPK : P ≤ K) (hKOP : ∀ k ∈ K, ∃ o ∈ O, ∃ s ∈ P, k = o * s) {y k : G}
    (hy : y ∈ P) (hk : k ∈ K) (hky : k⁻¹ * y * k ∈ P) : ∃ s ∈ P, k⁻¹ * y * k = s⁻¹ * y * s := by
  obtain ⟨o, ho, s, hs, rfl⟩ := hKOP k hk
  have hyK : y ∈ K := hPK hy
  have hwP : o⁻¹ * y * o ∈ P := by
    have e : o⁻¹ * y * o = s * ((o * s)⁻¹ * y * (o * s)) * s⁻¹ := by group
    rw [e]
    exact P.mul_mem (P.mul_mem hs hky) (P.inv_mem hs)
  have hyo : y * o * y⁻¹ ∈ O := hOn y hyK o ho
  have hgO : (o⁻¹ * y * o) * y⁻¹ ∈ O := by
    have e : (o⁻¹ * y * o) * y⁻¹ = o⁻¹ * (y * o * y⁻¹) := by group
    rw [e]
    exact O.mul_mem (O.inv_mem ho) hyo
  have hgP : (o⁻¹ * y * o) * y⁻¹ ∈ P := P.mul_mem hwP (P.inv_mem hy)
  have h1 : (o⁻¹ * y * o) * y⁻¹ = 1 := eq_one_of_odd_of_isPGroup hOodd hP hgO hgP
  have hwy : o⁻¹ * y * o = y := mul_inv_eq_one.mp h1
  refine ⟨s, hs, ?_⟩
  calc (o * s)⁻¹ * y * (o * s) = s⁻¹ * (o⁻¹ * y * o) * s := by group
    _ = s⁻¹ * y * s := by rw [hwy]

end CFSG.CGT.PushingUpLit.SolKNA.R4
