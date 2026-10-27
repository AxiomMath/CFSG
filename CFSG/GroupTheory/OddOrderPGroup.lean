module

public import Mathlib.GroupTheory.Nilpotent

public section

open scoped commutatorElement

namespace CFSG

variable {G : Type*} [Group G]

theorem mem_centralizer_of_odd_pow_eq_one {N P : Subgroup G} (hN : IsPGroup 2 N) {y : G}
    {m : ℕ} (hm : Odd m) (hy : y ^ m = 1)
    (hyN : y ∈ Subgroup.centralizer (N : Set G))
    (hyP : ∀ p ∈ P, ⁅y, p⁆ ∈ N) : y ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  set n : G := ⁅y, p⁆ with hn
  have hnN : n ∈ N := hyP p hp
  have hyn : Commute y n := (Subgroup.mem_centralizer_iff.mp hyN n hnN).symm
  have hyp : y * p * y⁻¹ = n * p := by rw [hn, commutatorElement_def]; group
  have hpow : ∀ k : ℕ, y ^ k * p * (y ^ k)⁻¹ = n ^ k * p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * p * (y ^ (k + 1))⁻¹
          = y * (y ^ k * p * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = y * (n ^ k * p) * y⁻¹ := by rw [ih]
        _ = (y * n ^ k * y⁻¹) * (y * p * y⁻¹) := by group
        _ = n ^ k * (n * p) := by rw [(hyn.pow_right k).eq, hyp]; group
        _ = n ^ (k + 1) * p := by rw [pow_succ]; group
  have hnm : n ^ m = 1 := by
    have h1 : p = n ^ m * p := by simpa [hy] using hpow m
    exact mul_right_cancel (a := n ^ m) (b := 1) (by simpa using h1.symm)
  obtain ⟨k, hk⟩ := hN ⟨n, hnN⟩
  have hk' : n ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : orderOf n ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hodd : Odd (orderOf n) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hnm)
  have hcop : Nat.Coprime (orderOf n) (2 ^ k) := (hodd.coprime_two_right).pow_right k
  have hn1 : n = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)
  have hcomm : y * p = p * y := by
    rw [hn1] at hyp
    rw [mul_inv_eq_iff_eq_mul] at hyp
    simpa using hyp
  exact hcomm.symm

theorem exists_normal_of_lt_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {U T : Subgroup G}
    (hT : IsPGroup p T) (hUT : U < T) :
    ∃ X : Subgroup G, U ≤ X ∧ X < T ∧ T ≤ Subgroup.normalizer (X : Set G) := by
  have hT' : IsPGroup p ↥T := hT
  haveI : Group.IsNilpotent ↥T := hT'.isNilpotent
  let U' : Subgroup T := U.subgroupOf T
  have hU'ne : U' ≠ ⊤ := by
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hUT.ne (le_antisymm hUT.le h)
  obtain ⟨M, hMcoat, hU'M⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom U').resolve_left hU'ne
  haveI : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M
    (Group.normalizerCondition_of_isNilpotent (G := ↥T)) hMcoat
  have hMlt : M < ⊤ := lt_of_le_of_ne le_top hMcoat.1
  refine ⟨M.map T.subtype, ?_, ?_, ?_⟩
  · intro u hu
    exact Subgroup.mem_map.mpr ⟨⟨u, hUT.le hu⟩, hU'M (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  · have h := (Subgroup.map_subtype_lt_map_subtype (G' := T) (H := M) (K := ⊤)).mpr hMlt
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  · have hXsub : (M.map T.subtype).subgroupOf T = M := by
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective T.subtype_injective M
    have hN : ((M.map T.subtype).subgroupOf T).Normal := by rw [hXsub]; exact ‹M.Normal›
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le M)).mp hN

end CFSG

end
