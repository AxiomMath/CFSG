module

public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.LieType.SteinbergBR

open CFSG.Blueprint CFSG.LieType.Ree
open scoped LinearAlgebra.Projectivization Pointwise

variable {a : ℕ} {K : Type} [Field K]

theorem isPGroup_suzukiU
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsPGroup 2 (suzukiU a K) := by
  apply IsPGroup.of_card (n := 2 * (2 * a + 1))
  rw [(suzuki_unipotent_structure hK).2.1, ← pow_mul, mul_comm]

theorem not_two_dvd_index_suzukiU
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ 2 ∣ (suzukiU a K).index := by
  have h := (suzukiU a K).index_mul_card
  rw [(suzuki_unipotent_structure hK).2.1, suzuki_order hK] at h
  have hq : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
  have h' : (suzukiU a K).index =
      (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    have h'' : (suzukiU a K).index * (2 ^ (2 * a + 1)) ^ 2 =
        ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) * (2 ^ (2 * a + 1)) ^ 2 := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_right hq h''
  rw [h', Nat.Prime.dvd_mul Nat.prime_two]
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  rintro (h3 | h3)
  · have : 2 ∣ 2 ^ (2 * a + 1) - (2 ^ (2 * a + 1) - 1) := Nat.dvd_sub h2 h3
    rw [Nat.sub_sub_self h1] at this
    exact absurd this (by norm_num)
  · have h4 : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := dvd_pow h2 two_ne_zero
    have : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 - (2 ^ (2 * a + 1)) ^ 2 := Nat.dvd_sub h3 h4
    rw [Nat.add_sub_cancel_left] at this
    exact absurd this (by norm_num)

theorem exists_le_conj_suzukiU
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {P : Subgroup (suzukiGroup a K)} (hP : IsPGroup 2 P) :
    ∃ g : suzukiGroup a K, ∀ x ∈ P, g⁻¹ * x * g ∈ suzukiU a K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (suzukiGroup a K) := Nat.finite_of_card_ne_zero (by
    rw [suzuki_order hK]
    have h1 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    have : 0 < 2 ^ (2 * a + 1) - 1 := by omega
    positivity)
  let S : Sylow 2 (suzukiGroup a K) := (isPGroup_suzukiU hK).toSylow (not_two_dvd_index_suzukiU hK)
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) S Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup (suzukiGroup a K)) := hPQ hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  change (MulAut.conj g)⁻¹ x ∈ suzukiU a K at hxQ
  rwa [MulAut.inv_apply, MulAut.conj_symm_apply] at hxQ

theorem smul_eq_of_mem_conj_suzukiU
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g x : suzukiGroup a K} (hx : g⁻¹ * x * g ∈ suzukiU a K) :
    x • (g • suzukiInfty K) = g • suzukiInfty K := by
  have h := suzukiB_le_stabilizer hK (suzukiU_le_suzukiB a K hx)
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul] at h
  rw [← smul_left_cancel_iff g⁻¹, h, inv_smul_smul]

theorem smul_ne_of_mem_conj_suzukiU
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g x : suzukiGroup a K} (hx : g⁻¹ * x * g ∈ suzukiU a K) (hx1 : x ≠ 1)
    {y : ℙ K (Fin 4 → K)} (hy : y ∈ suzukiOmega a K) (hyg : y ≠ g • suzukiInfty K) :
    x • y ≠ y := by
  intro hxy
  have hy' : g⁻¹ • y ∈ suzukiOmega a K \ {suzukiInfty K} := by
    refine ⟨suzuki_smul_mem_suzukiOmega hK g⁻¹ hy, fun h => hyg ?_⟩
    rw [Set.mem_singleton_iff] at h
    rw [← h, smul_inv_smul]
  obtain ⟨u, -, huniq⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _ hy' _ hy'
  have e1 : (⟨g⁻¹ * x * g, hx⟩ : suzukiU a K) = u := huniq _ (by
    change (g⁻¹ * x * g) • g⁻¹ • y = g⁻¹ • y
    rw [mul_smul, mul_smul, smul_inv_smul, hxy])
  have e2 : (1 : suzukiU a K) = u := huniq _ (one_smul _ _)
  have e3 : g⁻¹ * x * g = 1 := congrArg Subtype.val (e1.trans e2.symm)
  apply hx1
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [e3, mul_one, mul_inv_cancel]

end CFSG.LieType.SteinbergBR

namespace CFSG.LieType

open CFSG.Blueprint CFSG.LieType.Ree SteinbergBR

variable {a : ℕ} {K : Type} [Field K]

theorem suzuki_nontrivial_two_subgroup_normalizer_solvable [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (P : Subgroup (suzukiGroup a K)) (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥) :
    (∃ g : suzukiGroup a K, Subgroup.normalizer (P : Set (suzukiGroup a K)) ≤
      (suzukiB a K).map (MulAut.conj g).toMonoidHom) ∧
    Group.IsSolvable (Subgroup.normalizer (P : Set (suzukiGroup a K))) := by
  obtain ⟨g, hg⟩ := exists_le_conj_suzukiU hK hP
  obtain ⟨x, hxP, hx1⟩ := (P.bot_or_exists_ne_one).resolve_left hP1
  have hω : g • suzukiInfty K ∈ suzukiOmega a K :=
    suzuki_smul_mem_suzukiOmega hK g (suzukiInfty_mem_suzukiOmega a K)
  have hle : Subgroup.normalizer (P : Set (suzukiGroup a K)) ≤
      (suzukiB a K).map (MulAut.conj g).toMonoidHom := by
    intro n hn
    rw [← (suzuki_ovoid_stabilizer hK).1, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.mem_stabilizer_iff]
    by_contra hne
    refine smul_ne_of_mem_conj_suzukiU hK (hg x hxP) hx1 (suzuki_smul_mem_suzukiOmega hK n hω)
      hne ?_
    have hn' : n⁻¹ * x * n ∈ P := (Subgroup.mem_normalizer_iff''.1 hn x).1 hxP
    calc x • n • (g • suzukiInfty K) = n • ((n⁻¹ * x * n) • (g • suzukiInfty K)) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = n • (g • suzukiInfty K) := by rw [smul_eq_of_mem_conj_suzukiU hK (hg _ hn')]
  refine ⟨⟨g, hle⟩, ?_⟩
  have := (suzuki_borel_solvable hK).1
  have : Group.IsSolvable ((suzukiB a K).map (MulAut.conj g).toMonoidHom) :=
    Group.isSolvable_of_surjective
      ((MulAut.conj g).toMonoidHom.subgroupMap_surjective (suzukiB a K))
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end CFSG.LieType
