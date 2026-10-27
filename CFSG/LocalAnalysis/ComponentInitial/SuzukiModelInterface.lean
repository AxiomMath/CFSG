module

public import CFSG.LocalAnalysis.ComponentInitial.SuzukiOppositeSylow
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint CFSG.LieType.Ree
open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiU_isPGroup_index [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsPGroup 2 (suzukiU a K) ∧ ¬ 2 ∣ (suzukiU a K).index := by
  have hU := (suzuki_unipotent_structure hK).2.1
  refine ⟨IsPGroup.of_card (n := 2 * (2 * a + 1)) (by rw [hU, ← pow_mul, mul_comm]), ?_⟩
  have h := (suzukiU a K).card_mul_index
  rw [hU, suzuki_order hK, mul_assoc] at h
  have hidx := Nat.eq_of_mul_eq_mul_left (by positivity) h
  rw [hidx]
  have h1 : ¬ 2 ∣ 2 ^ (2 * a + 1) - 1 := by
    have : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
    have : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    omega
  have h2 : ¬ 2 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    have : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
    omega
  exact fun h => (Nat.prime_two.dvd_mul.1 h).elim h1 h2

theorem Suzuki_model_opposite_root_interface (ha : 1 ≤ a) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ P : Sylow 2 (suzukiGroup a K), (P : Subgroup (suzukiGroup a K)) = suzukiU a K ∧
      Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) = suzukiB a K ∧
      ((P : Subgroup (suzukiGroup a K)).map (MulAut.conj (suzukiWElt a K)).toMonoidHom :
        Subgroup (suzukiGroup a K)) = ((suzukiWElt a K • P : Sylow 2 (suzukiGroup a K)) :
          Subgroup (suzukiGroup a K)) ∧
      (∃ φ : suzukiOmegaSub hK ≃ Sylow 2 (suzukiGroup a K),
        (∀ (g : suzukiGroup a K) x, φ (g • x) = g • φ x) ∧
        φ ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ = P ∧
        φ ⟨suzukiLine a K 0 0, suzukiLine_mem_suzukiOmega a K 0 0⟩ = suzukiWElt a K • P ∧
        (∀ ψ : suzukiOmegaSub hK ≃ Sylow 2 (suzukiGroup a K),
          (∀ (g : suzukiGroup a K) x, ψ (g • x) = g • ψ x) →
            ψ ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ = P → ψ = φ) ∧
        ∃ τ : MulAut (suzukiGroup a K) →* Equiv.Perm (suzukiOmegaSub hK),
          Function.Injective τ ∧ ∀ α x, φ (τ α x) = α • φ x) ∧
      (∀ α : MulAut (suzukiGroup a K), ∃ g : suzukiGroup a K, ∃ β ∈ pairAutSubgroup
        (suzukiU a K) ((suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom),
          α = MulAut.conj g * β) ∧
      Function.Injective (pairAutRestrict (suzukiU a K)
        ((suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom)) := by
  obtain ⟨hpg, hidx⟩ := suzukiU_isPGroup_index hK
  set P : Sylow 2 (suzukiGroup a K) := hpg.toSylow hidx with hP
  have hPU : (P : Subgroup (suzukiGroup a K)) = suzukiU a K := hpg.toSylow_coe hidx
  have hdt := suzuki_ovoid_double_transitivity hK
  have : MulAction.IsMultiplyPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) 2 := hdt.2.2.1
  have : MulAction.IsPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : FaithfulSMul (suzukiGroup a K) (suzukiOmegaSub hK) := (suzuki_ovoid_faithful ha hK).2
  have : Finite (suzukiOmegaSub hK) := Subtype.finite
  set ξ : suzukiOmegaSub hK := ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ with hξ
  set o : suzukiOmegaSub hK := ⟨suzukiLine a K 0 0, suzukiLine_mem_suzukiOmega a K 0 0⟩ with ho
  have hΩ : 3 ≤ Nat.card (suzukiOmegaSub hK) := by
    have h := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.2
    change 3 ≤ Nat.card (suzukiOmega a K)
    rw [Nat.card_coe_set_eq, h]
    have : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
    nlinarith
  have hstab := (suzuki_ovoid_stabilizer hK).2
  have hUξ : (P : Subgroup (suzukiGroup a K)) ≤ MulAction.stabilizer (suzukiGroup a K) ξ := by
    rw [hPU, hstab]
    exact suzukiU_le_suzukiB a K
  have hBN : suzukiB a K ≤ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
    sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)
  have hUn : ((P : Subgroup (suzukiGroup a K)).subgroupOf
      (MulAction.stabilizer (suzukiGroup a K) ξ)).Normal := by
    rw [hPU, hstab]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (suzukiU_le_suzukiB a K)).2 hBN
  have htr : ∀ ω ω' : suzukiOmegaSub hK, ω ≠ ξ → ω' ≠ ξ →
      ∃ u : (P : Subgroup (suzukiGroup a K)), (u : suzukiGroup a K) • ω = ω' := by
    intro ω ω' h1 h2
    have hω : (ω : ℙ K (Fin 4 → K)) ∈ suzukiOmega a K \ {suzukiInfty K} :=
      ⟨ω.2, fun h => h1 (Subtype.ext h)⟩
    have hω' : (ω' : ℙ K (Fin 4 → K)) ∈ suzukiOmega a K \ {suzukiInfty K} :=
      ⟨ω'.2, fun h => h2 (Subtype.ext h)⟩
    obtain ⟨⟨u, hu⟩, hu', -⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _ hω _ hω'
    refine ⟨⟨u, hPU ▸ hu⟩, Subtype.ext ?_⟩
    rw [SubMulAction.val_smul]
    exact hu'
  have hWξ : suzukiWElt a K • ξ = o := Subtype.ext (by
    rw [SubMulAction.val_smul]
    exact (suzuki_ovoid_weyl_action a hK).1)
  have hoξ : o ≠ ξ := fun h => suzukiLine_ne_suzukiInfty (a := a) (0 : K) 0
    (congrArg Subtype.val h)
  obtain ⟨-, hnorm, -, huniq, φ, hφ, hφξ, hφg, τ, hτφ, hτinj, -, -⟩ :=
    Suzuki_Sylow_point_recovery hΩ ξ P hUξ hUn htr
  obtain ⟨-, hinj, hInnC, -⟩ :=
    Suzuki_opposite_Sylow_restriction hΩ ξ P hUξ hUn htr (suzukiWElt a K) (by rw [hWξ]; exact hoξ)
  refine ⟨P, hPU, ?_, (coe_smul_sylow' _ _).symm, ⟨φ, hφ, hφξ, ?_, fun ψ hψ hψξ =>
    huniq ψ φ hψ hψξ hφ hφξ, τ, hτinj, hτφ⟩, ?_, ?_⟩
  · rw [← hPU, hnorm, hstab]
  · rw [← hWξ, hφg]
  · rw [← hPU]
    exact hInnC
  · rw [← hPU]
    exact hinj

end CFSG.LocalAnalysis.ComponentInitial
