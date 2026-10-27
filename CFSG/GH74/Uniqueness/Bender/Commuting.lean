module

public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.GH74.Uniqueness.Bender.OuterFinal
public import CFSG.GH74.Uniqueness.Bender.Unitary

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Commuting

variable {K : Type*} [Group K] [Finite K]

theorem BenderCore.involution_mem_rootCenter_of_commute {q i e : ℕ} {P : Subgroup K} {t : K}
    (h : BenderCore q i e P t) {z y : K} (hz : z ∈ rootCenter P) (hz1 : z ≠ 1)
    (hyz : y * z = z * y) (hy : y * y = 1) (hy1 : y ≠ 1) : y ∈ rootCenter P := by
  have hyc : y ∈ centralizer ({z} : Set K) := Subgroup.mem_centralizer_singleton_iff.mpr hyz
  rw [h.centralizer_eq hz hz1] at hyc
  have hyM : y ∈ borel P :=
    (sup_le (le_borel P) ((fixCartan_le_cartan P t).trans (cartan_le_borel P t))) hyc
  exact (h.involution_iff.mp ⟨hyM, orderOf_eq_prime (by rw [sq]; exact hy) hy1⟩).1

theorem BenderType.commute_of_commute_involutions
    {n i e : ℕ} (h : BenderType K n i e)
    {a z y : K} (ha : a * a = 1) (hz : z * z = 1) (hy : y * y = 1) (hz1 : z ≠ 1)
    (haz : a * z = z * a) (hyz : y * z = z * y) : a * y = y * a := by
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  by_cases hy1 : y = 1
  · rw [hy1, one_mul, mul_one]
  have hordz : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz) hz1
  have hp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordz, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore S
  have hzS : z ∈ rootCenter (S : Subgroup K) :=
    (hc.involution_iff.mp ⟨le_borel _ (hS (Subgroup.mem_zpowers z)), hordz⟩).1
  have ha' := hc.involution_mem_rootCenter_of_commute hzS hz1 haz ha ha1
  have hy' := hc.involution_mem_rootCenter_of_commute hzS hz1 hyz hy hy1
  exact ((mem_rootCenter_iff.mp ha').2 y (rootCenter_le _ hy')).symm

end Commuting

section Unitary

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.fixed_of_commute_unitary
    {n e : ℕ} (h : BenderType K n 3 e) (α : MulAut K)
    (hα : α * α = 1) (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) {z y : K} (hz : z * z = 1)
    (hz1 : z ≠ 1) (hαz : α z = z) (hy : y * y = 1) (hyz : y * z = z * y) : α y = y := by
  by_cases hy1 : y = 1
  · rw [hy1, map_one]
  obtain ⟨hn, -⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  obtain ⟨e₁⟩ := h.fixed_unitary α hα hout
  have hL : BenderType (autFixed α) n 1 1 := BenderType.linear n hn e₁
  let z' : autFixed α := ⟨z, hαz⟩
  have hz'1 : z' ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hz'sq : z' * z' = 1 := Subtype.ext hz
  have hordz' : orderOf z' = 2 := orderOf_eq_prime (by rw [sq]; exact hz'sq) hz'1
  have hp : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordz', pow_one])
  obtain ⟨SA, hSA⟩ := hp.exists_le_sylow
  obtain ⟨tA, hcA⟩ := hL.exists_benderCore SA
  have hSAcard : Nat.card (SA : Subgroup (autFixed α)) = 2 ^ n := by
    rw [hcA.card_eq, pow_one]
  have hSAsq : ∀ x ∈ (SA : Subgroup (autFixed α)), x * x = 1 := by
    have heq : rootCenter (SA : Subgroup (autFixed α)) = SA :=
      Subgroup.eq_of_le_of_card_ge (rootCenter_le _) (le_of_eq (by rw [hcA.card_center, hSAcard]))
    intro x hx
    rw [← heq] at hx
    exact hcA.center_sq x hx
  set U : Subgroup K := (SA : Subgroup (autFixed α)).map (autFixed α).subtype with hU
  have hUcard : Nat.card U = 2 ^ n := by
    rw [hU, Subgroup.card_map_of_injective (autFixed α).subtype_injective, hSAcard]
  have hUsq : ∀ x ∈ U, x * x = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    exact congrArg Subtype.val (hSAsq s hs)
  have hUfix : ∀ x ∈ U, α x = x := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hzU : z ∈ U := ⟨z', hSA (Subgroup.mem_zpowers z'), rfl⟩
  obtain ⟨Q, hQ⟩ := (isPGroup_two_of_mul_self_eq_one hUsq).exists_le_sylow
  obtain ⟨t, hcQ⟩ := h.exists_benderCore Q
  have hUle : U ≤ rootCenter (Q : Subgroup K) := hcQ.elemAbelian_le_rootCenter hQ hUsq
  have hUeq : U = rootCenter (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hUle (le_of_eq (by rw [hcQ.card_center, hUcard]))
  have hyQ : y ∈ rootCenter (Q : Subgroup K) :=
    hcQ.involution_mem_rootCenter_of_commute (hUle hzU) hz1 hyz hy hy1
  rw [← hUeq] at hyQ
  exact hUfix y hyQ

end Unitary

theorem bender_outer_involution_sup
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (α : MulAut K) (hα : α * α = 1)
    (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) (S : Sylow 2 K) :
    (S : Subgroup K) ⊔ autFixed α = ⊤ := by
  obtain ⟨-, hS⟩ := bender_outer_involution hK α hα hout
  obtain ⟨x, hx, hxS⟩ := hS S
  obtain ⟨n, i, e, hT⟩ := isBenderGroup_iff_exists_benderType.mp hK
  obtain ⟨t, hc⟩ := hT.exists_benderCore S
  have : IsSimpleGroup K := hT.isSimple
  have h1 := hc.sup_zpowers_eq_top hxS
  rw [eq_top_iff, ← h1]
  exact sup_le_sup_left (Subgroup.zpowers_le.mpr hx) _

end CFSG.GH74.Uniqueness.Bender
