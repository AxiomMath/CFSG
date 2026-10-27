module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

@[expose] def InvConj (G : Type) [Group G] (f t : G) : Prop :=
  ∀ j ∈ centralizer ({f} : Set G), orderOf j = 2 → IsConj t j

theorem invConj_of_janko {G : Type} [Group G] [Finite G] (f t : G) (E : Subgroup G)
    (ht : orderOf t = 2) (hΓ : Nat.card ↥(centralizer ({f} : Set G)) = 877800)
    (hE : E ≤ centralizer ({f} : Set G)) (hE8 : Nat.card E = 8) (htE : t ∈ E)
    (htr : ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
      ∃ y ∈ centralizer ({f} : Set G), y * e * y⁻¹ = e') :
    InvConj G f t := by
  classical
  intro j hj hj2
  set Γ := centralizer ({f} : Set G)
  let E' : Subgroup Γ := E.subgroupOf Γ
  have hE'card : Nat.card E' = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv]; exact hE8
  have hfac : (Nat.card Γ).factorization 2 = 3 := by
    rw [hΓ]
    have : (877800 : ℕ) = 2 ^ 3 * 109725 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 109725 by norm_num)]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 Γ := Sylow.ofCard E' (by rw [hE'card, hfac]; norm_num)
  let jj : Γ := ⟨j, hj⟩
  have hjj : IsPGroup 2 (zpowers jj) := by
    apply IsPGroup.of_card
    · rw [Nat.card_zpowers]
      have : orderOf jj = orderOf j := Subgroup.orderOf_coe jj ▸ rfl
      rw [this, hj2]; exact (pow_one 2).symm
  obtain ⟨P, hP⟩ := hjj.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P S
  have hjP : jj ∈ P := hP (mem_zpowers jj)
  have hmem : g * jj * g⁻¹ ∈ (S : Subgroup Γ) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul jj (MulAut.conj g) _ hjP
  have hmemE : ((g * jj * g⁻¹ : Γ) : G) ∈ E := hmem
  have hne : ((g * jj * g⁻¹ : Γ) : G) ≠ 1 := by
    intro h1
    have : (g * jj * g⁻¹ : Γ) = 1 := Subtype.ext h1
    have : jj = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) this
      simpa [mul_assoc] using this
    have : j = 1 := congrArg Subtype.val this
    rw [this, orderOf_one] at hj2; exact absurd hj2 (by norm_num)
  have htne : t ≠ 1 := by rintro rfl; rw [orderOf_one] at ht; exact absurd ht (by norm_num)
  obtain ⟨y, -, hy⟩ := htr t htE htne _ hmemE hne
  refine isConj_iff.mpr ⟨(g : G)⁻¹ * y, ?_⟩
  have hy' : y * t * y⁻¹ = (g : G) * j * (g : G)⁻¹ := by rw [hy]; rfl
  rw [mul_inv_rev, inv_inv, show (g : G)⁻¹ * y * t * (y⁻¹ * (g : G)) =
    (g : G)⁻¹ * (y * t * y⁻¹) * (g : G) by group, hy']
  group

end CFSG.EvenSporadicStandard.RuStd.S2
