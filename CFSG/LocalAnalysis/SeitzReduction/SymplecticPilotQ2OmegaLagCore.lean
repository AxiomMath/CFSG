module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelLagCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaLagArith

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {K : Type} [Field K]

section Core

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (finrank_standard)

theorem mul_le_of_lagrangian {m n k : ℕ} (hn : n + 1 = 2 * m) (hk : k ≤ n) :
    (2 * n - 2 * k) * k ≤ 2 * m * (m - 1) := by
  rcases Nat.lt_or_ge k m with h | h
  · obtain ⟨t, ht⟩ : ∃ t, m = k + 1 + t := ⟨m - (k + 1), by omega⟩
    have e1 : 2 * n - 2 * k = 2 * k + 4 * t + 2 := by omega
    have e2 : m - 1 = k + t := by omega
    rw [e1, e2, ht]
    nlinarith
  · obtain ⟨t, u, ht, hu⟩ : ∃ t u, k = m + t ∧ m = t + 1 + u :=
      ⟨k - m, m - (k - m) - 1, by omega, by omega⟩
    have e1 : 2 * n - 2 * k = 2 * u := by omega
    have e2 : m - 1 = t + u := by omega
    rw [e1, e2, ht, hu]
    nlinarith

theorem card_le_of_lagrangian_core_of_not_dvd [Finite K] [CharP K 2] {H : Type} [Group H]
    [Finite H] {m n : ℕ} (hn : n + 1 = 2 * m) (ψ : H →* StatedSp n K)
    (hψ : Function.Injective ψ) (R X : Subgroup H) (hR : IsPGroup 2 R)
    (hXN : X ≤ normalizer (R : Set H)) [IsSimpleGroup X] (hXp : Group.IsPerfect X)
    (hRX : ⁅R, X⁆ = R) (hC : ∀ r ∈ R, (∀ x ∈ X, x * r = r * x) → r = 1)
    (hsmall : ∀ d, d ≤ n → ¬ Nat.card X ∣ ∏ i : Fin d, (Nat.card K ^ d - Nat.card K ^ (i : ℕ))) :
    Nat.card R ≤ Nat.card K ^ (2 * m * (m - 1)) := by
  have := Fintype.ofFinite K
  set ρ : H →* Module.End K (Fin n ⊕ Fin n → K) := (natRep (StatedSp n K)).comp ψ with hρdef
  have hρ : IsIsometric (spForm n K) ρ := fun h u v => isIsometric_natRep_statedSp n K (ψ h) u v
  have hinj : Function.Injective ρ := (natRep_injective _).comp hψ
  have hdimV : finrank K (Fin n ⊕ Fin n → K) = 2 * n := finrank_standard
  set W := isoSeq (spForm n K) ρ R (finrank K (Fin n ⊕ Fin n → K)) with hWdef
  have hWiso : (spForm n K).IsTotallyIsotropic W :=
    isoSeq_isTotallyIsotropic (spForm n K) ρ R (finrank K (Fin n ⊕ Fin n → K))
  have hk : 2 * finrank K W ≤ 2 * n := by
    have : 2 * finrank K W ≤ finrank K (Fin n ⊕ Fin n → K) :=
      two_mul_finrank_le_of_isTotallyIsotropic (spForm n K) hWiso
    omega
  have hXW : ∀ g ∈ X, ∀ u ∈ W, opNatEquiv ψ g u ∈ W := fun g hg u hu =>
    apply_mem_isoSeq (spForm n K) ρ hρ R _ (hXN hg) hu
  have hfixW : ∀ g ∈ X, ∀ u ∈ W, ρ g u = u := by
    set res := opRestrict (opNatEquiv ψ) X W hXW with hres
    have hnd : ¬ Nat.card X ∣ Nat.card (W ≃ₗ[K] W) := by
      rw [natCard_linearEquiv_self_eq, ← Nat.card_eq_fintype_card]
      exact hsmall _ (by omega)
    intro g hg u hu
    have h2 := eq_one_of_isSimpleGroup_of_not_dvd res hnd ⟨g, hg⟩
    exact congrArg (fun f : W ≃ₗ[K] W => ((f ⟨u, hu⟩ : W) : Fin n ⊕ Fin n → K)) h2
  have htriv : ∀ g ∈ X, ∀ k, ∀ v ∈ isoSeq (spForm n K) ρ R (k + 1),
      ρ g v - v ∈ isoSeq (spForm n K) ρ R k := fun g hg k v hv => by
    rw [hfixW g hg v (isoSeq_le_isoSeq_finrank _ ρ R _ hv), sub_self]
    exact zero_mem _
  have hcount := spBorelTitsCountInput_holds K (Fin n ⊕ Fin n → K) (spForm n K) H ρ hρ hinj R X
    hR hXN hXp hRX hC htriv
  refine hcount.trans (Nat.pow_le_pow_right Nat.card_pos ?_)
  have h := mul_le_of_lagrangian hn (k := finrank K W) (by omega)
  rw [← hdimV] at h
  exact h

theorem card_le_of_lagrangian_core_of_le_of_not_dvd [Finite K] [CharP K 2] {G : Type} [Group G]
    [Finite G] {P R X : Subgroup G} (hRP : R ≤ P) (hXP : X ≤ P) {m n : ℕ}
    (hn : n + 1 = 2 * m) (ψ : P →* StatedSp n K) (hψ : Function.Injective ψ)
    (hR : IsPGroup 2 R) (hXN : X ≤ normalizer (R : Set G)) [IsSimpleGroup X]
    (hXp : Group.IsPerfect X) (hRX : ⁅R, X⁆ = R)
    (hC : ∀ r ∈ R, (∀ x ∈ X, x * r = r * x) → r = 1)
    (hsmall : ∀ d, d ≤ n → ¬ Nat.card X ∣ ∏ i : Fin d, (Nat.card K ^ d - Nat.card K ^ (i : ℕ))) :
    Nat.card R ≤ Nat.card K ^ (2 * m * (m - 1)) := by
  have eR : R.subgroupOf P ≃* R := Subgroup.subgroupOfEquivOfLe hRP
  have eX : X.subgroupOf P ≃* X := Subgroup.subgroupOfEquivOfLe hXP
  have : IsSimpleGroup (X.subgroupOf P) := eX.isSimpleGroup
  have := hXp
  have hXp' : Group.IsPerfect (X.subgroupOf P) :=
    Group.IsPerfect.ofSurjective (f := eX.symm.toMonoidHom) eX.symm.surjective
  have hR' : IsPGroup 2 (R.subgroupOf P) := hR.of_equiv eR.symm
  have hXN' : X.subgroupOf P ≤ normalizer ((R.subgroupOf P : Subgroup P) : Set P) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.1 (hXN hg) h
  have hRX' : ⁅R.subgroupOf P, X.subgroupOf P⁆ = R.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hRP, inf_of_le_left hXP, hRX]
  have hC' : ∀ r ∈ R.subgroupOf P, (∀ y ∈ X.subgroupOf P, y * r = r * y) → r = 1 := by
    intro r hr hrX
    refine Subtype.ext (hC r hr fun y hy => ?_)
    exact congrArg Subtype.val (hrX ⟨y, hXP hy⟩ hy)
  have hsmall' : ∀ d, d ≤ n → ¬ Nat.card (X.subgroupOf P) ∣
      ∏ i : Fin d, (Nat.card K ^ d - Nat.card K ^ (i : ℕ)) := by
    intro d hd
    rw [Nat.card_congr eX.toEquiv]
    exact hsmall d hd
  rw [← Nat.card_congr eR.toEquiv]
  exact card_le_of_lagrangian_core_of_not_dvd hn ψ hψ _ _ hR' hXN' hXp' hRX' hC' hsmall'

end Core

end CFSG.SeitzReduction.SymplecticPilot
