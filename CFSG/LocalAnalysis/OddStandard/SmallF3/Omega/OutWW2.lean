module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Dihedral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem aor_componentAt_of_commute_case [Finite G] {X : Subgroup G} (hC : InC X)
    (hcase : ∀ {x₀ x : G}, orderOf x₀ = 2 → orderOf x = 2 → x₀ * x = x * x₀ →
      IsComponentIn X (centralizer ({x₀} : Set G)) → x ∈ centralizer (X : Set G) →
        IsComponentIn X (centralizer ({x} : Set G))) :
    ComponentAtCentralInvolutions X := by
  intro x hx hxX
  obtain ⟨x₀, hx₀, hXx₀⟩ := hC
  have hx₀X : x₀ ∈ centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXx₀.le ha)
  have ha : x₀ * x₀ = 1 := by
    rw [← pow_two]
    exact hx₀ ▸ pow_orderOf_eq_one x₀
  have hb : x * x = 1 := by
    rw [← pow_two]
    exact hx ▸ pow_orderOf_eq_one x
  have hprod : x₀ * x ∈ centralizer (X : Set G) := mul_mem hx₀X hxX
  rcases Nat.even_or_odd (orderOf (x₀ * x)) with hev | hodd
  · obtain ⟨n, hz, hza, hzb⟩ := exists_pow_involution_of_even_orderOf_mul ha hb hev
    have hzX : (x₀ * x) ^ n ∈ centralizer (X : Set G) := Subgroup.pow_mem _ hprod n
    have h1 : IsComponentIn X (centralizer ({(x₀ * x) ^ n} : Set G)) :=
      hcase hx₀ hz hza hXx₀ hzX
    exact hcase hz hx hzb.symm h1 hxX
  · obtain ⟨n, hn⟩ := exists_pow_inv_conj_of_odd_orderOf_mul ha hb hodd
    have hk : ((x₀ * x) ^ n)⁻¹ ∈ centralizer (X : Set G) :=
      inv_mem (Subgroup.pow_mem _ hprod n)
    have h := IsComponentIn.of_conj_centralizer hXx₀ hk
    rwa [hn] at h

end CFSG.OddStandard.SmallF3.Omega
