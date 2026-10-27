module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l771_inf_C_bot [Finite G] {K P : Subgroup G} {z : G}
    (hZK : K ⊓ centralizer (K : Set G) = ⊥) (hPN : P ≤ normalizer (K : Set G))
    (hP2 : IsPGroup 2 P) (hzK : z ∈ K) (hz1 : z ≠ 1)
    (hZP : ∀ y ∈ P, (∀ x ∈ P, x * y = y * x) → y = 1 ∨ y = z) :
    P ⊓ centralizer (K : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer (K : Set G)
  let H : Subgroup ↥P := (P ⊓ C).subgroupOf P
  have hPnormC : P ≤ normalizer (C : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
      have hxK : x⁻¹ * k * x ∈ K := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hPN (P.inv_mem hx)) k).mp hk
      have hck : (x⁻¹ * k * x) * c = c * (x⁻¹ * k * x) :=
        Subgroup.mem_centralizer_iff.mp hc _ hxK
      calc k * (x * c * x⁻¹) = x * ((x⁻¹ * k * x) * c) * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * k * x)) * x⁻¹ := by rw [hck]
        _ = (x * c * x⁻¹) * k := by group
    · intro hc
      refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
      have hxK : x * k * x⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hPN hx) k).mp hk
      have hck : (x * k * x⁻¹) * (x * c * x⁻¹) = (x * c * x⁻¹) * (x * k * x⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hc _ hxK
      have hkc : x * k * c * x⁻¹ = x * c * k * x⁻¹ := by
        calc x * k * c * x⁻¹ = (x * k * x⁻¹) * (x * c * x⁻¹) := by group
          _ = (x * c * x⁻¹) * (x * k * x⁻¹) := hck
          _ = x * c * k * x⁻¹ := by group
      calc k * c = x⁻¹ * (x * k * c * x⁻¹) * x := by group
        _ = x⁻¹ * (x * c * k * x⁻¹) * x := by rw [hkc]
        _ = c * k := by group
  haveI hHnorm : H.Normal := by
    have hle : P ≤ normalizer (P ⊓ C : Subgroup G) :=
      (le_inf Subgroup.le_normalizer hPnormC).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact Subgroup.normal_subgroupOf_of_le_normalizer hle
  haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
  by_contra hne
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hbot' : (P ⊓ C).subgroupOf P = ⊥ := hbot
    have hd : Disjoint (P ⊓ C) P := Subgroup.subgroupOf_eq_bot.mp hbot'
    have hPC : P ⊓ C ≤ P := inf_le_left
    have hbot'' : P ⊓ C = ⊥ := by
      have h := disjoint_iff.mp hd
      rwa [inf_eq_left.mpr hPC] at h
    exact hne hbot''
  have hcenter_ne : H ⊓ Subgroup.center ↥P ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter_ne
  have huH : (u : ↥P) ∈ (P ⊓ C).subgroupOf P := u.2.1
  have hucent : (u : ↥P) ∈ Subgroup.center ↥P := u.2.2
  have hu1P : (u : ↥P) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have h2dvd : 2 ∣ orderOf (u : ↥P) := hP2.dvd_orderOf hu1P
  have h2dvd' : 2 ∣ Nat.card (Subgroup.zpowers (u : ↥P)) := by
    rwa [Nat.card_zpowers]
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers (u : ↥P)) 2 h2dvd'
  have hvH : (v : ↥P) ∈ (P ⊓ C).subgroupOf P := (Subgroup.zpowers_le.mpr huH) v.2
  have hvPC : ((v : ↥P) : G) ∈ P ⊓ C := hvH
  have hvC : ((v : ↥P) : G) ∈ C := hvPC.2
  have hcommP : ∀ x ∈ P, x * ((v : ↥P) : G) = ((v : ↥P) : G) * x := by
    intro x hx
    have hvcent : (v : ↥P) ∈ Subgroup.center ↥P :=
      (Subgroup.zpowers_le.mpr hucent) v.2
    have h := Subgroup.mem_center_iff.mp hvcent (⟨x, hx⟩ : ↥P)
    exact congrArg Subtype.val h
  have hv_ord : orderOf ((v : ↥P) : G) = 2 := by
    rw [Subgroup.orderOf_coe (v : ↥P), Subgroup.orderOf_coe v, hv]
  rcases hZP ((v : ↥P) : G) hvPC.1 hcommP with hv1 | hvz
  · rw [hv1, orderOf_one] at hv_ord
    norm_num at hv_ord
  · have hzC : z ∈ C := by rw [← hvz]; exact hvC
    have hzbot : z ∈ (⊥ : Subgroup G) := by
      rw [← hZK]
      exact ⟨hzK, hzC⟩
    exact hz1 (Subgroup.mem_bot.mp hzbot)

end CFSG.OddStandard.SmallF3.Omega
