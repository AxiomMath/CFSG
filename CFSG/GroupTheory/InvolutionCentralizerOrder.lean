module

public import CFSG.GroupTheory.InvolutionFixedCentralSylow

public section

namespace CFSG.GroupTheory

open Subgroup

theorem even_card_inf_centralizer_of_mem_normalizer {G : Type*} [Group G] [Finite G] {u : G}
    (hu : u * u = 1) {T : Subgroup G} (hT : u ∈ normalizer (T : Set G))
    (hTe : Even (Nat.card T)) : Even (Nat.card ↥(T ⊓ centralizer ({u} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rwa [pow_one, pow_two])
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hP : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨a, haT, ha2, hacomm⟩ := exists_involution_commute_of_isPGroup_le_normalizer hP
    (zpowers_le.2 hT) hTe
  have haC : a ∈ T ⊓ centralizer ({u} : Set G) :=
    ⟨haT, mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]; exact hacomm u (mem_zpowers u)⟩
  rw [even_iff_two_dvd]
  have := orderOf_dvd_natCard (⟨a, haC⟩ : ↥(T ⊓ centralizer ({u} : Set G)))
  rwa [Subgroup.orderOf_mk, ha2] at this

theorem not_four_dvd_card_of_inf_centralizer_eq_zpowers {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} {a : G} (haT : a ∈ T) (ha : orderOf a = 2)
    (hc : T ⊓ centralizer ({a} : Set G) = zpowers a) : ¬ 4 ∣ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup T := (zpowers a).subgroupOf T
  have hcardA : Nat.card A = 2 := by
    have e : A ≃* Subgroup.zpowers a := Subgroup.subgroupOfEquivOfLe (zpowers_le.2 haT)
    rw [Nat.card_congr e.toEquiv, Nat.card_zpowers, ha]
  have hA : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by rw [hcardA, pow_one])
  obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow hA
  intro h4
  have h4S : 4 ∣ Nat.card (S : Subgroup T) := by
    have h := S.pow_dvd_card_of_pow_dvd_card (n := 2) (by simpa using h4)
    simpa using h
  have hcardS : 4 ≤ Nat.card (S : Subgroup T) := Nat.le_of_dvd Nat.card_pos h4S
  haveI : Nontrivial ↥(S : Subgroup T) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have haA : (⟨a, haT⟩ : T) ∈ A := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a)
  have haS : (⟨a, haT⟩ : T) ∈ (S : Subgroup T) := hAS haA
  have hcenter_le : Subgroup.center ↥(S : Subgroup T) ≤ A.subgroupOf (S : Subgroup T) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    have hcomm : (⟨a, haT⟩ : T) * (z : T) = (z : T) * (⟨a, haT⟩ : T) := by
      have h := Subgroup.mem_center_iff.mp hz (⟨⟨a, haT⟩, haS⟩ : ↥(S : Subgroup T))
      simpa using congrArg (fun w : ↥(S : Subgroup T) => (w : T)) h
    have hmem : ((z : T) : G) ∈ T ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨(z : T).2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg (fun w : T => (w : G)) hcomm).symm⟩
    rw [hc] at hmem
    exact Subgroup.mem_subgroupOf.mpr hmem
  have hcardAS : Nat.card (A.subgroupOf (S : Subgroup T)) = 2 := by
    have e : A.subgroupOf (S : Subgroup T) ≃* A := Subgroup.subgroupOfEquivOfLe hAS
    rw [Nat.card_congr e.toEquiv, hcardA]
  have hcenter_nt : Nontrivial ↥(Subgroup.center ↥(S : Subgroup T)) :=
    S.isPGroup'.center_nontrivial
  have hcenter_eq : Subgroup.center ↥(S : Subgroup T) = A.subgroupOf (S : Subgroup T) :=
    Subgroup.eq_of_le_of_card_ge hcenter_le (by
      rw [hcardAS]
      have h := Finite.one_lt_card_iff_nontrivial.mpr hcenter_nt
      omega)
  have ha_center : (⟨⟨a, haT⟩, haS⟩ : ↥(S : Subgroup T)) ∈
      Subgroup.center ↥(S : Subgroup T) := by
    rw [hcenter_eq]
    exact Subgroup.mem_subgroupOf.mpr haA
  have hSA : (S : Subgroup T) ≤ A := by
    intro x hx
    have hcomm : x * (⟨a, haT⟩ : T) = (⟨a, haT⟩ : T) * x := by
      have h := Subgroup.mem_center_iff.mp ha_center (⟨x, hx⟩ : ↥(S : Subgroup T))
      simpa using congrArg (fun w : ↥(S : Subgroup T) => (w : T)) h
    rw [Subgroup.mem_subgroupOf]
    have hmem : (x : G) ∈ T ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg (fun w : T => (w : G)) hcomm)⟩
    rw [hc] at hmem
    exact hmem
  have hcardSA : Nat.card (S : Subgroup T) ≤ Nat.card A := Subgroup.card_le_of_le hSA
  rw [hcardA] at hcardSA
  omega

end CFSG.GroupTheory
