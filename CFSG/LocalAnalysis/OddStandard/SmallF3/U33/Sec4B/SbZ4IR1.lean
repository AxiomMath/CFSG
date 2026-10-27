module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

private lemma z4i_pow_two_eq_one_of_odd {k : ℕ} (h : Odd (2 ^ k)) : 2 ^ k = 1 := by
  by_contra hne
  have hk : k ≠ 0 := fun hk0 => hne (by rw [hk0, pow_zero])
  exact (Nat.not_even_iff_odd.mpr h) (Nat.even_pow.mpr ⟨even_two, hk⟩)

private lemma z4i_map_subtype_le {G : Type*} [Group G] {C : Subgroup G} (N' : Subgroup C) :
    N'.map C.subtype ≤ C := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

theorem z4i_odd_core {G : Type*} [Group G] [Finite G] {Q C : Subgroup G} (hQC : Q ≤ C)
    (hQ2 : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.relIndex C)
    (hcent : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c) :
    ∃ N : Subgroup G, N ≤ C ∧ Odd (Nat.card N) ∧ N ⊓ Q = ⊥ ∧ N ⊔ Q = C ∧
      (∀ c ∈ C, c ∈ N ↔ Odd (orderOf c)) ∧ ∀ n ∈ N, ∀ q ∈ Q, n * q = q * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q' : Subgroup C := Q.subgroupOf C
  have hQ'2 : IsPGroup 2 Q' := by
    show IsPGroup 2 (Q.comap C.subtype)
    exact hQ2.comap_subtype
  have hQ'i : ¬ 2 ∣ Q'.index := by
    show ¬ 2 ∣ Q.relIndex C
    exact hQi
  let P : Sylow 2 C := hQ'2.toSylow hQ'i
  have hPcoe : (P : Subgroup C) = Q' := IsPGroup.toSylow_coe hQ'2 hQ'i
  haveI : Finite (Sylow 2 C) := Sylow.finite_of_finiteIndex P
  have hPcent : Subgroup.normalizer (P : Set C) ≤ Subgroup.centralizer (P : Set C) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ' : (y : C) ∈ Q' := by
      have hyP : y ∈ (P : Subgroup C) := hy
      rwa [hPcoe] at hyP
    have hyQ : (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp hyQ'
    exact Subtype.ext ((hcent (x : G) x.property (y : G) hyQ).symm)
  let ψ : C →* P := MonoidHom.transferSylow P hPcent
  have hker : ψ.ker.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hPcent
  have hoddN' : Odd (Nat.card ψ.ker) := by
    have h := MonoidHom.not_dvd_card_ker_transferSylow P hPcent
    exact Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
  let N : Subgroup G := ψ.ker.map C.subtype
  have hNle : N ≤ C := z4i_map_subtype_le ψ.ker
  have hodd : Odd (Nat.card N) := by
    change Odd (Nat.card (ψ.ker.map C.subtype))
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hoddN'
  have hQmap : Q'.map C.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQC
  have hinf : N ⊓ Q = ⊥ := by
    have hmap : N ⊓ Q = (ψ.ker ⊓ Q').map C.subtype := by
      change (ψ.ker.map C.subtype) ⊓ Q = (ψ.ker ⊓ Q').map C.subtype
      rw [Subgroup.map_inf _ _ C.subtype C.subtype_injective, hQmap]
    rw [hmap, ← hPcoe, hker.disjoint.eq_bot, Subgroup.map_bot]
  have hsup : N ⊔ Q = C := by
    have hmap : N ⊔ Q = (ψ.ker ⊔ Q').map C.subtype := by
      change (ψ.ker.map C.subtype) ⊔ Q = (ψ.ker ⊔ Q').map C.subtype
      rw [Subgroup.map_sup, hQmap]
    rw [hmap, ← hPcoe, hker.sup_eq_top, Subgroup.map_top, Subgroup.range_subtype]
  have hiff : ∀ c ∈ C, c ∈ N ↔ Odd (orderOf c) := by
    intro c hc
    constructor
    · intro hcN
      change c ∈ ψ.ker.map C.subtype at hcN
      rw [Subgroup.mem_map] at hcN
      obtain ⟨n', hn', hval⟩ := hcN
      have horder : orderOf c = orderOf n' := by
        rw [← hval]
        simpa using Subgroup.orderOf_coe n'
      rw [horder]
      exact Odd.of_dvd_nat hoddN' (Subgroup.orderOf_dvd_natCard ψ.ker hn')
    · intro hodd
      let g : C := ⟨c, hc⟩
      have hgψ : ψ g = 1 := by
        have hdvd : orderOf (ψ g) ∣ orderOf c := by
          have h1 : orderOf (ψ g) ∣ orderOf g := orderOf_map_dvd ψ g
          have h2 : orderOf g = orderOf c := (Subgroup.orderOf_coe g).symm
          rwa [h2] at h1
        have hoddψ : Odd (orderOf (ψ g)) := Odd.of_dvd_nat hodd hdvd
        obtain ⟨k, hk⟩ := P.isPGroup'.exists_orderOf_eq_pow (ψ g)
        have hpk : 2 ^ k = 1 := by
          apply z4i_pow_two_eq_one_of_odd
          rw [← hk]
          exact hoddψ
        rw [← orderOf_eq_one_iff, hk, hpk]
      change c ∈ ψ.ker.map C.subtype
      rw [Subgroup.mem_map]
      exact ⟨g, MonoidHom.mem_ker.mpr hgψ, rfl⟩
  have hcomm : ∀ n ∈ N, ∀ q ∈ Q, n * q = q * n :=
    fun n hn q hq => hcent n (hNle hn) q hq
  exact ⟨N, hNle, hodd, hinf, hsup, hiff, hcomm⟩

theorem z4i_odd_core_normal {G : Type*} [Group G] {C N : Subgroup G}
    (hN : ∀ c ∈ C, c ∈ N ↔ Odd (orderOf c)) (hNC : N ≤ C) {g : G}
    (hg : ∀ c ∈ C, g * c * g⁻¹ ∈ C) : ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
  intro n hn
  have hnC : n ∈ C := hNC hn
  have hgnC : g * n * g⁻¹ ∈ C := hg n hnC
  rw [hN _ hgnC]
  have hconj : orderOf (g * n * g⁻¹) = orderOf n := by
    simpa only [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj g) n)
  rw [hconj]
  exact (hN n hnC).mp hn

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
