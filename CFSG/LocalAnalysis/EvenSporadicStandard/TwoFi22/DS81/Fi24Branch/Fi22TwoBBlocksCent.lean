module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42Basic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

private lemma centralizer_subgroupOf_normal {G : Type*} [Group G]
    (C Q : Subgroup G) (hQC : Q ≤ C) {X : Type*} [Group X] (π : ↥C →* X)
    (hker : π.ker = Q.subgroupOf C) :
    ((Subgroup.centralizer (Q : Set G)).subgroupOf C).Normal := by
  refine ⟨fun d hd c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hd ⊢
  rw [Subgroup.mem_centralizer_iff] at hd ⊢
  intro q hq
  have hqC : q ∈ C := hQC hq
  have hcq : c⁻¹ * (⟨q, hqC⟩ : ↥C) * c ∈ π.ker :=
    (inferInstance : π.ker.Normal).conj_mem' _ (by rw [hker]; exact hq) c
  have hmem : ((c⁻¹ * (⟨q, hqC⟩ : ↥C) * c : ↥C) : G) ∈ Q := by
    rw [hker, Subgroup.mem_subgroupOf] at hcq
    exact hcq
  have hcomm := hd ((c⁻¹ * (⟨q, hqC⟩ : ↥C) * c : ↥C) : G) hmem
  calc
    q * ((c * d * c⁻¹ : ↥C) : G)
        = (c : G) * ((((c⁻¹ * (⟨q, hqC⟩ : ↥C) * c : ↥C) : G) * (d : G))) *
            (c : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
          group
    _ = (c : G) * ((d : G) * (((c⁻¹ * (⟨q, hqC⟩ : ↥C) * c : ↥C) : G))) *
            (c : G)⁻¹ := by
          rw [hcomm]
    _ = ((c * d * c⁻¹ : ↥C) : G) * q := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
          group

theorem cent_le_of_quot {G : Type} [Group G]
    (C Q : Subgroup G) (hQC : Q ≤ C) {X : Type} [Group X] (π : ↥C →* X)
    (hπ : Function.Surjective π) (hker : π.ker = Q.subgroupOf C) (hX : IsU42Two X)
    (hcomm : ∃ a ∈ C, ∃ b ∈ C, ∀ d ∈ Subgroup.centralizer (Q : Set G), ∀ q ∈ Q,
      a * b * a⁻¹ * b⁻¹ ≠ d * q) :
    C ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
  classical
  let D : Subgroup ↥C := (Subgroup.centralizer (Q : Set G)).subgroupOf C
  let M : Subgroup X := D.map π
  have hDnormal : D.Normal := centralizer_subgroupOf_normal C Q hQC π hker
  have hMnormal : M.Normal := hDnormal.map π hπ
  obtain ⟨a, haC, b, hbC, hcomm'⟩ := hcomm
  let a' : ↥C := ⟨a, haC⟩
  let b' : ↥C := ⟨b, hbC⟩
  let c0 : ↥C := a' * b' * a'⁻¹ * b'⁻¹
  have hc0G : (c0 : G) = a * b * a⁻¹ * b⁻¹ := by
    simp only [c0, a', b', Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  have key : π c0 ∈ M → False := by
    intro hmem
    have hmem' : π c0 ∈ D.map π := hmem
    obtain ⟨d', hd'D, hd'π⟩ := Subgroup.mem_map.1 hmem'
    have hd'cent : (d' : G) ∈ Subgroup.centralizer (Q : Set G) := by
      have h := hd'D
      change d' ∈ (Subgroup.centralizer (Q : Set G)).subgroupOf C at h
      rwa [Subgroup.mem_subgroupOf] at h
    have hu_ker : c0⁻¹ * d' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hd'π, inv_mul_cancel]
    have hu_Q : ((c0⁻¹ * d' : ↥C) : G) ∈ Q := by
      have h := hu_ker
      rw [hker, Subgroup.mem_subgroupOf] at h
      exact h
    have hc0_eq : (c0 : G) = (d' : G) * (((c0⁻¹ * d')⁻¹ : ↥C) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact hcomm' (d' : G) hd'cent (((c0⁻¹ * d')⁻¹ : ↥C) : G) (Q.inv_mem hu_Q)
      (hc0G.symm.trans hc0_eq)
  have hM := hX.normal_eq M hMnormal
  intro x hx
  obtain ⟨hxC, hxcent⟩ := Subgroup.mem_inf.mp hx
  rcases hM with hbot | hidx | htop
  · have hDle : D ≤ π.ker := by
      have h : D.map π = ⊥ := hbot
      exact (Subgroup.map_eq_bot_iff (H := D) (f := π)).mp h
    have hxD : (⟨x, hxC⟩ : ↥C) ∈ D := by
      change (⟨x, hxC⟩ : ↥C) ∈ (Subgroup.centralizer (Q : Set G)).subgroupOf C
      rw [Subgroup.mem_subgroupOf]
      exact hxcent
    have hxN : (⟨x, hxC⟩ : ↥C) ∈ Q.subgroupOf C := by
      rw [← hker]
      exact hDle hxD
    have hxQ := hxN
    rw [Subgroup.mem_subgroupOf] at hxQ
    simpa using hxQ
  · exfalso
    apply key
    have h1 : π a' * π b' ∈ M ↔ (π a' ∈ M ↔ π b' ∈ M) :=
      Subgroup.mul_mem_iff_of_index_two (H := M) hidx
    have h2 : (π a')⁻¹ * (π b')⁻¹ ∈ M ↔ (π a' ∈ M ↔ π b' ∈ M) := by
      rw [Subgroup.mul_mem_iff_of_index_two (H := M) hidx, Subgroup.inv_mem_iff,
        Subgroup.inv_mem_iff]
    have h3 : (π a' * π b') * ((π a')⁻¹ * (π b')⁻¹) ∈ M := by
      rw [Subgroup.mul_mem_iff_of_index_two (H := M) hidx, h1, h2]
    have hc0pi : π c0 = (π a' * π b') * ((π a')⁻¹ * (π b')⁻¹) := by
      simp only [c0, map_mul, map_inv]
      group
    rwa [hc0pi]
  · exfalso
    apply key
    rw [htop]
    exact Subgroup.mem_top _

theorem O2In_eq_of_quot {G : Type} [Group G]
    (C Q : Subgroup G) (hQC : Q ≤ C) (hQ2 : IsPGroup 2 ↥Q) {X : Type} [Group X] (π : ↥C →* X)
    (hπ : Function.Surjective π) (hker : π.ker = Q.subgroupOf C) (hX : IsU42Two X) :
    TwoFi22.O2In C = Q := by
  classical
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  let N : Subgroup ↥C := Q.subgroupOf C
  have hNnormal : N.Normal := by
    change (Q.subgroupOf C).Normal
    rw [← hker]
    infer_instance
  have hN2 : IsPGroup 2 N := by
    change IsPGroup 2 (Q.subgroupOf C)
    exact hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  have hNleP : N ≤ CFSG.pCore 2 ↥C := by
    change (Q.subgroupOf C) ≤ sSup {K : Subgroup ↥C | K.Normal ∧ IsPGroup 2 K}
    exact le_sSup ⟨hNnormal, hN2⟩
  have hPnormal : (CFSG.pCore 2 ↥C).Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 (CFSG.pCore 2 ↥C) := CFSG.pCore_isPGroup
  let M : Subgroup X := (CFSG.pCore 2 ↥C).map π
  have hMnormal : M.Normal := hPnormal.map π hπ
  have hM2 : IsPGroup 2 M := by
    change IsPGroup 2 ((CFSG.pCore 2 ↥C).map π)
    exact hP2.map π
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hX.card_eq]; norm_num)
  have hMbot : M = ⊥ := by
    rcases hX.normal_eq M hMnormal with hbot | hidx | htop
    · exact hbot
    · exfalso
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hM2
      have hcard := Subgroup.card_mul_index M
      rw [hidx, hX.card_eq, hn] at hcard
      have h3 : 3 ∣ 2 ^ (n + 1) := by
        rw [pow_succ, hcard]
        norm_num
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
    · exfalso
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hM2
      have hcard : Nat.card M = Nat.card X := by
        have h := Subgroup.card_mul_index M
        rw [htop] at h ⊢
        simpa using h
      have h3 : 3 ∣ 2 ^ n := by
        rw [← hn, hcard, hX.card_eq]
        norm_num
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hPleN : CFSG.pCore 2 ↥C ≤ Q.subgroupOf C := by
    have hmap : (CFSG.pCore 2 ↥C).map π = ⊥ := hMbot
    have hle : CFSG.pCore 2 ↥C ≤ π.ker :=
      (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥C) (f := π)).mp hmap
    rwa [hker] at hle
  have hPN : CFSG.pCore 2 ↥C = Q.subgroupOf C := le_antisymm hPleN hNleP
  change (CFSG.pCore 2 ↥C).map C.subtype = Q
  rw [hPN, Subgroup.map_subgroupOf_eq_of_le hQC]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
