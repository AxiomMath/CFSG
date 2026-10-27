module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46W

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf_of_le_normalizer [Finite G] {H K : Subgroup G}
    (hK : H ≤ normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := relIndex_mul_card H (H ⊔ K)
  have h2 := relIndex_mul_card (H ⊓ K) K
  rw [inf_eq_left.mpr le_sup_left] at h1
  rw [inf_eq_left.mpr inf_le_right] at h2
  rw [relIndex_sup_eq_relIndex_inf_of_normalizes hK] at h1
  rw [← h1, ← h2]
  ring

theorem eq_one_of_mem_two_of_mem_odd [Finite G] {S O : Subgroup G} (hS : IsPGroup 2 S)
    (hO : Odd (Nat.card O)) {y : G} (hyS : y ∈ S) (hyO : y ∈ O) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(S ⊓ O) := hS.to_le inf_le_left
  have hco := hO.of_dvd_nat (card_dvd_of_le (inf_le_right : S ⊓ O ≤ O))
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rw [hk] at hco
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hco) ((Nat.even_pow' hk0).mpr even_two)
  rw [hk0, pow_zero] at hk
  have hmem : y ∈ S ⊓ O := mem_inf.mpr ⟨hyS, hyO⟩
  rw [card_eq_one.mp hk, mem_bot] at hmem
  exact hmem

theorem mul_comm_of_mem_coreActionKernel [Finite G] {S J : Subgroup G} (hS : IsPGroup 2 S)
    {k p : G} (hkS : k ∈ S) (hk : k ∈ coreActionKernel J) (hpS : p ∈ S) (hpJ : p ∈ J) :
    k * p = p * k := by
  have h1 : p⁻¹ * k⁻¹ * p * k = 1 :=
    eq_one_of_mem_two_of_mem_odd hS (odd_card_map_pPrimeCore J)
      (mul_mem (mul_mem (mul_mem (inv_mem hpS) (inv_mem hkS)) hpS) hkS)
      ((mem_coreActionKernel.mp hk).2 p hpJ)
  calc k * p = k * p * (p⁻¹ * k⁻¹ * p * k) := by rw [h1, mul_one]
    _ = p * k := by group

theorem card_inf_eq_of_isSylowTwoIn [Finite G] {S N X : Subgroup G} (hS : IsSylowTwoIn S N)
    (hXN : X ≤ N) (hNX : N ≤ normalizer (X : Set G)) :
    Nat.card ↥(S ⊓ X) = 2 ^ (Nat.card X).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := GSThmB.exists_sylow_inf_of_le_normalizer hXN hNX hS.1 hS.2
  rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : S ⊓ X ≤ X)).toEquiv, ← hR,
    Sylow.card_eq_multiplicity]

theorem inf_withKernel_le [Finite G] {J S : Subgroup G}
    (hS : IsSylowTwoIn S (normalizer (J : Set G))) :
    S ⊓ withKernel J ≤ S ⊓ J ⊔ S ⊓ coreActionKernel J := by
  set N : Subgroup G := normalizer (J : Set G) with hN
  set K : Subgroup G := coreActionKernel J with hK
  have hJN : J ≤ N := le_normalizer
  have hKN : K ≤ N := fun k hk => (mem_coreActionKernel.mp hk).1
  have hNK : N ≤ normalizer (K : Set G) :=
    UnbalancedLayer.normalizer_le_normalizer_coreActionKernel J
  have hNsup : N ≤ normalizer ((J ⊔ K : Subgroup G) : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro y
    have hmap : ∀ m ∈ N, (J ⊔ K).map (MulAut.conj m).toMonoidHom ≤ J ⊔ K := fun m hm => by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨j, hj, rfl⟩
        exact (mem_normalizer_iff.mp hm j).mp hj
      · rintro _ ⟨k, hk, rfl⟩
        exact (mem_normalizer_iff.mp (hNK hm) k).mp hk
    refine ⟨fun hy => hmap n hn ⟨y, hy, rfl⟩, fun hy => ?_⟩
    have h : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ ∈ J ⊔ K := hmap n⁻¹ (inv_mem hn) ⟨_, hy, rfl⟩
    rwa [show n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y by group] at h
  have hNinf : N ≤ normalizer ((J ⊓ K : Subgroup G) : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp hn y, ← mem_normalizer_iff.mp (hNK hn) y]
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have cJ := card_inf_eq_of_isSylowTwoIn hS hJN le_rfl
  have cK := card_inf_eq_of_isSylowTwoIn hS hKN hNK
  have cJK := card_inf_eq_of_isSylowTwoIn hS (sup_le hJN hKN) hNsup
  have cJiK := card_inf_eq_of_isSylowTwoIn hS (inf_le_left.trans hJN) hNinf
  have hprod := card_sup_mul_card_inf_of_le_normalizer (hJN.trans hNK)
  have hfac : (Nat.card ↥(J ⊔ K)).factorization 2 + (Nat.card ↥(J ⊓ K)).factorization 2 =
      (Nat.card J).factorization 2 + (Nat.card K).factorization 2 := by
    have h := congrArg (fun n => n.factorization 2) hprod
    rwa [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Finsupp.add_apply] at h
  have hSJK : S ⊓ J ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp (hNK (hJN (mem_inf.mp hs).2)) y]
    constructor
    · rintro ⟨hyS, hyK⟩
      exact ⟨mul_mem (mul_mem (mem_inf.mp hs).1 hyS) (inv_mem (mem_inf.mp hs).1), hyK⟩
    · rintro ⟨hyS, hyK⟩
      refine ⟨?_, hyK⟩
      have h := mul_mem (mul_mem (inv_mem (mem_inf.mp hs).1) hyS) (mem_inf.mp hs).1
      rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h
  have hprod2 := card_sup_mul_card_inf_of_le_normalizer hSJK
  have hii : (S ⊓ J) ⊓ (S ⊓ K) = S ⊓ (J ⊓ K) := by
    ext y
    simp only [mem_inf]
    tauto
  rw [hii, cJ, cK, cJiK] at hprod2
  have hle : S ⊓ J ⊔ S ⊓ K ≤ S ⊓ (J ⊔ K) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  have hcard : Nat.card ↥(S ⊓ J ⊔ S ⊓ K) = Nat.card ↥(S ⊓ (J ⊔ K)) := by
    rw [cJK]
    have h2pos : 0 < 2 ^ (Nat.card ↥(J ⊓ K)).factorization 2 := by positivity
    refine Nat.eq_of_mul_eq_mul_right h2pos ?_
    rw [hprod2, ← pow_add, ← pow_add, hfac]
  have heq := eq_of_le_of_card_ge hle hcard.ge
  intro t ht
  rw [heq]
  exact ht

end CFSG.ComponentClassification.GrSLit.GrS4
