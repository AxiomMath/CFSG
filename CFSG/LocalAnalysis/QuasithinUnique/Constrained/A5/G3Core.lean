module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.QuasithinUnique.A5.G3

open Subgroup

variable {G : Type*} [Group G]

theorem perfect_coe {K : Subgroup G} (hperf : ⁅K, K⁆ = K) : _root_.commutator ↥K = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  show Subgroup.map K.subtype ⁅(⊤ : Subgroup ↥K), ⊤⁆ = _
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]

theorem no_index_two {K : Subgroup G} (hperf : ⁅K, K⁆ = K) (N : Subgroup ↥K) (hN : N.index = 2) :
    False := by
  have hnorm : N.Normal := Subgroup.normal_of_index_eq_two hN
  have hcard : Nat.card (↥K ⧸ N) = 2 := by rw [← Subgroup.index, hN]
  have : Fact (Nat.Prime (Nat.card (↥K ⧸ N))) := ⟨by rw [hcard]; exact Nat.prime_two⟩
  have : IsCyclic (↥K ⧸ N) := isCyclic_of_prime_card rfl
  let _ : CommGroup (↥K ⧸ N) := IsCyclic.commGroup
  have h1 := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [perfect_coe hperf, QuotientGroup.ker_mk'] at h1
  have : N = ⊤ := top_le_iff.mp h1
  rw [this, Subgroup.index_top] at hN
  omega

theorem eq_top_of_perfect_of_solvable_quotient [Finite G] {K : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (M : Subgroup ↥K) [M.Normal] (hsolv : Group.IsSolvable (↥K ⧸ M)) : M = ⊤ := by
  have h3 : Subgroup.map (QuotientGroup.mk' M) (⊤ : Subgroup ↥K) = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M)
  have hcomm : _root_.commutator (↥K ⧸ M) = ⊤ := by
    have h1 := perfect_coe hperf
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ (QuotientGroup.mk' M)
    rw [h3] at h2
    have h4 : _root_.commutator ↥K = ⁅(⊤ : Subgroup ↥K), ⊤⁆ := rfl
    rw [h4] at h1
    rw [h1, h3] at h2
    exact h2.symm
  by_contra hM
  have hne : (⊤ : Subgroup (↥K ⧸ M)) ≠ ⊥ := by
    intro h
    apply hM
    refine eq_top_iff.mpr fun x _ => ?_
    have : (QuotientGroup.mk x : ↥K ⧸ M) ∈ (⊥ : Subgroup (↥K ⧸ M)) := h ▸ Subgroup.mem_top _
    exact (QuotientGroup.eq_one_iff x).mp this
  have := (Group.isSolvable_iff_commutator_lt.mp hsolv) ⊤ hne
  have h4 : _root_.commutator (↥K ⧸ M) = ⁅(⊤ : Subgroup (↥K ⧸ M)), ⊤⁆ := rfl
  rw [← h4, hcomm] at this
  exact lt_irrefl _ this

theorem eq_of_sup_normal [Finite G] {K L Q P : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hLK : L ≤ K) (hQK : Q ≤ K) (hQn : (Q.subgroupOf K).Normal)
    (hQ2 : IsPGroup 2 Q) (hK : K = L ⊔ Q) (hPK : P ≤ K) (hQP : Q ≤ P)
    (hidx : (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P ∣ 2) : L = K := by
  have hKN : K ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mp hQn
  have hLN : L ≤ Subgroup.normalizer (Q : Set G) := hLK.trans hKN
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right L Q hLN
  have hidx2 : (K ⊓ Subgroup.normalizer (L : Set G)).relIndex K ∣ 2 := by
    obtain ⟨a, haP, ha⟩ := (Subgroup.relIndex_dvd_two_iff).mp hidx
    refine Subgroup.relIndex_dvd_two_iff.mpr ⟨a, hPK haP, fun b hb => ?_⟩
    have hb' : b ∈ ((L ⊔ Q : Subgroup G) : Set G) := hK ▸ hb
    rw [hmul] at hb'
    obtain ⟨l, hl, q, hq, rfl⟩ := hb'
    have hqP : q ∈ P := hQP hq
    have hlK : l ∈ K := hLK hl
    have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
    rcases ha q hqP with h | h
    · left
      refine ⟨?_, ?_⟩
      · rw [mul_assoc]
        exact K.mul_mem hlK (K.mul_mem (hQK hq) (hPK haP))
      · rw [mul_assoc]
        exact Subgroup.mul_mem _ hlN h.2
    · right
      exact ⟨K.mul_mem hlK (hQK hq), Subgroup.mul_mem _ hlN h.2⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx2 with h1 | h2
  ·
    have hKL : K ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
      ((Subgroup.relIndex_eq_one.mp h1) hx).2
    have hMn : (L.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr hKL
    have hsolv : Group.IsSolvable (↥K ⧸ L.subgroupOf K) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
      have hnil : Group.IsNilpotent (Q.subgroupOf K) := hQ'.isNilpotent
      have hsol : Group.IsSolvable (Q.subgroupOf K) := inferInstance
      let f : Q.subgroupOf K →* ↥K ⧸ L.subgroupOf K :=
        (QuotientGroup.mk' (L.subgroupOf K)).comp (Q.subgroupOf K).subtype
      have hf : Function.Surjective f := by
        intro y
        obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf K) y
        have hx' : x ∈ ((L ⊔ Q : Subgroup G) : Set G) := hK ▸ hx
        rw [hmul] at hx'
        obtain ⟨l, hl, q, hq, rfl⟩ := hx'
        refine ⟨⟨⟨q, hQK hq⟩, ?_⟩, ?_⟩
        · exact hq
        · simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype]
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have hqK : q ∈ K := hQK hq
          have := (Subgroup.mem_normalizer_iff.mp (hKL (K.inv_mem hqK)) l).mp hl
          simpa [mul_assoc] using this
      exact Group.isSolvable_of_surjective hf
    have htop := eq_top_of_perfect_of_solvable_quotient hperf (L.subgroupOf K) hsolv
    refine le_antisymm hLK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ L.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
    exact this
  · exfalso
    exact no_index_two hperf ((K ⊓ Subgroup.normalizer (L : Set G)).subgroupOf K) h2

end CFSG.QuasithinUnique.A5.G3
