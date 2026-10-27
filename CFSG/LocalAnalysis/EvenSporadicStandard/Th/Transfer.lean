module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Basic
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G] [Finite G]

theorem inv_mul_mem_of_cyclic {P Q : Subgroup G} (hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q) {u v : G} (huP : u ∈ P) (hvP : v ∈ P)
    (huQ : u ∉ Q) (hvQ : v ∉ Q) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) : u⁻¹ * v ∈ Q := by
  have hn : (Q.subgroupOf P).Normal := ⟨fun n hn g => hQn g g.2 n hn⟩
  set φ := QuotientGroup.mk' (Q.subgroupOf P) with hφ
  obtain ⟨b, hbP, hb⟩ := hcyc
  have hcy : IsCyclic (↥P ⧸ Q.subgroupOf P) := by
    refine ⟨φ ⟨b, hbP⟩, fun x => ?_⟩
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf P) x
    obtain ⟨k, hk⟩ := hb t t.2
    refine ⟨k, ?_⟩
    show φ ⟨b, hbP⟩ ^ k = φ t
    rw [← map_zpow, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hk
  have hord : ∀ y : G, ∀ hy : y ∈ P, y ∉ Q → y ^ 2 = 1 → orderOf (φ ⟨y, hy⟩) = 2 := by
    intro y hy hyQ hy2
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      rw [show (⟨y, hy⟩ : ↥P) ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow, hy2]; rfl),
        map_one]
    · intro h
      apply hyQ
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact h
  have hu := hord u huP huQ hu2
  have hv := hord v hvP hvQ hv2
  have heq : zpowers (φ ⟨u, huP⟩) = zpowers (φ ⟨v, hvP⟩) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hu, hv]
  have hmem : φ ⟨v, hvP⟩ ∈ zpowers (φ ⟨u, huP⟩) := heq ▸ mem_zpowers _
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hu hmem with h | h
  · exact absurd h (fun h1 => by rw [h1, orderOf_one] at hv; exact absurd hv (by norm_num))
  · have h1 : φ (⟨u, huP⟩⁻¹ * ⟨v, hvP⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1

theorem exists_normal_index_two_of_cyclic_quotient {N : Subgroup G} [N.Normal]
    (hp : IsPGroup 2 (G ⧸ N)) {u : G} (huN : u ∉ N) :
    ∃ M : Subgroup G, M.Normal ∧ M.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (G ⧸ N) := hp.isNilpotent
  have hbt : (⊥ : Subgroup (G ⧸ N)) ≠ ⊤ := by
    intro h
    apply huN
    have h1 : (QuotientGroup.mk u : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := by
      rw [h]
      exact Subgroup.mem_top _
    exact (QuotientGroup.eq_one_iff u).1 (Subgroup.mem_bot.1 h1)
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ N))).resolve_left hbt
  have hMidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hp).1 hM
  refine ⟨M.comap (QuotientGroup.mk' N), (Subgroup.normal_of_index_eq_two hMidx).comap _, ?_⟩
  exact (Subgroup.index_comap_of_surjective M (f := QuotientGroup.mk' N)
    QuotientGroup.mk_surjective).trans hMidx

theorem exists_extremal_conj_of_cyclic
    (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    {P Q : Subgroup G} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index)
    (hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q)
    {u : G} (huP : u ∈ P) (huQ : u ∉ Q) (hu2 : u ^ 2 = 1) :
    ∃ g : G, g⁻¹ * u * g ∈ Q ∧ IsExtremalIn 2 P (g⁻¹ * u * g) ∧
      ∀ c ∈ P ⊓ centralizer {u}, g⁻¹ * c * g ∈ P ⊓ centralizer {g⁻¹ * u * g} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ P → g⁻¹ * u ^ (2 * k) * g ∈ Q := by
    intro g k _
    rw [pow_mul, hu2, one_pow, mul_one, inv_mul_cancel]
    exact one_mem _
  have hc : ∀ g : G, g⁻¹ * u * g ∈ P → IsExtremalIn 2 P (g⁻¹ * u * g) →
      g⁻¹ * u * g ∈ Q ∨ u⁻¹ * (g⁻¹ * u * g) ∈ Q := by
    intro g hg _
    by_cases hgQ : g⁻¹ * u * g ∈ Q
    · exact Or.inl hgQ
    · right
      have hv2 : (g⁻¹ * u * g) ^ 2 = 1 := by
        rw [sq, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, ← sq, hu2]
        group
      exact inv_mul_mem_of_cyclic hQn hcyc huP hg huQ hgQ hu2 hv2
  rcases thompson_transfer_1515 hP hPidx hQn hcyc huP huQ hb hc with ⟨N, hN, -, hp, huN⟩ | h
  · exact absurd (exists_normal_index_two_of_cyclic_quotient hp huN) hG
  · exact h

theorem eq_of_inf_normalizer_le {p : ℕ} [Fact p.Prime] {P S : Subgroup G} (hP : IsPGroup p P)
    (hSP : S ≤ P) (h : ∀ x ∈ P, x ∈ normalizer (S : Set G) → x ∈ S) : S = P := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  have hnorm : normalizer ((S.subgroupOf P : Subgroup ↥P) : Set ↥P) = S.subgroupOf P := by
    refine le_antisymm (fun x hx => ?_) (le_normalizer)
    rw [mem_subgroupOf]
    refine h x x.2 (mem_normalizer_iff.2 fun s => ?_)
    constructor
    · intro hs
      have := (mem_normalizer_iff.1 hx ⟨s, hSP hs⟩).1 (by rw [mem_subgroupOf]; exact hs)
      rwa [mem_subgroupOf] at this
    · intro hs
      have hsP : s ∈ P := by
        have := hSP hs
        have h2 : x⁻¹ * (x * s * x⁻¹) * x ∈ P := P.mul_mem (P.mul_mem (P.inv_mem x.2) this) x.2
        simpa [mul_assoc] using h2
      have := (mem_normalizer_iff.1 hx ⟨s, hsP⟩).2 (by rw [mem_subgroupOf]; exact hs)
      rwa [mem_subgroupOf] at this
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.1 hnc) _ hnorm
  refine le_antisymm hSP (fun x hx => ?_)
  have : (⟨x, hx⟩ : ↥P) ∈ S.subgroupOf P := by rw [htop]; exact mem_top _
  exact this

end CFSG.EvenSporadicStandard.ThStd
