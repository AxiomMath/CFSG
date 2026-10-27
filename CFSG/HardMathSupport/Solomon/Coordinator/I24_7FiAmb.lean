module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiCoverData
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem fi_elemAbelian_closure {G : Type*} [Group G] {S : Set G}
    (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (h3 : ∀ a ∈ S, a ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.closure S) := by
  have h1 : ∀ a ∈ Subgroup.closure S, ∀ s ∈ S, a * s = s * a := by
    intro a ha s hs
    have : Subgroup.closure S ≤ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (hc s hs x hx).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (this ha)
  have hab : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    have : Subgroup.closure S ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (h1 a ha x hx).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (this hb)).symm
  refine ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h3 y hy
  | one => exact one_pow 3
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (hab a ha b hb) 3, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem fi_normalizer_closure {G : Type*} [Group G] {S : Set G} {n : G}
    (h1 : ∀ s ∈ S, n * s * n⁻¹ ∈ Subgroup.closure S)
    (h2 : ∀ s ∈ S, n⁻¹ * s * n ∈ Subgroup.closure S) :
    n ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have hf : ∀ x ∈ Subgroup.closure S, n * x * n⁻¹ ∈ Subgroup.closure S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact h1 y hy
    | one => simp
    | mul a b ha hb iha ihb =>
      have := (Subgroup.closure S).mul_mem iha ihb
      rwa [show n * a * n⁻¹ * (n * b * n⁻¹) = n * (a * b) * n⁻¹ by group] at this
    | inv a ha iha =>
      have := (Subgroup.closure S).inv_mem iha
      rwa [show (n * a * n⁻¹)⁻¹ = n * a⁻¹ * n⁻¹ by group] at this
  have hb : ∀ x ∈ Subgroup.closure S, n⁻¹ * x * n ∈ Subgroup.closure S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact h2 y hy
    | one => simp
    | mul a b ha hb iha ihb =>
      have := (Subgroup.closure S).mul_mem iha ihb
      rwa [show n⁻¹ * a * n * (n⁻¹ * b * n) = n⁻¹ * (a * b) * n by group] at this
    | inv a ha iha =>
      have := (Subgroup.closure S).inv_mem iha
      rwa [show (n⁻¹ * a * n)⁻¹ = n⁻¹ * a⁻¹ * n by group] at this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hf h hh, fun hh => ?_⟩
  have := hb _ hh
  rwa [show n⁻¹ * (n * h * n⁻¹) * n = h by group] at this

variable {G : Type*} [Group G] [Finite G]

theorem fi22CoverData_of_ambient (M P0 E5 Q4 : Subgroup G) (n5 n4 n4' : G) (hP0M : P0 ≤ M)
    (hP0 : IsPGroup 3 P0) (hP0c : Nat.card P0 = 3 ^ (Nat.card M).factorization 3)
    (hE5 : E5 ≤ P0) (he5 : IsElemAbelian 3 E5) (hc5 : Nat.card E5 = 3 ^ 5)
    (hQ4 : Q4 ≤ P0) (hq4 : IsElemAbelian 3 Q4) (hc4 : Nat.card Q4 = 3 ^ 4)
    (h5M : n5 ∈ M) (h4M : n4 ∈ M) (h4'M : n4' ∈ M)
    (hn5 : n5 ∈ Subgroup.normalizer (E5 : Set G)) (hn4 : n4 ∈ Subgroup.normalizer (Q4 : Set G))
    (hn4' : n4' ∈ Subgroup.normalizer (Q4 : Set G))
    (hgen : Subgroup.closure ({n5, n4, n4'} : Set G) = M) : Fi22CoverData ↥M := by
  have hcardOf : ∀ {H : Subgroup G}, H ≤ M → Nat.card (H.subgroupOf M) = Nat.card H :=
    fun {H} hH => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hea : ∀ {H : Subgroup G}, IsElemAbelian 3 H → IsElemAbelian 3 (H.subgroupOf M) := by
    intro H hH
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · exact fi_comm_of_elemAbelian hH (Subgroup.mem_subgroupOf.1 a.2)
        (Subgroup.mem_subgroupOf.1 b.2)
    · exact Subtype.ext (hH.2 _ (Subgroup.mem_subgroupOf.1 hx))
  have hnorm : ∀ {H : Subgroup G} {n : G} (hn : n ∈ M),
      n ∈ Subgroup.normalizer (H : Set G) →
        (⟨n, hn⟩ : ↥M) ∈ Subgroup.normalizer ((H.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro H n hn hnH
    rw [Subgroup.mem_normalizer_iff] at hnH ⊢
    intro h
    exact hnH (h : G)
  refine ⟨P0.subgroupOf M, E5.subgroupOf M, Q4.subgroupOf M, ⟨n5, h5M⟩, ⟨n4, h4M⟩, ⟨n4', h4'M⟩,
    ?_, ?_, ?_, hea he5, ?_, ?_, hea hq4, ?_, hnorm h5M hn5, hnorm h4M hn4, hnorm h4'M hn4', ?_⟩
  · obtain ⟨k, hk⟩ := hP0.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [hcardOf hP0M, hk])
  · rw [hcardOf hP0M, hP0c]
  · exact fun x hx => Subgroup.mem_subgroupOf.2 (hE5 (Subgroup.mem_subgroupOf.1 hx))
  · rw [hcardOf (hE5.trans hP0M), hc5]
  · exact fun x hx => Subgroup.mem_subgroupOf.2 (hQ4 (Subgroup.mem_subgroupOf.1 hx))
  · rw [hcardOf (hQ4.trans hP0M), hc4]
  · apply Subgroup.map_injective M.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have : M.subtype '' ({⟨n5, h5M⟩, ⟨n4, h4M⟩, ⟨n4', h4'M⟩} : Set ↥M) = {n5, n4, n4'} := by
      simp [Set.image_insert_eq]
    rw [this, hgen]

end CFSG.HardMathSupport.Solomon.Coordinator
