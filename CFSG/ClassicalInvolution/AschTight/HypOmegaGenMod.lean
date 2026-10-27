module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_isPerfect_of_not_dvd_index {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    {N : Subgroup L} [N.Normal] (hN : ¬ 2 ∣ N.index) : N = ⊤ := by
  have hodd : Odd (Nat.card (L ⧸ N)) := by
    change Odd N.index
    rw [Nat.odd_iff]
    omega
  have hsol : Group.IsSolvable (L ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_contra hne
  have h1 : N.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hnt : Nontrivial (L ⧸ N) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    change 1 < N.index
    have := N.index_ne_zero_of_finite
    omega
  exact Group.IsPerfect.not_isSolvable (L ⧸ N) hsol

theorem closure_twoElements_eq {K : Subgroup G} [Group.IsPerfect K] :
    Subgroup.closure {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.closure {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} with hN
  have hNK : N ≤ K := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hconj : ∀ g ∈ K, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨K.mul_mem (K.mul_mem hg hx.1) (K.inv_mem hg), ?_⟩
      obtain ⟨n, hn⟩ := hx.2.exists_card_eq
      refine IsPGroup.of_card (n := n) ?_
      have hord : orderOf (g * x * g⁻¹) = orderOf x := by
        simpa [MulAut.conj_apply] using
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      rw [Nat.card_zpowers, hord, ← Nat.card_zpowers, hn]
    | one => simp [N.one_mem]
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact N.mul_mem ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact N.inv_mem ha
  have hnormal : (N.subgroupOf K).Normal := ⟨fun n hn g => by
    have := hconj g g.2 n hn
    exact Subgroup.mem_subgroupOf.mpr this⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hQN : (Q : Subgroup ↥K) ≤ N.subgroupOf K := by
    intro q hq
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨q.2, ?_⟩)
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp Q.isPGroup' ⟨q, hq⟩
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ← Subgroup.orderOf_mk q hq, hn]
  have hodd : ¬ 2 ∣ (N.subgroupOf K).index := fun h =>
    Q.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hQN))
  have htop := eq_top_of_isPerfect_of_not_dvd_index hodd
  exact le_antisymm hNK (Subgroup.subgroupOf_eq_top.mp htop)

variable {p f : ℕ} [Fact p.Prime]

theorem natCard_eq_of_isSylow2In_of_isClassicalMember {K P : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) (hP : IsSylow2In P K) :
    Nat.card P = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hK.nonempty_equiv
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨J, hJ, hRJ, hR2, hmax⟩ :=
    mem_RSet_iff.mp (show Q.map K.subtype ∈ RSet ({K} : Set (Subgroup G)) from ⟨K, rfl, Q, rfl⟩)
  rw [Set.mem_singleton_iff] at hJ
  subst hJ
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥J)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥J
  rw [hP.natCard_eq ⟨hRJ, hR2, hmax⟩, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    Sylow.card_eq_multiplicity, Subgroup.card_eq_card_quotient_mul_card_subgroup
      (classicalInvolutionOddCore ↥J), Nat.card_congr e.toEquiv,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]

theorem hypOmegaGen_of_mod (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (h : HypOmegaMod p f Ω) : HypOmegaGen Ω where
  conjInvariant := h.conjInvariant
  omega1 K hK := by
    obtain ⟨z, hz⟩ := h.classical K hK
    refine ⟨⟨z, ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz⟩, ?_⟩
    obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
    have hR : Q.map K.subtype ∈ RSet (CoreAssembly.conjClass K) :=
      ⟨K, CoreAssembly.mem_conjClass_self K, Q, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := (exists_ne_comm_of_mem_rSet hp hq hz hR).1
    obtain ⟨J, hJ, hRJ, hR2, hmax⟩ :=
      mem_RSet_iff.mp (show Q.map K.subtype ∈ RSet ({K} : Set (Subgroup G)) from ⟨K, rfl, Q, rfl⟩)
    rw [Set.mem_singleton_iff] at hJ
    subst hJ
    refine ⟨Q.map J.subtype, ⟨hRJ, hR2, hmax⟩, fun hc => hxy ?_⟩
    exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  omega2 K hK := by
    obtain ⟨z, hz⟩ := h.classical K hK
    have := hz.perfect
    exact Or.inl closure_twoElements_eq
  omega3 K hK J hJ P Q hP hQ := by
    obtain ⟨z, hz⟩ := h.classical K hK
    obtain ⟨t, ht⟩ := h.classical J hJ
    rw [natCard_eq_of_isSylow2In_of_isClassicalMember hz hP,
      natCard_eq_of_isSylow2In_of_isClassicalMember ht hQ]
  omega4 := h.omega4
  omega5 := h.omega5

end CFSG.ClassicalInvolution.Disconnected.AschTight
