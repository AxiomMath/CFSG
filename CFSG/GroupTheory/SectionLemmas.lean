module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement IsMulCommutative

lemma exists_maximal_invariant_lt {G : Type*} [Group G] [Finite G]
    {H N₀ P : Subgroup G} (hN₀P : N₀ ≤ P) (hlt : N₀ < P)
    (hHN₀ : H ≤ Subgroup.normalizer (N₀ : Set G)) :
    ∃ N : Subgroup G, N₀ ≤ N ∧ N < P ∧ H ≤ Subgroup.normalizer (N : Set G) ∧
      ∀ K : Subgroup G, N ≤ K → K ≤ P → H ≤ Subgroup.normalizer (K : Set G) →
        K = N ∨ K = P := by
  classical
  haveI hfinSub : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  let s : Set (Subgroup G) := {K | N₀ ≤ K ∧ K < P ∧ H ≤ Subgroup.normalizer (K : Set G)}
  have hs : s.Finite := Set.toFinite s
  obtain ⟨N, hN₀N, hNmax⟩ := hs.exists_le_maximal (a := N₀) ⟨le_rfl, hlt, hHN₀⟩
  refine ⟨N, hN₀N, hNmax.1.2.1, hNmax.1.2.2, ?_⟩
  intro K hNK hKP hHK
  by_cases hKeq : K = P
  · exact Or.inr hKeq
  · exact Or.inl (le_antisymm
      (hNmax.2 ⟨hN₀N.trans hNK, lt_of_le_of_ne hKP hKeq, hHK⟩ hNK) hNK)

theorem isElementaryAbelian_quotient_of_commutator_pow {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] {M N F : Subgroup G} [hN : (N.subgroupOf F).Normal]
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hexp : ∀ x ∈ M, x ^ p ∈ N) (hFM : F ≤ M) :
    IsElementaryAbelian p (↥F ⧸ N.subgroupOf F) := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, _root_.commutator_def,
      Subgroup.commutator_le]
    rintro x - y -
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hab (x : G) (hFM x.2) (y : G) (hFM y.2)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf F) z
    rw [← map_pow (QuotientGroup.mk' (N.subgroupOf F)) x p]
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf F) (x := x ^ p)).mpr (by
      rw [Subgroup.mem_subgroupOf]
      simpa using hexp (x : G) (hFM x.2))

theorem frattini_le_of_comm_pow {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (N : Subgroup P) (hc : ∀ x y : P, ⁅x, y⁆ ∈ N)
    (hpow : ∀ x : P, x ^ p ∈ N) : frattini P ≤ N := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
  refine (closure_le _).2 ?_
  rintro x (hx | ⟨y, rfl⟩)
  · exact (commutator_le.2 fun a _ b _ => hc a b : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ N) hx
  · exact hpow y

theorem relIndex_zpowers_dvd {p : ℕ} {P : Type*} [Group P] (F : Subgroup P) [F.Normal]
    (c : P) (hc : c ^ p ∈ F) : F.relIndex (Subgroup.zpowers c) ∣ p := by
  let N : Subgroup (Subgroup.zpowers c) := F.subgroupOf (Subgroup.zpowers c)
  let g : Subgroup.zpowers c := ⟨c, Subgroup.mem_zpowers c⟩
  have hgen : ∀ y : Subgroup.zpowers c ⧸ N,
      y ∈ Subgroup.zpowers (QuotientGroup.mk g : Subgroup.zpowers c ⧸ N) := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← QuotientGroup.mk_zpow]
    exact congrArg QuotientGroup.mk (Subtype.ext (by simpa [g] using hk))
  have h1 : Nat.card (Subgroup.zpowers c ⧸ N) =
      orderOf (QuotientGroup.mk g : Subgroup.zpowers c ⧸ N) :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).symm
  have h2 : (QuotientGroup.mk g : Subgroup.zpowers c ⧸ N) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hc
  change Nat.card (Subgroup.zpowers c ⧸ N) ∣ p
  rw [h1]
  exact orderOf_dvd_of_pow_eq_one h2

end CFSG.GroupTheory
