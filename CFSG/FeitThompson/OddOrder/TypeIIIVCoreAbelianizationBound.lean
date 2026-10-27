module

public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.OddOrder.FreeActionKernelCongruence
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.FixedOrderMultiplicativityNormal
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

theorem two_mul_le_sub_one_of_odd {a e : ℕ} (ha : Odd a) (he : Odd e) (h1 : 1 < a)
    (hdvd : e ∣ a - 1) : 2 * e ≤ a - 1 := by
  obtain ⟨t, ht⟩ := hdvd
  have heven : Even (a - 1) := Nat.Odd.sub_odd ha odd_one
  have ht2 : Even t := by
    rw [ht, Nat.even_mul] at heven
    exact heven.resolve_left (Nat.not_even_iff_odd.2 he)
  obtain ⟨s, hs⟩ := ht2
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · rw [hs] at ht; omega
    · exact h
  calc 2 * e = e * 2 := by ring
    _ ≤ e * (s + s) := Nat.mul_le_mul_left _ (by omega)
    _ = a - 1 := by rw [← hs, ← ht]

variable {A V : Type*} [Group A] [Group V]

theorem mulAut_zpow_apply_eq_self {X : Type*} [Group X] {f : MulAut X} {x : X} (h : f x = x)
    (n : ℤ) : (f ^ n) x = x := by
  have hs : f ∈ MulAction.stabilizer (MulAut X) x := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact h
  have h2 := zpow_mem hs n
  rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2
  exact h2

theorem natCard_dvd_natCard_sub_one_of_mulAut {X : Type*} [Group X] [Finite A] [Finite X]
    (ρ : A →* MulAut X) (h : ∀ x : X, x ≠ 1 → ∀ a : A, ρ a x = x → a = 1) :
    Nat.card A ∣ Nat.card X - 1 := by
  let _ : MulDistribMulAction A X := MulDistribMulAction.compHom X ρ
  exact card_dvd_card_sub_one_of_smul_eq_self A X h

theorem natCard_dvd_index_commutator_sub_one [Finite A] [Finite V] [Group.IsSolvable A]
    [Group.IsSolvable V] (ρ : A →* MulAut V) (hcop : (Nat.card A).Coprime (Nat.card V))
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : V, ρ a v = v → v ∈ commutator V) :
    Nat.card A ∣ (commutator V).index - 1 := by
  have hN : IsInvariantSubgroup ρ (commutator V) :=
    isInvariantSubgroup_iff_forall_map_eq.2 fun b => by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (ρ b).surjective]
  rw [Subgroup.index_eq_card]
  refine natCard_dvd_natCard_sub_one_of_mulAut hN.quotientAut ?_
  intro x hx a ha
  by_contra hone
  set B := Subgroup.zpowers a with hB
  have hfixall : ∀ b : ↥B, (hN.comp B.subtype).quotientAut b x = x := by
    intro b
    rw [hN.quotientAut_comp B.subtype]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    have hb : (B.subtype b : A) = a ^ n := hn.symm
    simp only [MonoidHom.comp_apply, hb, map_zpow]
    exact mulAut_zpow_apply_eq_self ha n
  obtain ⟨v, hv, hvx⟩ := exists_mem_fixedPoints_range_mk_eq (hN.comp B.subtype)
    (hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B)) hfixall
  have hva : ρ a v = v := by
    have h := (mem_fixedPoints_range_iff (ρ.comp B.subtype)).1 hv ⟨a, Subgroup.mem_zpowers a⟩
    simpa using h
  exact hx (hvx ▸ (QuotientGroup.eq_one_iff v).2 (hfree a hone v hva))

variable {G : Type*} [Group G] {M U W₁ W₂ : Subgroup G}

theorem relIndex_commutator_self_eq_natCard_abelianization (K : Subgroup G) :
    ⁅K, K⁆.relIndex K = Nat.card (Abelianization ↥K) := by
  rw [Subgroup.relIndex, ← commutator_eq_subgroupOf_commutator, Subgroup.index_eq_card]
  rfl

theorem relIndex_commutator_self_dvd_natCard (K : Subgroup G) :
    ⁅K, K⁆.relIndex K ∣ Nat.card K :=
  Subgroup.index_dvd_card _

theorem relIndex_commutator_self_le_natCard [Finite G] (K : Subgroup G) :
    ⁅K, K⁆.relIndex K ≤ Nat.card K :=
  Nat.le_of_dvd Nat.card_pos (relIndex_commutator_self_dvd_natCard K)

variable [Finite G]

namespace IsWitnessedPConfiguration

variable (hc : IsWitnessedPConfiguration M U W₁ W₂)

include hc

theorem ne_bot_commutator : (⁅M, M⁆ : Subgroup G) ≠ ⊥ := fun h =>
  hc.ne_bot_W₂ (le_bot_iff.1 ((hc.le_commutator_commutator_W₂.trans
    (Subgroup.commutator_le_self _)).trans h.le))

theorem le_normalizer_commutator_W₁ : W₁ ≤ normalizer ((⁅M, M⁆ : Subgroup G) : Set G) :=
  hc.le_M_W₁.trans (Subgroup.normalizer_commutator_ge_left M M)

omit hc in
theorem isSolvable_commutator [Group.IsSolvable ↥M] :
    Group.IsSolvable ↥(⁅M, M⁆ : Subgroup G) :=
  Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (Subgroup.commutator_le_self M))

theorem isSolvable_W₁ : Group.IsSolvable ↥W₁ :=
  Group.isSolvable_of_comm fun a b => hc.isCyclic_W₁.commGroup.mul_comm a b

theorem one_lt_relIndex_commutator_commutator [Group.IsSolvable ↥M] :
    1 < ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆.relIndex (⁅M, M⁆ : Subgroup G) := by
  have := isSolvable_commutator (M := M)
  have hnt : Nontrivial ↥(⁅M, M⁆ : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hc.ne_bot_commutator
  rw [Subgroup.relIndex, ← commutator_eq_subgroupOf_commutator]
  have h1 : (commutator ↥(⁅M, M⁆ : Subgroup G)).index ≠ 1 := fun h =>
    (Group.IsSolvable.commutator_lt_top_of_nontrivial
      ↥(⁅M, M⁆ : Subgroup G)).ne (Subgroup.index_eq_one.1 h)
  have h0 : (commutator ↥(⁅M, M⁆ : Subgroup G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem natCard_W₁_dvd_relIndex_sub_one [Group.IsSolvable ↥M] :
    Nat.card W₁ ∣
      ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆.relIndex (⁅M, M⁆ : Subgroup G) - 1 := by
  have := isSolvable_commutator (M := M)
  have := hc.isSolvable_W₁
  rw [Subgroup.relIndex, ← commutator_eq_subgroupOf_commutator]
  refine natCard_dvd_index_commutator_sub_one
    (conjOnNormalized (⁅M, M⁆ : Subgroup G) hc.le_normalizer_commutator_W₁)
    hc.coprime_natCard_W₁_natCard_commutator ?_
  intro w hw v hv
  have hw1 : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
  have hvc : (v : G) ∈ (⁅M, M⁆ : Subgroup G) ⊓ centralizer {(w : G)} := by
    refine Subgroup.mem_inf.2 ⟨v.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    have h2 := congrArg (fun z : ↥(⁅M, M⁆ : Subgroup G) => (z : G)) hv
    simp only [conjOnNormalized_apply_coe] at h2
    rw [hy]
    exact mul_inv_eq_iff_eq_mul.1 h2
  rw [hc.inf_centralizer_eq_W₂ _ w.2 hw1] at hvc
  rw [commutator_eq_subgroupOf_commutator, Subgroup.mem_subgroupOf]
  exact hc.le_commutator_commutator_W₂ hvc

theorem two_mul_natCard_W₁_le_relIndex_sub_one [Group.IsSolvable ↥M] (hodd : Odd (Nat.card G)) :
    2 * Nat.card W₁ ≤
      ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆.relIndex (⁅M, M⁆ : Subgroup G) - 1 := by
  refine two_mul_le_sub_one_of_odd (Odd.of_dvd_nat hodd ?_) (Odd.of_dvd_nat hodd ?_)
    hc.one_lt_relIndex_commutator_commutator hc.natCard_W₁_dvd_relIndex_sub_one
  · exact (relIndex_commutator_self_dvd_natCard _).trans
      (Subgroup.card_subgroup_dvd_card (⁅M, M⁆ : Subgroup G))
  · exact Subgroup.card_subgroup_dvd_card W₁

end IsWitnessedPConfiguration

theorem natCard_W₁_bound_of_isWitnessedPConfiguration {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (_hsimple : IsSimpleGroup G) (_hnonabelian : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {M U W₁ W₂ : Subgroup G}
    (hmax : IsCoatom M) (_htype : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆.relIndex (⁅M, M⁆ : Subgroup G) ∣
        Nat.card (⁅M, M⁆ : Subgroup G) ∧
      Nat.card W₁ ∣
        ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆.relIndex (⁅M, M⁆ : Subgroup G) - 1 ∧
      2 * Nat.card W₁ ≤
        ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆.relIndex (⁅M, M⁆ : Subgroup G) - 1 ∧
      ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆.relIndex (⁅M, M⁆ : Subgroup G) - 1 ≤
        Nat.card (⁅M, M⁆ : Subgroup G) - 1 := by
  have := hsolv M hmax.1
  refine ⟨relIndex_commutator_self_dvd_natCard _, hc.natCard_W₁_dvd_relIndex_sub_one,
    hc.two_mul_natCard_W₁_le_relIndex_sub_one hodd,
    Nat.sub_le_sub_right (relIndex_commutator_self_le_natCard _) 1⟩

end CFSG.FeitThompson
