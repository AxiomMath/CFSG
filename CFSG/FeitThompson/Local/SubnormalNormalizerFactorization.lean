module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.IsSubnormal
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import CFSG.FeitThompson.Local.SubnormalConstrainedTransitivity
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {A P Q : Subgroup G} {q : ℕ}

theorem le_inf_normalizer_of_mem (hQ : Q ∈ maximalNormalizedPSubgroups P q) :
    P ≤ normalizer (P : Set G) ⊓ normalizer (Q : Set G) :=
  le_inf Subgroup.le_normalizer (le_normalizer_of_mem hQ)

variable [Finite G]

theorem constrainedCentralizerCore_le_normalizer (P : Subgroup G) :
    constrainedCentralizerCore P ≤ normalizer (P : Set G) :=
  (constrainedCentralizerCore_le_centralizer P).trans (centralizer_le_normalizer _)

theorem normal_subgroupOf_constrainedCentralizerCore (P : Subgroup G) :
    ((constrainedCentralizerCore P).subgroupOf (normalizer (P : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer (constrainedCentralizerCore_le_normalizer P)).2
    (normalizer_le_normalizer_constrainedCentralizerCore P)

theorem exists_mem_inf_mul_mem_constrainedCentralizerCore
    (htrans : ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
      ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) {n : G} (hn : n ∈ normalizer (P : Set G)) :
    ∃ l ∈ normalizer (P : Set G) ⊓ normalizer (Q : Set G), ∃ k ∈ constrainedCentralizerCore P,
      n = l * k := by
  have hQ' : (MulAut.conj n⁻¹ • Q : Subgroup G) ∈ maximalNormalizedPSubgroups P q :=
    smul_mem_maximalNormalizedPSubgroups
      (conj_smul_eq_self_iff_mem_normalizer.2 ((normalizer (P : Set G)).inv_mem hn)) hQ
  obtain ⟨c, hc, hceq⟩ := htrans Q hQ _ hQ'
  have hfix : (MulAut.conj (n * c⁻¹) • Q : Subgroup G) = Q :=
    calc (MulAut.conj (n * c⁻¹) • Q : Subgroup G)
        = MulAut.conj n • (MulAut.conj c⁻¹ • Q : Subgroup G) := by rw [map_mul, mul_smul]
      _ = MulAut.conj n • (MulAut.conj n⁻¹ • Q : Subgroup G) := by rw [hceq]
      _ = Q := by rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  refine ⟨n * c⁻¹, Subgroup.mem_inf.2 ⟨mul_mem hn (inv_mem (constrainedCentralizerCore_le_normalizer
    P hc)), conj_smul_eq_self_iff_mem_normalizer.1 hfix⟩, c, hc, by group⟩

theorem coe_inf_mul_coe_constrainedCentralizerCore
    (htrans : ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
      ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) :
    ((normalizer (P : Set G) ⊓ normalizer (Q : Set G) : Subgroup G) : Set G) *
        (constrainedCentralizerCore P : Set G) = (normalizer (P : Set G) : Set G) := by
  refine Set.Subset.antisymm ?_ fun n hn => ?_
  · rintro x ⟨l, hl, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_inf.1 hl).1 (constrainedCentralizerCore_le_normalizer P hk)
  · obtain ⟨l, hl, k, hk, rfl⟩ := exists_mem_inf_mul_mem_constrainedCentralizerCore htrans hQ hn
    exact ⟨l, hl, k, hk, rfl⟩

theorem coe_constrainedCentralizerCore_mul_coe_inf
    (htrans : ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
      ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) :
    (constrainedCentralizerCore P : Set G) *
        ((normalizer (P : Set G) ⊓ normalizer (Q : Set G) : Subgroup G) : Set G) =
      (normalizer (P : Set G) : Set G) := by
  refine Set.Subset.antisymm ?_ fun n hn => ?_
  · rintro x ⟨k, hk, l, hl, rfl⟩
    exact mul_mem (constrainedCentralizerCore_le_normalizer P hk) (Subgroup.mem_inf.1 hl).1
  · obtain ⟨l, hl, k, hk, rfl⟩ := exists_mem_inf_mul_mem_constrainedCentralizerCore htrans hQ hn
    have hlN : l ∈ normalizer (P : Set G) := (Subgroup.mem_inf.1 hl).1
    refine ⟨l * k * l⁻¹, (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_constrainedCentralizerCore P hlN) k).1 hk, l, hl, by group⟩

theorem sup_constrainedCentralizerCore_inf_eq_normalizer
    (htrans : ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
      ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) :
    constrainedCentralizerCore P ⊔ (normalizer (P : Set G) ⊓ normalizer (Q : Set G)) =
      normalizer (P : Set G) := by
  refine le_antisymm (sup_le (constrainedCentralizerCore_le_normalizer P) inf_le_left)
    fun n hn => ?_
  obtain ⟨l, hl, k, hk, rfl⟩ := exists_mem_inf_mul_mem_constrainedCentralizerCore htrans hQ hn
  exact mul_mem (Subgroup.mem_sup_right hl) (Subgroup.mem_sup_left hk)

theorem inf_commutator_normalizer_le_commutator_inf
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P)
    (hcompl : subgroupPrimeSupportCompl P = subgroupPrimeSupportCompl A)
    (htrans : ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
      ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) :
    P ⊓ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ ≤
      ⁅normalizer (P : Set G) ⊓ normalizer (Q : Set G),
        normalizer (P : Set G) ⊓ normalizer (Q : Set G)⁆ := by
  set N : Subgroup G := normalizer (P : Set G) with hN
  set L : Subgroup G := N ⊓ normalizer (Q : Set G) with hL
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hLN : L ≤ N := inf_le_left
  have hKN : constrainedCentralizerCore P ≤ N := constrainedCentralizerCore_le_normalizer P
  have hPπ : IsPiSubgroup (subgroupPrimeSupport A) (P.subgroupOf N) := by
    rw [← isPiSubgroup_map_subtype_iff, Subgroup.map_subgroupOf_eq_of_le hPN]; exact hP
  have hKnormal : ((constrainedCentralizerCore P).subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKN).2
      (normalizer_le_normalizer_constrainedCentralizerCore P)
  have hKπ : ∀ p ∈ (Nat.card ((constrainedCentralizerCore P).subgroupOf N)).primeFactors,
      p ∉ subgroupPrimeSupport A := by
    intro p hp
    have hcard : Nat.card ((constrainedCentralizerCore P).subgroupOf N) =
        Nat.card (constrainedCentralizerCore P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
    rw [hcard] at hp
    have h2 := isPiSubgroup_iff.1 (isPiSubgroup_constrainedCentralizerCore P) p hp
    rw [hcompl] at h2
    exact (mem_subgroupPrimeSupportCompl_iff.1 h2).2
  have hPL : P.subgroupOf N ≤ L.subgroupOf N := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
      ⟨x.2, le_normalizer_of_mem hQ (Subgroup.mem_subgroupOf.1 hx)⟩)
  have hprod : ((constrainedCentralizerCore P).subgroupOf N : Set ↥N) * (L.subgroupOf N : Set ↥N)
      = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨l, hl, k, hk, hx⟩ := exists_mem_inf_mul_mem_constrainedCentralizerCore htrans hQ x.2
    have hlN : l ∈ N := (Subgroup.mem_inf.1 hl).1
    have hklk : l * k * l⁻¹ ∈ constrainedCentralizerCore P :=
      (Subgroup.mem_normalizer_iff.1
        (normalizer_le_normalizer_constrainedCentralizerCore P hlN) k).1 hk
    refine ⟨⟨l * k * l⁻¹, mul_mem (mul_mem hlN (hKN hk)) (inv_mem hlN)⟩,
      Subgroup.mem_subgroupOf.2 hklk, ⟨l, hlN⟩, Subgroup.mem_subgroupOf.2 hl, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hx]; group
  have hkey := hPπ.inf_commutator_le_commutator hKnormal hKπ hprod hPL
  have hmap := Subgroup.map_mono (f := N.subtype) hkey
  rwa [Subgroup.map_inf _ _ _ N.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hPN,
    Subgroup.map_subtype_commutator, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hLN] at hmap

theorem inf_commutator_normalizer_le_commutator_normalizer
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P)
    (hcompl : subgroupPrimeSupportCompl P = subgroupPrimeSupportCompl A)
    (htrans : ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
      ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) :
    P ⊓ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ ≤
      ⁅normalizer (Q : Set G), normalizer (Q : Set G)⁆ :=
  (inf_commutator_normalizer_le_commutator_inf hP hcompl htrans hQ).trans
    (Subgroup.commutator_mono inf_le_right inf_le_right)

theorem normalizer_factorization_and_inf_commutator_le
    (hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P) (hPtop : P < ⊤)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hsn : (A.subgroupOf P).IsSubnormal)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) :
    (constrainedCentralizerCore P : Set G) *
          ((normalizer (P : Set G) ⊓ normalizer (Q : Set G) : Subgroup G) : Set G) =
        (normalizer (P : Set G) : Set G) ∧
      ((normalizer (P : Set G) ⊓ normalizer (Q : Set G) : Subgroup G) : Set G) *
          (constrainedCentralizerCore P : Set G) = (normalizer (P : Set G) : Set G) ∧
      P ⊓ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ ≤
        ⁅normalizer (Q : Set G), normalizer (Q : Set G)⁆ := by
  have htrans := (isConstrainedTransitive_of_isSubnormal hodd hsimple hG hsolv hAbot hAtop hcon
    hq hqπ hAP hPtop hP hsn hconj).2
  exact ⟨coe_constrainedCentralizerCore_mul_coe_inf htrans hQ,
    coe_inf_mul_coe_constrainedCentralizerCore htrans hQ,
    inf_commutator_normalizer_le_commutator_normalizer hP
      (subgroupPrimeSupportCompl_eq_of_isPiSubgroup hAP hP) htrans hQ⟩

end

end CFSG.FeitThompson
