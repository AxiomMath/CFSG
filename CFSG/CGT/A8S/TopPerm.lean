module

public import CFSG.CGT.A8S.Words
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.A8S

open Equiv Equiv.Perm

namespace Perm8

theorem map_subtype_centralizer {G : Type*} [Group G] (K : Subgroup G) (x : K) :
    (Subgroup.centralizer {x}).map K.subtype = K ⊓ Subgroup.centralizer {(x : G)} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val hy⟩
  · rintro ⟨hyK, hy⟩
    exact ⟨⟨y, hyK⟩, Subtype.ext hy, rfl⟩

theorem card_centralizer_subtype {G : Type*} [Group G] (K : Subgroup G) (x : K) :
    Nat.card (Subgroup.centralizer {x}) = Nat.card ↥(K ⊓ Subgroup.centralizer {(x : G)}) := by
  rw [← map_subtype_centralizer, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nat.card (Subgroup.centralizer {a}) = Nat.card (Subgroup.centralizer {e a}) := by
  have h : (Subgroup.centralizer {a}).map e.toMonoidHom = Subgroup.centralizer {e a} := by
    ext b
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hb
      have h1 := congrArg e hb
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    · intro hb
      apply e.injective
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply]
  rw [← h, Subgroup.card_map_of_injective e.injective]

theorem cycleType_eq_replicate {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    ∃ k, σ.cycleType = Multiset.replicate k 2 ∧ 1 ≤ k ∧ k ≤ 4 := by
  have ho : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  refine ⟨n + 1, hn, by omega, ?_⟩
  have hle := sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hle
  omega

theorem even_of_sign_eq_one {σ : Perm (Fin 8)} {k : ℕ}
    (hk : σ.cycleType = Multiset.replicate k 2) (hs : sign σ = 1) : Even k := by
  rw [sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hs
  rcases Nat.even_or_odd k with he | ho
  · exact he
  · exfalso
    have hodd : Odd (k * 2 + k) := by
      rw [Nat.odd_iff] at ho ⊢
      omega
    rw [hodd.neg_one_pow] at hs
    exact absurd hs (by decide)

theorem card_centralizer_perm {σ : Perm (Fin 8)} {k : ℕ}
    (hk : σ.cycleType = Multiset.replicate k 2) (hk1 : k ≠ 0) :
    Nat.card (Subgroup.centralizer {σ}) = (8 - k * 2).factorial * 2 ^ k * k.factorial := by
  rw [nat_card_centralizer, hk, Multiset.sum_replicate, Multiset.prod_replicate,
    Multiset.toFinset_replicate, ite_eq_right hk1, Finset.prod_singleton,
    Multiset.count_replicate_self, Fintype.card_fin, smul_eq_mul]

theorem not_centralizer_le_alternatingGroup {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    ¬ Subgroup.centralizer {σ} ≤ alternatingGroup (Fin 8) := by
  intro h
  obtain ⟨k, hk, hk1, -⟩ := cycleType_eq_replicate h2 h1
  have h2mem : 2 ∈ σ.cycleType := by
    rw [hk]
    exact Multiset.mem_replicate.2 ⟨by omega, rfl⟩
  exact absurd (OnCycleFactors.odd_of_centralizer_le_alternatingGroup h 2 h2mem) (by decide)

theorem relIndex_alternatingGroup_centralizer {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) : (alternatingGroup (Fin 8)).relIndex (Subgroup.centralizer {σ}) = 2 := by
  have hd : (alternatingGroup (Fin 8)).relIndex (Subgroup.centralizer {σ}) ∣ 2 := by
    rw [← alternatingGroup.index_eq_two (α := Fin 8)]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact absurd (Subgroup.relIndex_eq_one.1 h) (not_centralizer_le_alternatingGroup h2 h1)
  · exact h

theorem two_mul_card_centralizer {σ : alternatingGroup (Fin 8)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    2 * Nat.card (Subgroup.centralizer {σ}) =
      Nat.card (Subgroup.centralizer {(σ : Perm (Fin 8))}) := by
  have h2' : (σ : Perm (Fin 8)) ^ 2 = 1 := by rw [← Subgroup.coe_pow, h2]; rfl
  have h1' : (σ : Perm (Fin 8)) ≠ 1 := fun h => h1 (Subtype.ext h)
  rw [card_centralizer_subtype, ← relIndex_alternatingGroup_centralizer h2' h1',
    Subgroup.relIndex_mul_card]

theorem ninetySix_le_card_centralizer {σ : alternatingGroup (Fin 8)} (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) : 96 ≤ Nat.card (Subgroup.centralizer {σ}) := by
  have h2' : (σ : Perm (Fin 8)) ^ 2 = 1 := by rw [← Subgroup.coe_pow, h2]; rfl
  have h1' : (σ : Perm (Fin 8)) ≠ 1 := fun h => h1 (Subtype.ext h)
  obtain ⟨k, hk, hk1, hk4⟩ := cycleType_eq_replicate h2' h1'
  obtain ⟨j, rfl⟩ := even_of_sign_eq_one hk σ.2
  have hc := two_mul_card_centralizer h2 h1
  rw [card_centralizer_perm hk (by omega)] at hc
  have hj : j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl
  · norm_num [Nat.factorial] at hc
    omega
  · norm_num [Nat.factorial] at hc
    omega

theorem card_centralizer_eq_of_forall_ne {σ : alternatingGroup (Fin 8)} (h2 : σ ^ 2 = 1)
    (hσ : ∀ i, (σ : Perm (Fin 8)) i ≠ i) : Nat.card (Subgroup.centralizer {σ}) = 192 := by
  have h2' : (σ : Perm (Fin 8)) ^ 2 = 1 := by rw [← Subgroup.coe_pow, h2]; rfl
  have h1' : (σ : Perm (Fin 8)) ≠ 1 := fun h => hσ 0 (by rw [h]; rfl)
  have h1 : σ ≠ 1 := fun h => h1' (by rw [h]; rfl)
  obtain ⟨k, hk, -, -⟩ := cycleType_eq_replicate h2' h1'
  have hsupp : (σ : Perm (Fin 8)).support = Finset.univ :=
    Finset.eq_univ_of_forall fun i => mem_support.2 (hσ i)
  have hsum := sum_cycleType (σ : Perm (Fin 8))
  rw [hk, hsupp, Multiset.sum_replicate, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  obtain rfl : k = 4 := by omega
  have hc := two_mul_card_centralizer h2 h1
  rw [card_centralizer_perm hk (by norm_num)] at hc
  norm_num [Nat.factorial] at hc
  omega

theorem card_fixedPoints_eq_four {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1)
    (hs : sign σ = 1) {i : Fin 8} (hi : σ i = i) :
    Fintype.card (Function.fixedPoints σ) = 4 := by
  obtain ⟨k, hk, hk1, hk4⟩ := cycleType_eq_replicate h2 h1
  obtain ⟨j, rfl⟩ := even_of_sign_eq_one hk hs
  have hlt : σ.support.card < 8 := by
    have := Finset.card_lt_univ_of_notMem (s := σ.support) (x := i) (by
      rw [mem_support, not_not]; exact hi)
    rwa [Fintype.card_fin] at this
  rw [← sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul] at hlt
  rw [card_fixedPoints, hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin]
  omega

theorem exists_forall_ne_of_card_eq_eight {E : Subgroup (alternatingGroup (Fin 8))}
    (hE : Nat.card E = 8) (h2 : ∀ e ∈ E, e ^ 2 = 1) :
    ∃ e ∈ E, ∀ i, ((e : alternatingGroup (Fin 8)) : Perm (Fin 8)) i ≠ i := by
  classical
  by_contra hne'
  have hne : ∀ e ∈ E, ∃ i, ((e : alternatingGroup (Fin 8)) : Perm (Fin 8)) i = i :=
    fun e he => by_contra fun h => hne' ⟨e, he, fun i hi => h ⟨i, hi⟩⟩
  have hEcard : Fintype.card E = 8 := by rw [← Nat.card_eq_fintype_card, hE]
  have hfix : ∀ e : E, e ≠ 1 → Fintype.card (MulAction.fixedBy (Fin 8) e) = 4 := by
    intro e he
    have he2 : ((e : alternatingGroup (Fin 8)) : Perm (Fin 8)) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, h2 _ e.2]; rfl
    have he1 : ((e : alternatingGroup (Fin 8)) : Perm (Fin 8)) ≠ 1 := fun h =>
      he (Subtype.ext (Subtype.ext h))
    obtain ⟨i, hi⟩ := hne _ e.2
    rw [← card_fixedPoints_eq_four he2 he1 (e : alternatingGroup (Fin 8)).2 hi]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hfix1 : Fintype.card (MulAction.fixedBy (Fin 8) (1 : E)) = 8 := by
    have h := Fintype.card_congr (Equiv.subtypeUnivEquiv
      (p := fun x : Fin 8 => x ∈ MulAction.fixedBy (Fin 8) (1 : E)) fun x => one_smul E x)
    rwa [Fintype.card_fin] at h
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group E (Fin 8)
  rw [Fintype.sum_eq_add_sum_compl 1, hfix1,
    Finset.sum_congr rfl (fun e he => hfix e (by simpa using he)), Finset.sum_const,
    Finset.card_compl, Finset.card_singleton, hEcard, smul_eq_mul] at hB
  omega

theorem cycleType_eq_of_forall_ne {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1) (hσ : ∀ i, σ i ≠ i) :
    σ.cycleType = Multiset.replicate 4 2 := by
  have h1 : σ ≠ 1 := fun h => hσ 0 (by rw [h]; rfl)
  obtain ⟨k, hk, -, -⟩ := cycleType_eq_replicate h2 h1
  have hsupp : σ.support = Finset.univ := Finset.eq_univ_of_forall fun i => mem_support.2 (hσ i)
  have hsum := sum_cycleType σ
  rw [hk, hsupp, Multiset.sum_replicate, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  obtain rfl : k = 4 := by omega
  exact hk

theorem exists_conj_eq_of_forall_ne {σ τ : alternatingGroup (Fin 8)} (hσ2 : σ ^ 2 = 1)
    (hσ : ∀ i, (σ : Perm (Fin 8)) i ≠ i) (hτ2 : τ ^ 2 = 1)
    (hτ : ∀ i, (τ : Perm (Fin 8)) i ≠ i) : ∃ π : alternatingGroup (Fin 8), π * τ * π⁻¹ = σ := by
  have hσ2' : (σ : Perm (Fin 8)) ^ 2 = 1 := by rw [← Subgroup.coe_pow, hσ2]; rfl
  have hτ2' : (τ : Perm (Fin 8)) ^ 2 = 1 := by rw [← Subgroup.coe_pow, hτ2]; rfl
  have hτ1 : (τ : Perm (Fin 8)) ≠ 1 := fun h => hτ 0 (by rw [h]; rfl)
  have hc : IsConj (τ : Perm (Fin 8)) (σ : Perm (Fin 8)) := by
    rw [isConj_iff_cycleType_eq, cycleType_eq_of_forall_ne hσ2' hσ,
      cycleType_eq_of_forall_ne hτ2' hτ]
  obtain ⟨π₀, hπ₀⟩ := isConj_iff.1 hc
  have key : ∀ π : Perm (Fin 8), sign π = 1 → π * τ * π⁻¹ = σ →
      ∃ π : alternatingGroup (Fin 8), π * τ * π⁻¹ = σ := fun π hs hπ =>
    ⟨⟨π, mem_alternatingGroup.2 hs⟩, Subtype.ext (by simpa using hπ)⟩
  rcases Int.units_eq_one_or (sign π₀) with hs | hs
  · exact key π₀ hs hπ₀
  · obtain ⟨ρ, hρC, hρA⟩ := Set.not_subset.1 (not_centralizer_le_alternatingGroup hτ2' hτ1)
    have hρs : sign ρ = -1 := (Int.units_eq_one_or (sign ρ)).resolve_left hρA
    have hρτ : ρ * τ = τ * ρ := Subgroup.mem_centralizer_singleton_iff.1 hρC
    refine key (π₀ * ρ) (by rw [map_mul, hs, hρs]; rfl) ?_
    calc π₀ * ρ * τ * (π₀ * ρ)⁻¹ = π₀ * (ρ * τ) * ρ⁻¹ * π₀⁻¹ := by group
      _ = σ := by rw [hρτ, ← hπ₀]; group

end Perm8

end CFSG.CGT.A8S
