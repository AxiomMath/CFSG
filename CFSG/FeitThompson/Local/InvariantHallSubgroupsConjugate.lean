module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

variable {X : Type*} [Group X] {π : Set ℕ} {K A H₁ H₂ : Subgroup X}

theorem mem_inf_centralizer_iff_forall_mul_comm {c : X} :
    c ∈ K ⊓ centralizer (A : Set X) ↔ c ∈ K ∧ ∀ a ∈ A, c * a = a * c := by
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  exact and_congr_right fun _ => ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩

theorem sup_eq_top_iff_coe_mul_coe_eq_univ [K.Normal] :
    K ⊔ A = ⊤ ↔ (K : Set X) * (A : Set X) = Set.univ := by
  rw [← Subgroup.normal_mul K A]
  simp [Subgroup.eq_top_iff', Set.eq_univ_iff_forall, SetLike.ext'_iff]

theorem conj_smul_le_normalizer_conj_smul (g : X) {S T : Subgroup X}
    (h : T ≤ normalizer (S : Set X)) :
    MulAut.conj g • T ≤ normalizer ((MulAut.conj g • S : Subgroup X) : Set X) := by
  intro y hy
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  have hkey : g⁻¹ * (y * z * y⁻¹) * g
      = (g⁻¹ * y * g) * (g⁻¹ * z * g) * (g⁻¹ * y * g)⁻¹ := by group
  rw [hkey]
  exact Subgroup.mem_normalizer_iff.1 (h hy) _

theorem IsHallSubgroup.subgroupOf [Finite X] {S V : Subgroup X} (hS : IsHallSubgroup π S)
    (h : S ≤ V) : IsHallSubgroup π (S.subgroupOf V) where
  natCard := by rw [natCard_subgroupOf_of_le h]; exact hS.natCard
  index := hS.index.of_dvd (Subgroup.relIndex_dvd_index_of_le h) Subgroup.index_ne_zero_of_finite

theorem conj_smul_eq_of_subgroupOf {V S T : Subgroup X} (hS : S ≤ V) (hT : T ≤ V) {v : V}
    (h : MulAut.conj v • S.subgroupOf V = T.subgroupOf V) :
    MulAut.conj (v : X) • S = T := by
  have := congrArg (fun W : Subgroup V => W.map V.subtype) h
  simpa [map_subtype_conj_smul, Subgroup.map_subgroupOf_eq_of_le hS,
    Subgroup.map_subgroupOf_eq_of_le hT] using this

theorem mem_centralizer_of_mem_normalizer_of_inf_eq_bot [K.Normal] (hinf : K ⊓ A = ⊥) {c : X}
    (hcK : c ∈ K) (hcA : c ∈ normalizer (A : Set X)) : c ∈ centralizer (A : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : c⁻¹ * a * c ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcA) a).1 ha
    simpa using this
  have hmemA : a⁻¹ * (c⁻¹ * a * c) ∈ A := A.mul_mem (A.inv_mem ha) h1
  have hmemK : a⁻¹ * (c⁻¹ * a * c) ∈ K := by
    have h2 : a⁻¹ * c⁻¹ * a⁻¹⁻¹ ∈ K := ‹K.Normal›.conj_mem _ (K.inv_mem hcK) a⁻¹
    have h3 : a⁻¹ * (c⁻¹ * a * c) = a⁻¹ * c⁻¹ * a⁻¹⁻¹ * c := by group
    rw [h3]
    exact K.mul_mem h2 hcK
  have hone : a⁻¹ * (c⁻¹ * a * c) = 1 := by
    have h : a⁻¹ * (c⁻¹ * a * c) ∈ K ⊓ A := Subgroup.mem_inf.2 ⟨hmemK, hmemA⟩
    rw [hinf] at h
    simpa using h
  have heq : c⁻¹ * a * c = a := (inv_mul_eq_one.1 hone).symm
  calc a * c = c * (c⁻¹ * a * c) := by group
    _ = c * a := by rw [heq]

theorem natCard_mul_natCard_eq_of_coprime [Finite X] [K.Normal] (hKA : K ⊔ A = ⊤)
    (hcop : (Nat.card K).Coprime (Nat.card A)) : Nat.card K * Nat.card A = Nat.card X := by
  have hinf : K ⊓ A = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have h := natCard_mul_mul_natCard_inf K A
  rw [hinf, Subgroup.card_bot, mul_one, ← Subgroup.normal_mul K A, hKA] at h
  rw [← h]
  simp

theorem index_eq_natCard_of_coprime [Finite X] [K.Normal] (hKA : K ⊔ A = ⊤)
    (hcop : (Nat.card K).Coprime (Nat.card A)) : A.index = Nat.card K := by
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A)) ?_
  rw [Subgroup.card_mul_index A, ← natCard_mul_natCard_eq_of_coprime hKA hcop, mul_comm]

theorem isHallSubgroup_primeFactors_of_coprime [Finite X] [K.Normal] (hKA : K ⊔ A = ⊤)
    (hcop : (Nat.card K).Coprime (Nat.card A)) :
    IsHallSubgroup (↑(Nat.card A).primeFactors : Set ℕ) A where
  natCard := isPiNumber_iff.2 fun p hp => Finset.mem_coe.2 hp
  index := by
    rw [isPiNumber_compl_iff, index_eq_natCard_of_coprime hKA hcop]
    intro p hp hp'
    exact Finset.disjoint_left.1
      ((Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne').2 hcop) hp
      (Finset.mem_coe.1 hp')

theorem exists_mem_inf_centralizer_conj_inv_smul_eq
    [Finite X] [Group.IsSolvable X] [K.Normal]
    (hKA : K ⊔ A = ⊤) (hcop : (Nat.card K).Coprime (Nat.card A))
    (hH₁K : H₁ ≤ K) (hH₂K : H₂ ≤ K)
    (hH₁ : IsHallSubgroup π (H₁.subgroupOf K)) (hH₂ : IsHallSubgroup π (H₂.subgroupOf K))
    (hA₁ : A ≤ normalizer (H₁ : Set X)) (hA₂ : A ≤ normalizer (H₂ : Set X)) :
    ∃ c ∈ K ⊓ centralizer (A : Set X), MulAut.conj c⁻¹ • H₁ = H₂ := by
  obtain ⟨k', hk'⟩ := exists_conj_smul_eq_of_isHallSubgroup hH₁ hH₂
  have hkK : (k' : X) ∈ K := k'.2
  have hk : MulAut.conj (k' : X) • H₁ = H₂ := conj_smul_eq_of_subgroupOf hH₁K hH₂K hk'
  set k : X := (k' : X) with hkdef
  set V : Subgroup X := normalizer (H₂ : Set X) with hVdef
  have hAV : A ≤ V := hA₂
  have hAkV : MulAut.conj k • A ≤ V := by
    have := conj_smul_le_normalizer_conj_smul k hA₁
    rwa [hk] at this
  have hAHall := isHallSubgroup_primeFactors_of_coprime hKA hcop
  have hAkHall : IsHallSubgroup (↑(Nat.card A).primeFactors : Set ℕ) (MulAut.conj k • A) :=
    hAHall.conj_smul k
  obtain ⟨v', hv'⟩ := exists_conj_smul_eq_of_isHallSubgroup
    (hAkHall.subgroupOf hAkV) (hAHall.subgroupOf hAV)
  have hv : MulAut.conj (v' : X) • (MulAut.conj k • A) = A :=
    conj_smul_eq_of_subgroupOf hAkV hAV hv'
  have hvV : (v' : X) ∈ V := v'.2
  set v : X := (v' : X) with hvdef
  have hprod : ((A : Set X) * (K : Set X)) = Set.univ := by
    rw [← Subgroup.mul_normal A K, sup_comm, hKA]
    simp
  obtain ⟨a, ha, l, hl, hal⟩ := Set.mem_mul.1 (hprod ▸ Set.mem_univ v)
  have hlV : l ∈ V := by
    have hl' : l = a⁻¹ * v := by rw [← hal]; group
    rw [hl']
    exact V.mul_mem (V.inv_mem (hAV ha)) hvV
  have hnorm : MulAut.conj (l * k) • A = A := by
    have h1 : MulAut.conj (v * k) • A = A := by rw [map_mul, mul_smul]; exact hv
    have h2 : MulAut.conj a • (MulAut.conj (l * k) • A) = A := by
      rw [← mul_smul, ← map_mul, ← mul_assoc, hal]; exact h1
    have h3 : MulAut.conj a • A = A := mem_normalizer_iff_conj_smul_eq.1 (le_normalizer ha)
    calc MulAut.conj (l * k) • A
        = MulAut.conj a⁻¹ • (MulAut.conj a • (MulAut.conj (l * k) • A)) := by
          rw [← mul_smul, ← map_mul]; simp
      _ = MulAut.conj a⁻¹ • A := by rw [h2]
      _ = A := by rw [map_inv, inv_smul_eq_iff, h3]
  have hinf : K ⊓ A = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hc₀K : l * k ∈ K := K.mul_mem hl hkK
  have hc₀C : l * k ∈ centralizer (A : Set X) :=
    mem_centralizer_of_mem_normalizer_of_inf_eq_bot hinf hc₀K
      (mem_normalizer_iff_conj_smul_eq.2 hnorm)
  refine ⟨(l * k)⁻¹, Subgroup.mem_inf.2 ⟨K.inv_mem hc₀K, inv_mem hc₀C⟩, ?_⟩
  rw [inv_inv, map_mul, mul_smul, hk]
  exact mem_normalizer_iff_conj_smul_eq.1 hlV

theorem exists_mem_inf_centralizer_forall_mem_iff
    [Finite X] [Group.IsSolvable X] [K.Normal]
    (hKA : K ⊔ A = ⊤) (hcop : (Nat.card K).Coprime (Nat.card A))
    (hH₁K : H₁ ≤ K) (hH₂K : H₂ ≤ K)
    (hH₁ : IsHallSubgroup π (H₁.subgroupOf K)) (hH₂ : IsHallSubgroup π (H₂.subgroupOf K))
    (hA₁ : A ≤ normalizer (H₁ : Set X)) (hA₂ : A ≤ normalizer (H₂ : Set X)) :
    ∃ c ∈ K ⊓ centralizer (A : Set X), ∀ y : X, y ∈ H₂ ↔ c * y * c⁻¹ ∈ H₁ := by
  obtain ⟨c, hc, hconj⟩ :=
    exists_mem_inf_centralizer_conj_inv_smul_eq hKA hcop hH₁K hH₂K hH₁ hH₂ hA₁ hA₂
  refine ⟨c, hc, fun y => ?_⟩
  rw [← hconj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, map_inv,
    inv_inv, MulAut.conj_apply]

end CFSG.FeitThompson

