module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74.L38

open CFSG Subgroup
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_isSylowIn {C T U : Subgroup G} (hT : IsSylowIn 2 T C) (hU : IsPGroup 2 U)
    (hUC : U ≤ C) (hTU : T ≤ U) : U ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : IsPGroup 2 (T.subgroupOf C) := hT.2.1.comap_of_injective _ C.subtype_injective
  set T₁ : Sylow 2 C := hp1.toSylow hT.2.2 with hT₁
  have hU' : IsPGroup 2 (U.subgroupOf C) := hU.comap_of_injective _ C.subtype_injective
  have hle : (T₁ : Subgroup C) ≤ U.subgroupOf C := fun c hc => hTU hc
  have heq := T₁.is_maximal' hU' hle
  intro u hu
  have hmem : (⟨u, hUC hu⟩ : C) ∈ U.subgroupOf C := hu
  rw [heq] at hmem
  exact hmem

omit [Finite G] in
theorem mem_of_isSylowIn {C T : Subgroup G} (hT : IsSylowIn 2 T C) {g : G} (hgC : g ∈ C)
    (hg : orderOf g = 2) (hgT : ∀ x ∈ T, g * x = x * g) : g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hnorm : zpowers g ≤ normalizer (T : Set G) := by
    rw [zpowers_le]
    exact centralizer_le_normalizer (T : Set G)
      (mem_centralizer_iff.mpr fun x hx => (hgT x hx).symm)
  have hU : IsPGroup 2 ↥(T ⊔ zpowers g) := hT.2.1.to_sup_of_normal_left' hzp hnorm
  exact le_of_isSylowIn hT hU (sup_le hT.1 (zpowers_le.mpr hgC)) le_sup_left
    (mem_sup_right (mem_zpowers g))

omit [Finite G] in
theorem mem_of_isSylowIn_of_le {C T P : Subgroup G} (hT : IsSylowIn 2 T C) (hP : IsPGroup 2 P)
    (hTP : T ≤ P) {x : G} (hxP : x ∈ P) (hxC : x ∈ C) : x ∈ T :=
  le_of_isSylowIn hT (hP.to_le (sup_le hTP (zpowers_le.mpr hxP)))
    (sup_le hT.1 (zpowers_le.mpr hxC)) le_sup_left (mem_sup_right (mem_zpowers x))

theorem factorization_two_pow_mul {a o : ℕ} (ho : Odd o) : (2 ^ a * o).factorization 2 = a := by
  have ho0 : o ≠ 0 := fun h => by rw [h] at ho; exact Nat.not_odd_zero ho
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) ho0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr ho)
      (even_iff_two_dvd.mpr h)), smul_eq_mul, mul_one, add_zero]

theorem card_eq_of_isSylowIn {C T : Subgroup G} (hT : IsSylowIn 2 T C) :
    Nat.card T = 2 ^ (Nat.card C).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : IsPGroup 2 (T.subgroupOf C) := hT.2.1.comap_of_injective _ C.subtype_injective
  have h := (hp1.toSylow hT.2.2).card_eq_multiplicity
  rw [← h]
  exact (Nat.card_congr (subgroupOfEquivOfLe hT.1).toEquiv).symm

theorem conj_mem_of_card_sylow {C T : Subgroup G} (hT : IsSylowIn 2 T C) (P : Sylow 2 G)
    (hTP : T ≤ P) {o : ℕ} (ho : Odd o) (hcard : Nat.card G = Nat.card C * (2 * o)) {x y : G}
    (hx : x ∈ (P : Subgroup G)) (hy : y ∈ T) : x * y * x⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have ho0 : o ≠ 0 := fun h => by rw [h] at ho; exact Nat.not_odd_zero ho
  have hfac : (Nat.card G).factorization 2 = (Nat.card C).factorization 2 + 1 := by
    rw [hcard, Nat.factorization_mul hC0 (mul_ne_zero two_ne_zero ho0), Finsupp.add_apply,
      show 2 * o = 2 ^ 1 * o by rw [pow_one], factorization_two_pow_mul ho]
  have hP : Nat.card (P : Subgroup G) = 2 * Nat.card T := by
    rw [P.card_eq_multiplicity, card_eq_of_isSylowIn hT, hfac, pow_succ, mul_comm]
  have hidx : (T.subgroupOf (P : Subgroup G)).index = 2 := by
    have h := relIndex_mul_card T (P : Subgroup G)
    rw [inf_of_le_left hTP, hP] at h
    have hT0 : 0 < Nat.card T := Nat.card_pos
    change T.relIndex (P : Subgroup G) = 2
    nlinarith
  have hN := normal_of_index_eq_two hidx
  have h := hN.conj_mem ⟨y, hTP hy⟩ hy ⟨x, hx⟩
  exact h

end CFSG.ComponentClassification.HarrisLit.T1.S74.L38
