module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p d : ℕ} {X Y : Type*} [Group X] [Group Y]

structure IsElementaryAbelianSubgroup (p : ℕ) (A : Subgroup X) : Prop where
  mul_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  pow_eq_one : ∀ x ∈ A, x ^ p = 1

theorem IsElementaryAbelianSubgroup.isMulCommutative {A : Subgroup X}
    (h : IsElementaryAbelianSubgroup p A) : IsMulCommutative A :=
  IsMulCommutative.of_comm fun a b => Subtype.ext (h.mul_comm a a.2 b b.2)

theorem isElementaryAbelianSubgroup_iff {A : Subgroup X} :
    IsElementaryAbelianSubgroup p A ↔ IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1 :=
  ⟨fun h => ⟨h.isMulCommutative, h.pow_eq_one⟩, fun ⟨hc, hexp⟩ =>
    ⟨fun x hx y hy =>
      congrArg Subtype.val (hc.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩), hexp⟩⟩

theorem isElementaryAbelianSubgroup_bot (p : ℕ) :
    IsElementaryAbelianSubgroup p (⊥ : Subgroup X) where
  mul_comm := by simp
  pow_eq_one := by simp

theorem IsElementaryAbelianSubgroup.mono {A B : Subgroup X}
    (h : IsElementaryAbelianSubgroup p A) (hBA : B ≤ A) :
    IsElementaryAbelianSubgroup p B where
  mul_comm x hx y hy := h.mul_comm x (hBA hx) y (hBA hy)
  pow_eq_one x hx := h.pow_eq_one x (hBA hx)

theorem IsElementaryAbelianSubgroup.isPGroup {A : Subgroup X}
    (h : IsElementaryAbelianSubgroup p A) : IsPGroup p A :=
  fun g => ⟨1, by simpa using Subtype.ext (h.pow_eq_one g g.2)⟩

theorem IsElementaryAbelianSubgroup.map {A : Subgroup X} (h : IsElementaryAbelianSubgroup p A)
    (f : X →* Y) : IsElementaryAbelianSubgroup p (A.map f) where
  mul_comm := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.mul_comm a ha b hb]
  pow_eq_one := by
    rintro x ⟨a, ha, rfl⟩
    rw [← map_pow, h.pow_eq_one a ha, map_one]

theorem IsElementaryAbelianSubgroup.comap {A : Subgroup Y} (h : IsElementaryAbelianSubgroup p A)
    {f : X →* Y} (hf : Function.Injective f) :
    IsElementaryAbelianSubgroup p (A.comap f) where
  mul_comm x hx y hy := hf (by rw [map_mul, map_mul, h.mul_comm (f x) hx (f y) hy])
  pow_eq_one x hx := hf (by rw [map_pow, h.pow_eq_one (f x) hx, map_one])

theorem IsElementaryAbelianSubgroup.mem_elementaryAbelianRanks (hp : p.Prime) {A : Subgroup X}
    (h : IsElementaryAbelianSubgroup p A) (hcard : Nat.card A = p ^ d) :
    d ∈ elementaryAbelianRanks p X :=
  (mem_elementaryAbelianRanks_iff_exists_subgroup hp).2
    ⟨A, h.isMulCommutative, h.pow_eq_one, hcard⟩

theorem exists_maximal_isElementaryAbelianSubgroup_ge [Finite X] {A : Subgroup X}
    (h : IsElementaryAbelianSubgroup p A) :
    ∃ B : Subgroup X, A ≤ B ∧ Maximal (IsElementaryAbelianSubgroup p) B :=
  Finite.exists_le_maximal h

theorem maximal_isElementaryAbelianSubgroup_map (e : X ≃* Y) {A : Subgroup X}
    (h : Maximal (IsElementaryAbelianSubgroup p) A) :
    Maximal (IsElementaryAbelianSubgroup p) (A.map e.toMonoidHom) := by
  refine ⟨h.prop.map _, fun B hB hle => ?_⟩
  have h2 := h.le_of_ge (hB.comap e.injective) (Subgroup.map_le_iff_le_comap.1 hle)
  calc B = (B.comap e.toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
    _ ≤ A.map e.toMonoidHom := Subgroup.map_mono h2

def IsPNarrow (p : ℕ) (P : Type*) [Group P] : Prop :=
  elementaryAbelianPRank p P ≤ 2 ∨
    ∃ A : Subgroup P, Maximal (IsElementaryAbelianSubgroup p) A ∧ Nat.card A = p ^ 2

theorem isPNarrow_iff (p : ℕ) (P : Type*) [Group P] :
    IsPNarrow p P ↔ elementaryAbelianPRank p P ≤ 2 ∨
      ∃ A : Subgroup P, Maximal (IsElementaryAbelianSubgroup p) A ∧ Nat.card A = p ^ 2 := Iff.rfl

theorem isPNarrow_of_elementaryAbelianPRank_le_two (h : elementaryAbelianPRank p X ≤ 2) :
    IsPNarrow p X := Or.inl h

theorem isPNarrow_of_maximal_card_eq {A : Subgroup X}
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) (hcard : Nat.card A = p ^ 2) :
    IsPNarrow p X := Or.inr ⟨A, hA, hcard⟩

theorem isPNarrow_of_subsingleton [Subsingleton X] (hp : 1 < p) : IsPNarrow p X :=
  Or.inl (by rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp]; omega)

theorem isPNarrow_of_not_dvd_card [Finite X] (hp : p.Prime) (h : ¬ p ∣ Nat.card X) :
    IsPNarrow p X :=
  Or.inl (by rw [(elementaryAbelianPRank_eq_zero_iff hp).2 h]; omega)

theorem two_le_elementaryAbelianPRank_of_maximal_card_eq [Finite X] (hp : p.Prime)
    {A : Subgroup X} (hA : Maximal (IsElementaryAbelianSubgroup p) A)
    (hcard : Nat.card A = p ^ 2) : 2 ≤ elementaryAbelianPRank p X :=
  le_elementaryAbelianPRank hp.one_lt
    (IsElementaryAbelianSubgroup.mem_elementaryAbelianRanks hp hA.prop hcard)

theorem isPNarrow_congr [Finite X] [Finite Y] (hp : 1 < p) (e : X ≃* Y) :
    IsPNarrow p X ↔ IsPNarrow p Y := by
  constructor
  · rintro (h | ⟨A, hA, hcard⟩)
    · exact Or.inl (by rwa [← elementaryAbelianPRank_eq_of_mulEquiv hp e])
    · exact Or.inr ⟨A.map e.toMonoidHom, maximal_isElementaryAbelianSubgroup_map e hA,
        by rw [Subgroup.card_map_of_injective e.injective, hcard]⟩
  · rintro (h | ⟨A, hA, hcard⟩)
    · exact Or.inl (by rwa [elementaryAbelianPRank_eq_of_mulEquiv hp e])
    · exact Or.inr ⟨A.map e.symm.toMonoidHom, maximal_isElementaryAbelianSubgroup_map e.symm hA,
        by rw [Subgroup.card_map_of_injective e.symm.injective, hcard]⟩

def betaPrimes (X : Type*) [Group X] [Finite X] : Set ℕ :=
  {p | p ∈ (Nat.card X).primeFactors ∧ ∀ P : Sylow p X, ¬ IsPNarrow p (P : Subgroup X)}

theorem mem_betaPrimes_iff [Finite X] :
    p ∈ betaPrimes X ↔
      p ∈ (Nat.card X).primeFactors ∧ ∀ P : Sylow p X, ¬ IsPNarrow p (P : Subgroup X) := Iff.rfl

theorem betaPrimes_subset_primeFactors [Finite X] :
    betaPrimes X ⊆ (Nat.card X).primeFactors := fun _ h => h.1

theorem prime_of_mem_betaPrimes [Finite X] (h : p ∈ betaPrimes X) : p.Prime :=
  Nat.prime_of_mem_primeFactors h.1

theorem dvd_card_of_mem_betaPrimes [Finite X] (h : p ∈ betaPrimes X) : p ∣ Nat.card X :=
  Nat.dvd_of_mem_primeFactors h.1

theorem not_isPNarrow_of_mem_betaPrimes [Finite X] (h : p ∈ betaPrimes X) (P : Sylow p X) :
    ¬ IsPNarrow p (P : Subgroup X) := h.2 P

theorem betaPrimes_finite [Finite X] : (betaPrimes X).Finite :=
  (Nat.card X).primeFactors.finite_toSet.subset betaPrimes_subset_primeFactors

theorem mem_betaPrimes_iff_exists [Finite X] (hp : p.Prime) :
    p ∈ betaPrimes X ↔ p ∣ Nat.card X ∧ ∃ P : Sylow p X, ¬ IsPNarrow p (P : Subgroup X) := by
  have := Fact.mk hp
  rw [mem_betaPrimes_iff, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨-, hdvd, -⟩, h⟩
    exact ⟨hdvd, Classical.arbitrary _, h _⟩
  · rintro ⟨hdvd, P, hP⟩
    exact ⟨⟨hp, hdvd, Nat.card_pos.ne'⟩,
      fun Q hQ => hP ((isPNarrow_congr hp.one_lt (Sylow.equiv P Q)).2 hQ)⟩

end

end CFSG.FeitThompson
