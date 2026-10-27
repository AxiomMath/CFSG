module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2Torus
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup Matrix
open scoped MatrixGroups

theorem map_equiv_centralizer {G N : Type*} [Group G] [Group N] (f : G ≃* N) (s : Set G) :
    (centralizer s).map f.toMonoidHom = centralizer (f '' s) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    apply f.symm.injective
    simpa using h y hy
  · intro h y hy
    apply f.injective
    simpa using h (f y) ⟨y, hy, rfl⟩

theorem centralizer_zpowers {G : Type*} [Group G] (d : G) :
    centralizer (zpowers d : Set G) = centralizer {d} := by
  rw [zpowers_eq_closure, centralizer_closure]

variable {k : Type*} [Field k] [CharP k 2] {X : Type*} [Group X]

theorem exists_mulEquiv_eq_diagSL [Finite k] (ψ : X ≃* SL(2, k)) {d : X} (hd1 : d ≠ 1)
    (hd : d ^ (Nat.card k - 1) = 1) :
    ∃ (ψ' : X ≃* SL(2, k)) (μ : kˣ), μ ≠ 1 ∧ ψ' d = diagSL μ := by
  obtain ⟨x, μ, hμ, hx⟩ := exists_conj_eq_diagSL (g := ψ d) (by simpa using hd1)
    (by rw [← map_pow, hd, map_one])
  exact ⟨ψ.trans (MulAut.conj x), μ, hμ, by simpa [MulAut.conj_apply] using hx⟩

theorem map_centralizer_zpowers_eq_torusSL (ψ : X ≃* SL(2, k)) {d : X} {μ : kˣ} (hμ : μ ≠ 1)
    (hψd : ψ d = diagSL μ) :
    (centralizer (zpowers d : Set X)).map ψ.toMonoidHom = torusSL k := by
  rw [centralizer_zpowers, map_equiv_centralizer, Set.image_singleton, hψd,
    centralizer_diagSL hμ]

theorem exists_mulEquiv_map_centralizer_zpowers [Finite k] (ψ : X ≃* SL(2, k)) {d : X}
    (hd1 : d ≠ 1) (hd : d ^ (Nat.card k - 1) = 1) :
    ∃ (ψ' : X ≃* SL(2, k)) (μ : kˣ), μ ≠ 1 ∧ ψ' d = diagSL μ ∧
      (centralizer (zpowers d : Set X)).map ψ'.toMonoidHom = torusSL k := by
  obtain ⟨ψ', μ, hμ, hψd⟩ := exists_mulEquiv_eq_diagSL ψ hd1 hd
  exact ⟨ψ', μ, hμ, hψd, map_centralizer_zpowers_eq_torusSL ψ' hμ hψd⟩

theorem isMulCommutative_centralizer_zpowers [Finite k] (ψ : X ≃* SL(2, k)) {d : X}
    (hd1 : d ≠ 1) (hd : d ^ (Nat.card k - 1) = 1) :
    IsMulCommutative (centralizer (zpowers d : Set X)) := by
  obtain ⟨ψ', -, -, -, hC⟩ := exists_mulEquiv_map_centralizer_zpowers ψ hd1 hd
  refine isMulCommutative_iff.2 fun a b => Subtype.ext (ψ'.injective ?_)
  have ha : ψ' a ∈ torusSL k := hC ▸ ⟨a, a.2, rfl⟩
  have hb : ψ' b ∈ torusSL k := hC ▸ ⟨b, b.2, rfl⟩
  have := mul_comm' (⟨ψ' a, ha⟩ : torusSL k) ⟨ψ' b, hb⟩
  simpa using congrArg Subtype.val this

theorem card_centralizer_zpowers [Finite k] (ψ : X ≃* SL(2, k)) {d : X} (hd1 : d ≠ 1)
    (hd : d ^ (Nat.card k - 1) = 1) :
    Nat.card (centralizer (zpowers d : Set X)) = Nat.card k - 1 := by
  obtain ⟨ψ', -, -, -, hC⟩ := exists_mulEquiv_map_centralizer_zpowers ψ hd1 hd
  rw [← card_torusSL, ← hC, Subgroup.card_map_of_injective ψ'.injective]

theorem centralizer_zpowers_le_normalizer [Finite k] (ψ : X ≃* SL(2, k)) {d : X} (hd1 : d ≠ 1)
    (hd : d ^ (Nat.card k - 1) = 1) {S : Subgroup X} (hS : Nat.card S = Nat.card k)
    (hdS : d ∈ normalizer (S : Set X)) :
    centralizer (zpowers d : Set X) ≤ normalizer (S : Set X) := by
  obtain ⟨ψ', μ, hμ, hψd, hC⟩ := exists_mulEquiv_map_centralizer_zpowers ψ hd1 hd
  have hS' : Nat.card (S.map ψ'.toMonoidHom) = Nat.card k := by
    rw [Subgroup.card_map_of_injective ψ'.injective, hS]
  have hdS' : diagSL μ ∈ normalizer ((S.map ψ'.toMonoidHom : Subgroup SL(2, k)) :
      Set SL(2, k)) := by
    rw [← map_equiv_normalizer_eq, ← hψd]
    exact ⟨d, hdS, rfl⟩
  have h := torusSL_le_normalizer hS' hμ hdS'
  rw [← hC, ← map_equiv_normalizer_eq] at h
  exact (Subgroup.map_le_map_iff_of_injective ψ'.injective).1 h

theorem centralizer_zpowers_inf_centralizer_eq_bot [Finite k] (ψ : X ≃* SL(2, k)) {d : X}
    (hd1 : d ≠ 1) (hd : d ^ (Nat.card k - 1) = 1) {S : Subgroup X}
    (hS : Nat.card S = Nat.card k) (hdS : d ∈ normalizer (S : Set X)) :
    centralizer (zpowers d : Set X) ⊓ centralizer (S : Set X) = ⊥ := by
  obtain ⟨ψ', μ, hμ, hψd, hC⟩ := exists_mulEquiv_map_centralizer_zpowers ψ hd1 hd
  have hS' : Nat.card (S.map ψ'.toMonoidHom) = Nat.card k := by
    rw [Subgroup.card_map_of_injective ψ'.injective, hS]
  have hdS' : diagSL μ ∈ normalizer ((S.map ψ'.toMonoidHom : Subgroup SL(2, k)) :
      Set SL(2, k)) := by
    rw [← map_equiv_normalizer_eq, ← hψd]
    exact ⟨d, hdS, rfl⟩
  have h := torusSL_inf_centralizer hS' hμ hdS'
  rw [← hC, coe_map, MulEquiv.coe_toMonoidHom, ← map_equiv_centralizer,
    ← Subgroup.map_inf_eq _ _ _ ψ'.injective] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ ψ'.injective).1 h

theorem card_sylow_two_eq [Finite k] (ψ : X ≃* SL(2, k)) (P : Sylow 2 X) :
    Nat.card P = Nat.card k := by
  have : Fintype k := Fintype.ofFinite k
  have : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  rw [← Nat.card_eq_fintype_card] at hn
  have hq : 1 ≤ Nat.card k ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hodd : ¬ 2 ∣ Nat.card k ^ 2 - 1 := by
    intro h2
    have h4 : 2 ∣ Nat.card k ^ 2 := by
      rw [hn, ← pow_mul]
      exact dvd_pow_self 2 (by positivity)
    omega
  have hX : Nat.card X = 2 ^ (n : ℕ) * (Nat.card k ^ 2 - 1) := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hn]
  rw [P.card_eq_multiplicity, hX, Nat.factorization_mul (by positivity) (by omega),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, hn]

end CFSG.LocalAnalysis.EvenBN.Common
