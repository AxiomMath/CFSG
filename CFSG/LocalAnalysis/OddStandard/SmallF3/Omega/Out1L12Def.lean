module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] abbrev L12R {S : Type} [Group S] (t : S) : Subgroup S :=
  Subgroup.centralizer ({t} : Set S)

@[expose] abbrev L12N {S : Type} [Group S] (t : S) : Subgroup S :=
  Subgroup.normalizer (L12R t : Set S)

structure L12Coord (S : Type) [Group S] (t u : S) : Prop where
  ord_t : orderOf t = 2
  ord_u : orderOf u = 4
  comm : u * t = t * u
  not_mem : t ∉ Subgroup.zpowers u
  cent : ∀ x : S, x * t = t * x → ∃ i j : ℕ, x = u ^ i * t ^ j
  card : Nat.card (L12R t) = 8

structure L12Main (S : Type) [Group S] (t u : S) : Prop where
  coord : L12Coord S t u
  z_central : ∀ x : S, x * u ^ 2 = u ^ 2 * x
  N_comm : ∀ n ∈ L12N t, n * u = u * n
  N_conj : ∀ n ∈ L12N t, n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * u ^ 2
  mem_N : ∀ x : S, x * t * x⁻¹ * t⁻¹ ∈ Subgroup.zpowers u → x ∈ L12N t
  N_card : Nat.card (L12N t) = 16
  center_N : ∀ w ∈ L12N t, (∀ n ∈ L12N t, n * w = w * n) → w ∈ Subgroup.zpowers u

end CFSG.OddStandard.SmallF3.Omega
