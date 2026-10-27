module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

structure IsExt2 (R : Subgroup K) (t : K) : Prop where
  t_mem : t ∈ R
  t_sq : t ^ 2 = 1
  t_ne : t ≠ 1
  t_comm : ∀ r ∈ R, r * t = t * r
  center_le : ∀ y ∈ R, (∀ r ∈ R, y * r = r * y) → y ∈ zpowers t
  sq_mem : ∀ r ∈ R, r ^ 2 ∈ zpowers t
  comm_mem : ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ zpowers t

structure Setup628 (p f : ℕ) (S X N : Subgroup K) (z : K) : Prop where
  hp : p.Prime
  hf : f.Prime
  hp2 : p ≠ 2
  hf2 : f ≠ 2
  hfp : f ≠ p
  hS : IsPGroup 2 S
  hX : IsPGroup f X
  hNX : N ≤ X
  hNn : (N.subgroupOf X).Normal
  hXN : ¬ X ≤ N
  hzp : z ^ p = 1
  hz1 : z ≠ 1
  hzS : zpowers z ≤ normalizer (S : Set K)
  hSX : S ⊔ zpowers z ≤ normalizer (X : Set K)
  hSN : S ⊔ zpowers z ≤ normalizer (N : Set K)
  hR : ⁅zpowers z, S⁆ ≠ ⊥
  hC : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
    X ⊓ centralizer (S₀ : Set K) ≤ N
  hCz : X ⊓ centralizer ({z} : Set K) ≤ N

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
