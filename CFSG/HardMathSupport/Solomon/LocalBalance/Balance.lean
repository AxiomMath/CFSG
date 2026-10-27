module

public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.HardMathSupport.Solomon.Coordinator.Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

abbrev barOf {G : Type*} [Group G] (p : ℕ) (L : Subgroup G) : Type _ :=
  ↥L ⧸ GLAPPrimeCore p ↥L

@[expose] def innerAut (K : Type*) [Group K] : Subgroup (MulAut K) :=
  (MulAut.conj : K →* MulAut K).range

@[expose] def localDeltaIn (p : ℕ) {M : Type*} [Group M] (H D : Subgroup M) : Subgroup M :=
  ⨅ (d : M) (_ : d ∈ D) (_ : d ≠ 1), GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set M))

@[expose] def IsLocallyBalanced (p k : ℕ) {K : Type*} [Group K] (A : Subgroup (MulAut K)) : Prop :=
  ∀ D : Subgroup (MulAut K), IsEkIn p k A D → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    D ≤ Subgroup.normalizer (H : Set (MulAut K)) → localDeltaIn p H D = ⊥

@[expose] def IsWeaklyLocallyBalanced (p k : ℕ) {K : Type*} [Group K]
    (A : Subgroup (MulAut K)) : Prop :=
  ∀ D : Subgroup (MulAut K), IsEkIn p k A D → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    A ≤ Subgroup.normalizer (H : Set (MulAut K)) → ⁅localDeltaIn p H D, A⁆ = ⊥

variable {G : Type*} [Group G]

@[expose] noncomputable def autBar (p : ℕ) (B L : Subgroup G) : Subgroup (MulAut (barOf p L)) :=
  ((B ⊓ Subgroup.normalizer (L : Set G)).subgroupOf (Subgroup.normalizer (L : Set G))).map
    (barAut p L)

@[expose] def IsCompLocallyBalanced (p k : ℕ) (B L : Subgroup G) : Prop :=
  IsLocallyBalanced p k (autBar p B L)

@[expose] def IsCompWeaklyLocallyBalanced (p k : ℕ) (B L : Subgroup G) : Prop :=
  IsWeaklyLocallyBalanced p k (autBar p B L)

end CFSG.HardMathSupport.Solomon.LocalBalance
