module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

@[expose] def LocalNoQ16Q16' (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (F : Type) [Group F], P F → ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal],
    Nonempty (↥N ≃* F) → Subgroup.centralizer (N : Set Y) = ⊥ →
    ∀ t : Y, orderOf t = 2 → ∀ K K' : Subgroup Y,
      CFSG.Open.IsSubnormal K (Subgroup.centralizer ({t} : Set Y)) →
      CFSG.Open.IsSubnormal K' (Subgroup.centralizer ({t} : Set Y)) →
      IsTwoPrimeTwo K → IsTwoPrimeTwo K' →
      ∀ x ∈ K, ∀ y ∈ K, ∀ x' ∈ K', ∀ y' ∈ K', x ^ 4 = t → ¬ Q16Q16 x y x' y'

theorem twinLeafR_of_local' {r n : ℕ} (hr : 4 ≤ r) {P : ∀ (F : Type) [Group F], Prop}
    (h : LocalNoQ16Q16' P) : TwinLeafR r n P := by
  intro Y _ _ R S t hP _ hPF
  haveI := genFittingFStar_normal Y
  haveI := hP.core.simple
  obtain ⟨K', x, y, x', y', -, ⟨g, hg⟩, -, hsub', hx, hy, hx', hy', hq⟩ :=
    exists_q16Q16_of_perp hr hP
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hP.core.datum
  have hsub : CFSG.Open.IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_of_hypOmegaGen hP.core.hyp (CoreAssembly.mem_conjClass_self _) hz
  have h22' : IsTwoPrimeTwo K' := by
    rw [← show conjSub g (tightCore R) = K' from hg]
    exact isTwoPrimeTwo_conjSub g (isTwoPrimeTwo_core hP)
  have hxt : x ^ 4 = t := by
    obtain ⟨hx4, hx8, -, -⟩ := hq.1
    have h1 : x ^ 4 * x ^ 4 = 1 := by rw [← pow_add]; exact hx8
    rcases hz.unique (x ^ 4) ((tightCore R).pow_mem hx 4) h1 with h' | h'
    · exact absurd h' hx4
    · exact h'
  exact h _ hPF Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hP.core.nonab) t hP.core.datum.order _ K' hsub hsub'
    (isTwoPrimeTwo_core hP) h22' x hx y hy x' hx' y' hy' hxt hq

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
