module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDNodes
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6NoCover

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (NoCover)

variable {p f : ℕ} [Fact p.Prime]

theorem spinMinus6Generated_galois (hp2 : p ≠ 2) :
    SpinMinus6Generated (minusCoeffs_irr p f) :=
  CFSG.ClassicalInvolution.WeakCT.spinMinusModel_blocks_sup_eq_top (minusCoeffs_irr p f)
    (Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p f) p]; exact hp2))

theorem spinMinus6_noCover_galois (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    NoCover.{0} Odd (spinGroup (quadMinus 3 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  exact CFSG.ClassicalInvolution.WeakCT.spinMinus6_noCover_odd hp2 hF (by rw [hF]; exact hq)
    (minusCoeffs_irr p f)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem exists_nodes_typeTwistedD_odd {m : ℕ} (hm : 4 ≤ m) (c : TCtx p f .POmegaMinus m Ω K z) :
    ∃ j : Fin (m - 1) → Subgroup G, (∀ a, Commutes K (j a)) ∧ (∀ a, ⁅j a, j a⁆ = j a) ∧
      (∀ a, j a ≤ locLayer Ω z) ∧ (∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ Ω) ∧
      (∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u) ∧
      (∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
      (∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
        ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (j a) (j b)) :=
  exists_nodes_typeTwistedD hm (spinMinus6Generated_galois c.hp2)
    (spinMinus6_noCover_galois c.hp2 c.hq) c

end CFSG.ClassicalInvolution.RouteD
