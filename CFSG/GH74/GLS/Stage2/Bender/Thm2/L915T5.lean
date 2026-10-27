module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T4

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1

@[expose] def Prop9_5Tail3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    (k = Kind.g2 ∨ k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε) →
    ∀ (J : Subgroup G) (n : ℕ), IsQuasisimple ↥J → z ∈ J →
      (∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) → 2 ≤ n →
      LieModel (↥J ⧸ center ↥J) .PSL 3 p n → Op p M ≤ J → IsElementaryAbelian p ↥(Op p M) →
      Nat.card ↥(Op p M) = p ^ (2 * n) → Op p M ⊓ Cen z = ⊥ →
      (∀ x ∈ Op p M, x ≠ 1 → ∀ y ∈ Op p M, y ≠ 1 → ∃ c ∈ J ⊓ Cen z, c * x * c⁻¹ = y) →
      M ≤ normalizer (J : Set G)

theorem prop9_5Tail2_of_tail3 (h : Prop9_5Tail3) : Prop9_5Tail2 := by
  intro G _ _ z k S M p hC J n hJ hzJ hnoc hn hLie hPJ hel hcard hPz htr
  cases k with
  | g2 => exact h G z Kind.g2 S M p hC (Or.inl rfl) J n hJ hzJ hnoc hn hLie hPJ hel hcard hPz htr
  | psp4 =>
    exact h G z Kind.psp4 S M p hC (Or.inr (Or.inl rfl)) J n hJ hzJ hnoc hn hLie hPJ hel hcard hPz htr
  | l4 ε =>
    exact h G z (Kind.l4 ε) S M p hC (Or.inr (Or.inr ⟨ε, rfl⟩)) J n hJ hzJ hnoc hn hLie hPJ hel hcard
      hPz htr
  | m12 =>
    exact (L915.false_of_m12 hC.ctx.data hC.orderOf_z hzJ hnoc hC.prime hC.odd hn hLie).elim
  | mcl => exact (L915.false_of_sporadic hC (Or.inl rfl) hzJ hnoc hn hLie hel hcard hPz).elim
  | ly => exact (L915.false_of_sporadic hC (Or.inr rfl) hzJ hnoc hn hLie hel hcard hPz).elim

theorem lemma9_15_of_tail3 (h43E : Prop4_3E) (h34 : Leaf_Prop34) (hTail : Prop9_5Tail3)
    (h911 : Prop9_11Core) : Lemma9_15 :=
  lemma9_15_of_leaves'' h43E h34 (prop9_5Tail2_of_tail3 hTail) h911

end CFSG.GH74.GLS.Stage2.Bender.Thm2
