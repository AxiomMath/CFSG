module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

abbrev IsL2OddW {G : Type} [Group G] (J : Subgroup G) : Prop :=
  ∃ r m : ℕ, r.Prime ∧ r ≠ 2 ∧ (¬ ∃ k : ℕ, m = 2 ^ k) ∧
    (LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 r m ∨
      HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) (fun q => q = r ^ m))

structure Ctx29w (G : Type) [Group G] [Finite G] (x : G) (K A B Q : Subgroup G) (y b : G)
    (D J : Subgroup G) : Prop where
  hyp : Hyp2 G
  noAlt : NoAltJ2 G
  circ : IsJ2Circ x K
  shape : B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K)
  src : IsSource2 x K A
  ext : IsExtSource2 x K A B
  rankB : pRank 2 ↥B = 4
  C_rank : pRank 2 ↥(CxK x K) = 2
  B0_le_C : B ⊓ cSec K ≤ CxK x K
  Q_syl : IsSylowOf 2 Q (CxK x K)
  Q_cent : Q ≤ centralizer (A : Set G)
  B0_le_Q : B ⊓ cSec K ≤ Q
  y_mem : y ∈ A ⊓ K
  y_ord : orderOf y = 2
  notG : ¬ (A7InGamma K A B ∧ IsKBal 3 B ∧ IsWeakKBal 2 B)
  b_mem : b ∈ B
  obs : Obs52 B b D J ∨
    (b = y ∧ Obs32 A y D J ∧ D ≤ A ∧ IsA7Bar J ∧ ¬ J ≤ gammaK 2 B 3)

@[expose] def Tab52w (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K A B : Subgroup G) (b : G) (D J : Subgroup G), Hyp2 G → NoAltJ2 G → IsJ2Circ x K →
    B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B → pRank 2 ↥B = 4 →
    Obs52 B b D J → IsA7Bar J ∨ IsL2OddW J

section Passages

variable {G : Type} [Group G] [Finite G]

theorem Ctx29w.toCtx29 {x y b : G} {K A B Q D J : Subgroup G} (h : Ctx29w G x K A B Q y b D J)
    (htype : IsA7Bar J ∨ IsL2OddNonSquare J) : Ctx29 G x K A B Q y b D J :=
  ⟨h.hyp, h.noAlt, h.circ, h.shape, h.src, h.ext, h.rankB, h.C_rank, h.B0_le_C, h.Q_syl, h.Q_cent,
    h.B0_le_Q, h.y_mem, h.y_ord, h.notG, h.b_mem, htype, h.obs⟩

omit [Finite G] in
theorem isL2OddNonSquare_of_W {J : Subgroup G} (h : IsA7Bar J ∨ IsL2OddW J)
    (hsl : ¬ HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) Odd) : IsA7Bar J ∨ IsL2OddNonSquare J := by
  rcases h with hA | ⟨r, m, hr, hr2, hm, hL | ⟨F, hF, hFin, hq, he⟩⟩
  · exact Or.inl hA
  · exact Or.inr ⟨r, m, hr, hr2, hm, hL⟩
  · refine absurd ⟨F, hF, hFin, ?_, he⟩ hsl
    rw [hq]
    exact Odd.pow (hr.odd_of_ne_two hr2)

end Passages

end CFSG.GH74.Generic.BProg.B3
