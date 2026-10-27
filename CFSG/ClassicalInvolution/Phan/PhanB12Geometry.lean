module

public import CFSG.ClassicalInvolution.Phan.PhanB11Final

public section

namespace CFSG.ClassicalInvolution.PhanB3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.Monster.B.Geometry
open CFSG.ClassicalInvolution.Asc77.B3C (PhanB3Recognition)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def PhanB3Geometry (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → p ^ f % 4 = 3 →
    ∀ (hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) (h2 : (2 : GaloisField p f) ≠ 0),
      ∃ (C : B2Coord hK (GaloisField p f) h2)
        (S : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))),
        GoodFamily S ∧
          (S.ι 0).range ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)) ∧
          (phanSystem S).Connected ∧ (phanSystem S).SimplyTwoConnected

theorem phanB3Universal_of_geometry (hG : PhanB3Geometry p f) : PhanB3Universal p f := by
  intro hp2 hq hmod hK h2
  obtain ⟨C, S, hg, hfund, hconn, hsc⟩ := hG hp2 hq hmod hK h2
  refine ⟨C, S, hfund, fun Y _ E => ?_⟩
  have h2K : (2 : GaloisField p (2 * f)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField p (2 * f)) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p (2 * f)) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h')
  exact universal_of_geometry hq hg h2K hconn hsc E


theorem phanB3Recognition_of_geometry (hG : PhanB3Geometry p f) : PhanB3Recognition p f :=
  phanB3Recognition_of_universal (phanB3Universal_of_geometry hG)

end CFSG.ClassicalInvolution.PhanB3
