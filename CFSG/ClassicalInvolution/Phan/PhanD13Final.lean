module

public import CFSG.ClassicalInvolution.Phan.PhanD2Reduction
public import CFSG.ClassicalInvolution.Phan.PhanD9Tits

public section

namespace CFSG.ClassicalInvolution.PhanD4

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin
open CFSG.Monster.B.Geometry

variable {p f : ℕ} [Fact p.Prime]

@[expose] def PhanD4Geometry (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∃ S : PhanFamilyD4 (GaloisField p (2 * f)) p f (spinGroup (quadPlus 4 (GaloisField p f))),
      GoodFamily S ∧
        (S.ι 0).range ∈ fundamentalSubgroups .POmegaPlus
          (plusDatum 4 (GaloisField p f) (by norm_num)) ∧
        (phanSystem S).Connected ∧ (phanSystem S).SimplyTwoConnected

theorem phanD4Universal_of_geometry (hG : PhanD4Geometry p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    PhanD4Universal p f := by
  obtain ⟨S, hg, hfund, hconn, hsc⟩ := hG hp2 hq
  refine ⟨S, hfund, fun Y _ F => ?_⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField p (2 * f)) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p (2 * f)) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h')
  exact universal_of_geometry hK' hq hg h2 hconn hsc F


theorem phanD4Recognition_of_geometry (hG : PhanD4Geometry p f) :
    CFSG.ClassicalInvolution.Asc77.R31.PhanD4Recognition p f :=
  phanD4Recognition_of_universal (phanD4Universal_of_geometry hG)

end CFSG.ClassicalInvolution.PhanD4
