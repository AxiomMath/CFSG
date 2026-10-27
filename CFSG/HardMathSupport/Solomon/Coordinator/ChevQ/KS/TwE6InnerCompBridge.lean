module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqKac
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint TwE6UniqAbs

namespace TwE6InnerAbs

section Arith

variable {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {ζ : Lˣ} {w : WeylGroup Tag.E6}
  {m0 m1 m2 m3 m4 m5 : Fin 4}

theorem inner_mod_three (hζ : IsPrimitiveRoot (ζ : L) 3)
    (hchar : ∀ β, rootChar a β = ζ ^ dotμ (w • β) ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ)
      ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ) ((m5 : ℕ) : ℤ))
    (hin : rootChar a CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3 = 1) :
    (4 * m0.val + 3 * m1.val + 5 * m2.val + 6 * m3.val + 4 * m4.val + 2 * m5.val) % 3 = 0 := by
  have hζu : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have h1 := hchar CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3
  rw [hin] at h1
  have h2 : ((3 : ℕ) : ℤ) ∣ dotμ (w • CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3)
      ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ) := (hζu.zpow_eq_one_iff_dvd _).1 h1.symm
  have hw : ∀ j, (((w • CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3) j : ℤ) : ZMod 3) =
      ((CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3 j : ℤ) : ZMod 3) := fun j => by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := CFSG.HardMathSupport.Timmesfeld.CrossChar.three_dvd_smul_e6Omega3_sub w j
    exact (dvd_sub_comm).1 this
  have h3 : ((dotμ (w • CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3)
      ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ) : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 h2
  simp only [dotμ, Int.cast_add, Int.cast_mul, hw] at h3
  have h4 : ((4 * m0.val + 3 * m1.val + 5 * m2.val + 6 * m3.val + 4 * m4.val + 2 * m5.val : ℕ) :
      ZMod 3) = 0 := by
    push_cast
    simpa [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3] using h3
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ 3).1 h4)

theorem exists_ne_zero_of_ne_one (hζ : IsPrimitiveRoot (ζ : L) 3)
    (hchar : ∀ β, rootChar a β = ζ ^ dotμ (w • β) ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ)
      ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ) ((m5 : ℕ) : ℤ))
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) :
    m0.val % 3 ≠ 0 ∨ m1.val % 3 ≠ 0 ∨ m2.val % 3 ≠ 0 ∨ m3.val % 3 ≠ 0 ∨ m4.val % 3 ≠ 0 ∨
      m5.val % 3 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hcon
  have hζu : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hd : ∀ (n : Fin 4), n.val % 3 = 0 → ((3 : ℕ) : ℤ) ∣ ((n : ℕ) : ℤ) := fun n hn => by
    exact_mod_cast Nat.dvd_of_mod_eq_zero hn
  have hall : ∀ β, rootChar a β = 1 := fun β => by
    rw [hchar β]
    refine (hζu.zpow_eq_one_iff_dvd _).2 ?_
    simp only [dotμ]
    exact dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (Dvd.dvd.mul_left (hd m0 c0) _)
      (Dvd.dvd.mul_left (hd m1 c1) _)) (Dvd.dvd.mul_left (hd m2 c2) _))
        (Dvd.dvd.mul_left (hd m3 c3) _)) (Dvd.dvd.mul_left (hd m4 c4) _))
          (Dvd.dvd.mul_left (hd m5 c5) _)
  apply h1
  have ha : a = 1 := by
    funext j
    have h := hall (Pi.single j 1)
    rw [rootChar, Finset.prod_eq_single j (fun b _ hb => by
      rw [Pi.single_eq_of_ne hb, zpow_zero]) (fun h => absurd (Finset.mem_univ _) h)] at h
    simpa using h
  rw [ha]
  exact rootDiagUnit_one

end Arith

end TwE6InnerAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
