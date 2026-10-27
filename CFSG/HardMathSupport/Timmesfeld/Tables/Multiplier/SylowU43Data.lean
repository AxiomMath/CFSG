module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.NineCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 Matrix

namespace U43Six

@[expose] def m1 : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, ⟨2, 0⟩, ⟨1, 2⟩;
    0, 0, ⟨2, 2⟩, ⟨2, 0⟩;
    0, 0, 0, 0;
    0, 0, 0, 0]

@[expose] def m2 : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    ⟨2, 0⟩, ⟨2, 1⟩, 0, 0;
    ⟨1, 1⟩, ⟨2, 0⟩, 0, 0]

@[expose] def tmat (s : F9) : Matrix (Fin 4) (Fin 4) F9 := 1 + s • m1 - (s ^ 3) • m2

theorem tmat_mul : ∀ s s' : F9, tmat s * tmat s' = tmat (s + s') := by decide +kernel

theorem tmat_zero : tmat 0 = 1 := by decide +kernel

theorem det_tmat : ∀ s : F9, (tmat s).det = 1 := by decide +kernel

theorem tmat_unitary : ∀ s : F9, ((tmat s).map (· ^ 3))ᵀ * tmat s = 1 := by decide +kernel

@[expose] def act (s : F9) (x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) :
    ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 :=
  (x.1 + (s.re ^ 2 + s.im ^ 2) * x.2.1 + s.im * x.2.2.1 - s.re * x.2.2.2, x.2.1,
    x.2.2.1 - s.im * x.2.1, x.2.2.2 + s.re * x.2.1)

theorem tmat_mul_rmat : ∀ (s : F9) (a b c d : ZMod 3),
    tmat s * rmat a b c d = rmat (act s (a, b, c, d)).1 (act s (a, b, c, d)).2.1
      (act s (a, b, c, d)).2.2.1 (act s (a, b, c, d)).2.2.2 * tmat s := by decide +kernel

theorem fixed_card_le : ∀ s : F9, s ≠ 0 →
    Fintype.card {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // act s x = x} ≤ 9 := by decide +kernel

theorem tmat_ne_scalar_rmat : ∀ (s c : F9) (a b d e : ZMod 3),
    tmat s = c • rmat a b d e → s = 0 := by decide +kernel
end U43Six

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
