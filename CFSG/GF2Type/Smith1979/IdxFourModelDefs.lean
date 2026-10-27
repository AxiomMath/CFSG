
module

public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

@[expose] def s12Rows : Array ℕ := #[2, 1, 4, 8, 16, 32, 128, 64, 256, 512, 1024, 2048]

@[expose] def s6Rows : Array ℕ := #[2, 4, 8, 16, 32, 1, 128, 256, 512, 1024, 2048, 64]

@[expose] def sigRows : Array ℕ := #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]

@[expose] def y3Rows : Array ℕ := #[7, 323, 197, 56, 2608, 1584, 448, 389, 387, 3584, 1576, 2584]

@[expose] def a3Rows : Array ℕ := #[2, 4, 1, 8, 16, 32, 128, 256, 64, 512, 1024, 2048]

@[expose] def a5Rows : Array ℕ := #[1, 4, 8, 16, 32, 2, 64, 256, 512, 1024, 2048, 128]

@[expose] def tRows : Array ℕ := #[62, 61, 59, 55, 47, 31, 3968, 3904, 3776, 3520, 3008, 1984]

@[expose] def tbarRows : Array ℕ := #[2, 1, 8, 4, 32, 16, 130, 65, 520, 260, 2080, 1040]

@[expose] def omegaRows : Array ℕ := #[64, 128, 256, 512, 1024, 2048, 65, 130, 260, 520, 1040, 2080]

@[expose] def d5Rows : List (Array ℕ) :=
  [#[64, 130, 4, 8, 16, 32, 65, 2, 256, 512, 1024, 2048],
   #[1, 128, 260, 8, 16, 32, 64, 130, 4, 512, 1024, 2048],
   #[1, 2, 256, 520, 16, 32, 64, 128, 260, 8, 1024, 2048],
   #[1, 2, 4, 512, 1040, 32, 64, 128, 256, 520, 16, 2048],
   #[1, 2, 4, 8, 1024, 2080, 64, 128, 256, 512, 1040, 32]]

@[expose] def m0Gens : List (Array ℕ) := [s12Rows, s6Rows, sigRows, y3Rows]

@[expose] def e0Gens : List (Array ℕ) := [a3Rows, a5Rows, y3Rows]

@[expose] def n0Gens : List (Array ℕ) := d5Rows ++ [s12Rows, s6Rows, sigRows]

@[expose] def M0 : Subgroup (V12 ≃ₗ[ZMod 2] V12) := Viol.genGrp m0Gens

@[expose] def E0 : Subgroup (V12 ≃ₗ[ZMod 2] V12) := Viol.genGrp e0Gens

@[expose] def N0 : Subgroup (V12 ≃ₗ[ZMod 2] V12) := Viol.genGrp n0Gens

end CFSG.GF2Type.Smith1979.IdxFour
