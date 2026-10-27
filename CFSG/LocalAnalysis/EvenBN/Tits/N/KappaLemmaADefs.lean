module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.ParrottCert

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA

open Matrix CFSG.LocalAnalysis.EvenBN.Tits.Model

abbrev W4 : Type := Fin 4 → ZMod 2

@[expose] def idx3 (i k l : Fin 4) : Fin 64 := ⟨16 * i.val + 4 * k.val + l.val, by omega⟩

@[expose] def betaT (T : Fin 64 → ZMod 2) (a b : W4) : W4 :=
  fun i => ∑ k, ∑ l, T (idx3 i k l) * a k * b l

@[expose] def basisV (j : Fin 5) : ℕ := 12 - j.val

@[expose] noncomputable def prodE (c : Fin 5 → ZMod 2) : Equiv.Perm (Fin 1755) :=
  parrottV 12 ^ (c 0).val * parrottV 11 ^ (c 1).val * parrottV 10 ^ (c 2).val *
    parrottV 9 ^ (c 3).val * parrottV 8 ^ (c 4).val

@[expose] def b0 : W4 := ![0, 0, 0, 1]

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA
