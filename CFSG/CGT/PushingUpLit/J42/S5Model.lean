module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.PushingUpLit.SolK

@[expose] def extraMul (i j : ℕ) : ℕ :=
  (i ^^^ j) ^^^ ((((i >>> 3) &&& (j >>> 1) &&& 1) ^^^ ((i >>> 4) &&& j &&& 1)) <<< 2)

@[expose] def extraMulFin (i j : Fin 32) : Fin 32 :=
  ⟨extraMul i j % 32, Nat.mod_lt _ (by norm_num)⟩

structure ExtraData (K : Type*) [Group K] where
  nf : Fin 32 → K
  nf_inj : Function.Injective nf
  nf_mul : ∀ i j : Fin 32, nf i * nf j = nf (extraMulFin i j)
  nf_conj : ∀ (k : K) (i : Fin 32), ∃ j : Fin 32, k * nf i * k⁻¹ = nf j
  nf_cent : ∀ k : K, (∀ i : Fin 32, k * nf i = nf i * k) → ∃ i : Fin 32, k = nf i

end CFSG.CGT.PushingUpLit.SolK
