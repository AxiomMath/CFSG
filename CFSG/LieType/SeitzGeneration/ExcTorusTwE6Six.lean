module

public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

@[expose] def twE6SixWord : List (Fin TwistTag.E6.tag.rank) :=
  [1, 2, 4, 3, 5, 4, 3, 1, 2, 3, 4, 5]

@[expose] def twE6SixMat : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 1], [-1, 1, 1, -1, 0, 1], [-1, 0, 1, -1, 1, 1], [-2, 1, 1, -1, 1, 1],
   [-1, 1, 0, -1, 1, 1], [-1, 0, 0, 0, 0, 1]]

@[expose] def twE6SixBasis : List (List ℤ) :=
  [[-1, 1, 1, 1, -1, 0], [2, 2, 1, 3, 0, 0], [-2, -2, 1, 0, -1, -1], [0, 1, -1, 0, 0, 0],
   [-2, 2, -2, 0, -1, 0], [1, 2, 1, 0, 0, 1]]

@[expose] def twE6SixBasisInv : List (List ℤ) :=
  [[-6, 2, 3, -4, 3, 3], [3, -1, -1, 4, -2, -1], [3, -1, -1, 3, -2, -1], [1, 0, -1, -1, 0, -1],
   [12, -4, -6, 10, -7, -6], [-3, 1, 0, -7, 3, 1]]

theorem twE6Six_wordMat :
    wordMat TwistTag.E6.tag twE6SixWord =
      toMat TwistTag.E6.tag.rank (lmul TwistTag.E6.tag.rank twE6SixMat twE6PermList) :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem twE6Six_pow : (toMat TwistTag.E6.tag.rank twE6SixMat) ^ 6 = 1 := by
  rw [← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat TwistTag.E6.tag.rank) (by decide +kernel)

theorem twE6Six_charpoly :
    (toMat TwistTag.E6.tag.rank twE6SixMat).charpoly =
      ([6, 6, 6].map fun d => cyclotomic d ℤ).prod :=
  charpoly_of_basis twE6SixMat twE6SixBasis twE6SixBasisInv [6, 6, 6]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_twistedE6_six
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 6) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) • x =
      toMat TwistTag.E6.tag.rank twE6SixMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Six_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have hp3 : 3 < p := by omega
  have h := exists_elemAbelian_twistedE6_of_blocks hℓ hf K hK σ hσ hp hp3 _ hv [6, 6, 6]
    twE6Six_charpoly (by norm_num) twE6Six_pow (Or.inl rfl) he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
