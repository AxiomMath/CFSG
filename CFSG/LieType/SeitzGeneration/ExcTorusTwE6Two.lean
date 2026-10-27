module

public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

@[expose] def twE6TwoWord : List (Fin TwistTag.E6.tag.rank) :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
   4, 3, 2, 0]

@[expose] def twE6TwoMat : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0], [0, 0, 0, -1, 0, 0],
   [0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, -1]]

@[expose] def twE6TwoBasis : List (List ℤ) :=
  [[-1, 1, 0, -2, 1, 0], [2, 1, -1, -2, -2, -1], [-2, 1, 2, 2, 2, 0], [0, -1, -2, -2, -1, 0],
   [-2, -2, 0, 1, 1, 1], [1, 1, -2, -1, 1, 0]]

@[expose] def twE6TwoBasisInv : List (List ℤ) :=
  [[1, 10, 0, -7, 10, 2], [-2, -22, -1, 14, -22, -4], [1, 7, 0, -5, 7, 1], [-1, -6, 0, 4, -6, -1],
   [2, 20, 1, -13, 20, 4], [-3, -38, -3, 23, -37, -7]]

theorem twE6Two_wordMat :
    wordMat TwistTag.E6.tag twE6TwoWord =
      toMat TwistTag.E6.tag.rank (lmul TwistTag.E6.tag.rank twE6TwoMat twE6PermList) :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem twE6Two_pow : (toMat TwistTag.E6.tag.rank twE6TwoMat) ^ 2 = 1 := by
  rw [← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat TwistTag.E6.tag.rank) (by decide +kernel)

theorem twE6Two_charpoly :
    (toMat TwistTag.E6.tag.rank twE6TwoMat).charpoly =
      ([2, 2, 2, 2, 2, 2].map fun d => cyclotomic d ℤ).prod :=
  charpoly_of_basis twE6TwoMat twE6TwoBasis twE6TwoBasisInv [2, 2, 2, 2, 2, 2]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_twistedE6_two
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 2) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E ∧ Nat.card E = p ^ 6 := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord) • x =
      toMat TwistTag.E6.tag.rank twE6TwoMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have h := exists_elemAbelian_twistedE6_of_blocks hℓ hf K hK σ hσ hp hp3 _ hv [2, 2, 2, 2, 2, 2]
    twE6Two_charpoly (by norm_num) twE6Two_pow (Or.inl rfl) he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
