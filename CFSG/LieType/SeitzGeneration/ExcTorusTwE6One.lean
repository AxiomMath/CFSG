module

public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

@[expose] def twE6OneWord : List (Fin TwistTag.E6.tag.rank) :=
  [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0]

@[expose] def twE6OneMat : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0], [-1, 1, 0, 0, 0, -1], [-2, 0, 1, 0, 0, -1], [-2, 0, 0, 1, 0, -2],
   [-1, 0, 0, 0, 1, -2], [0, 0, 0, 0, 0, -1]]

@[expose] def twE6OneBasis : List (List ℤ) :=
  [[0, 0, 0, 0, -2, 1], [0, 1, 1, -1, -1, -1], [-1, -2, 1, 1, -1, 2], [2, 1, -1, 0, -1, 2],
   [-2, 1, -2, -1, 2, -2], [0, 0, 0, 0, -1, 0]]

@[expose] def twE6OneBasisInv : List (List ℤ) :=
  [[-8, 2, 3, 3, 1, 10], [19, -5, -8, -7, -3, -24], [5, -1, -2, -2, -1, -7],
   [23, -7, -10, -9, -4, -28], [0, 0, 0, 0, 0, -1], [1, 0, 0, 0, 0, -2]]

theorem twE6One_wordMat :
    wordMat TwistTag.E6.tag twE6OneWord =
      toMat TwistTag.E6.tag.rank (lmul TwistTag.E6.tag.rank twE6OneMat twE6PermList) :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem twE6One_pow : (toMat TwistTag.E6.tag.rank twE6OneMat) ^ 2 = 1 := by
  rw [← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat TwistTag.E6.tag.rank) (by decide +kernel)

theorem twE6One_charpoly :
    (toMat TwistTag.E6.tag.rank twE6OneMat).charpoly =
      ([1, 1, 1, 1, 2, 2].map fun d => cyclotomic d ℤ).prod :=
  charpoly_of_basis twE6OneMat twE6OneBasis twE6OneBasisInv [1, 1, 1, 1, 2, 2]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_twistedE6_one
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 1) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) • x =
      toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have h := exists_elemAbelian_twistedE6_of_blocks hℓ hf K hK σ hσ hp hp3 _ hv [1, 1, 1, 1, 2, 2]
    twE6One_charpoly (by norm_num) twE6One_pow (Or.inr (by decide)) he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
