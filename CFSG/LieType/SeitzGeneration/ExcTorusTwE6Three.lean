module

public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.LieType.SeitzGeneration.ExcTorusNeg
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

@[expose] def twE6ThreeWord : List (Fin TwistTag.E6.tag.rank) :=
  [0, 1, 2, 3, 1, 2, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4]

@[expose] def twE6ThreeMat : List (List ℤ) :=
  [[1, 0, -1, 0, 0, 0], [1, 1, -1, 0, 0, -1], [2, 1, -2, 0, 0, 0], [2, 2, -2, -1, 1, -1],
   [1, 2, -1, -1, 0, 0], [0, 1, -1, 0, 0, 0]]

@[expose] def twE6ThreeBasis : List (List ℤ) :=
  [[0, 1, -1, 1, 2, 3], [0, 1, -1, 1, 2, 4], [-1, 2, -2, 1, -1, 8], [2, -2, 1, 0, 1, 6],
   [-2, -1, 0, -2, -2, 6], [0, 1, -1, 1, 1, 3]]

@[expose] def twE6ThreeBasisInv : List (List ℤ) :=
  [[14, -9, 3, 1, -1, -10], [2, 2, 2, 0, -1, -8], [-19, 16, -2, -1, 0, 5],
   [-19, 11, -4, -1, 1, 15], [1, 0, 0, 0, 0, -1], [-1, 1, 0, 0, 0, 0]]

theorem twE6Three_wordMat :
    wordMat TwistTag.E6.tag twE6ThreeWord =
      toMat TwistTag.E6.tag.rank (lmul TwistTag.E6.tag.rank twE6ThreeMat twE6PermList) :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem twE6Three_pow : (toMat TwistTag.E6.tag.rank twE6ThreeMat) ^ 6 = 1 := by
  rw [← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat TwistTag.E6.tag.rank) (by decide +kernel)

theorem twE6Three_charpoly :
    (toMat TwistTag.E6.tag.rank twE6ThreeMat).charpoly =
      ([3, 3, 6].map fun d => cyclotomic d ℤ).prod :=
  charpoly_of_basis twE6ThreeMat twE6ThreeBasis twE6ThreeBasisInv [3, 3, 6]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_twistedE6_three
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 3) :
    SylowTorus (twistedE6RootGroup K σ) p 2 := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6ThreeWord) • x =
      toMat TwistTag.E6.tag.rank twE6ThreeMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Three_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (-1 : ZMod p) ≠ 1 := neg_one_ne_one_zmod hp (by omega)
  have he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = 6 := by
    have h := orderOf_neg_of_odd h1 he (by decide) (by norm_num)
    push_cast
    simpa using h
  have hΦ : ∀ x : ℤ, ((cyclotomic 6 ℤ).eval (-x)).natAbs =
      ((cyclotomic 3 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_six_eq, cyclotomic_three_eq]
    simp
  have h := sylowTorus_twistedE6_of_blocks hℓ hf K hK σ hσ hp _ hv [3, 3, 6]
    twE6Three_charpoly (by norm_num) twE6Three_pow (Or.inr (by decide)) he (by norm_num) he' hΦ
    (by decide) (by decide) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
