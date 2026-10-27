module

public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.LieType.SeitzGeneration.ExcTorusNeg
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

@[expose] def twE6TwelveWord : List (Fin TwistTag.E6.tag.rank) :=
  [1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5]

@[expose] def twE6TwelveMat : List (List ℤ) :=
  [[0, 0, 1, -1, 0, 0], [0, 1, 0, -1, 0, 0], [-1, 0, 1, -1, 0, 0], [-1, 1, 1, -1, -1, 0],
   [-1, 1, 1, -1, 0, -1], [-1, 1, 1, -1, 0, 0]]

@[expose] def twE6TwelveBasis : List (List ℤ) :=
  [[0, 1, -2, -2, 0, 2], [0, 0, 1, 0, 0, 0], [1, 1, -1, 0, 2, 2], [0, 0, 1, 0, 0, 1],
   [1, 0, 1, 2, 1, 0], [1, 1, -1, 1, 2, 2]]

@[expose] def twE6TwelveBasisInv : List (List ℤ) :=
  [[1, -1, 1, 0, 2, -2], [1, 4, -2, -2, 0, 2], [0, 1, 0, 0, 0, 0], [0, 0, -1, 0, 0, 1],
   [-1, 0, 1, 0, -1, 0], [0, -1, 0, 1, 0, 0]]

theorem twE6Twelve_wordMat :
    wordMat TwistTag.E6.tag twE6TwelveWord =
      toMat TwistTag.E6.tag.rank (lmul TwistTag.E6.tag.rank twE6TwelveMat twE6PermList) :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem twE6Twelve_pow : (toMat TwistTag.E6.tag.rank twE6TwelveMat) ^ 12 = 1 := by
  rw [← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat TwistTag.E6.tag.rank) (by decide +kernel)

theorem twE6Twelve_charpoly :
    (toMat TwistTag.E6.tag.rank twE6TwelveMat).charpoly =
      ([6, 12].map fun d => cyclotomic d ℤ).prod :=
  charpoly_of_basis twE6TwelveMat twE6TwelveBasis twE6TwelveBasisInv [6, 12]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_twistedE6_twelve
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 12) :
    SylowTorus (twistedE6RootGroup K σ) p 1 := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwelveWord) • x =
      toMat TwistTag.E6.tag.rank twE6TwelveMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Twelve_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (-1 : ZMod p) ≠ 1 := neg_one_ne_one_zmod hp (by omega)
  have he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = 12 := by
    have h := orderOf_neg_of_four_dvd he (by norm_num) (by norm_num)
    push_cast
    simpa using h
  have hΦ : ∀ x : ℤ, ((cyclotomic 12 ℤ).eval (-x)).natAbs =
      ((cyclotomic 12 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_twelve_eq]
    simp
    congr 1
    ring
  have h := sylowTorus_twistedE6_of_blocks hℓ hf K hK σ hσ hp _ hv [6, 12]
    twE6Twelve_charpoly (by norm_num) twE6Twelve_pow (Or.inl rfl) he (by norm_num) he' hΦ
    (by decide) (by decide) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
