module

public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.LieType.SeitzGeneration.ExcTorusNeg
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

@[expose] def twE6EighteenWord : List (Fin TwistTag.E6.tag.rank) :=
  [1, 2, 0, 3, 1, 2, 0, 4, 3, 1, 2, 0, 3, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3]

@[expose] def twE6EighteenMat : List (List ℤ) :=
  [[0, 1, 0, -1, 1, -1], [0, 1, 0, -1, 0, 0], [-1, 1, 0, -1, 1, -1], [-1, 2, 0, -2, 1, 0],
   [0, 1, -1, -1, 1, 0], [0, 0, 0, -1, 1, 0]]

@[expose] def twE6EighteenBasis : List (List ℤ) :=
  [[0, 0, 0, -1, 1, 0], [-1, -1, 1, 0, 0, -1], [0, 0, 0, -1, 2, -1], [0, -2, 1, 0, 1, -2],
   [0, -1, 0, 0, 1, -2], [-1, 0, 1, -1, 0, 0]]

@[expose] def twE6EighteenBasisInv : List (List ℤ) :=
  [[-1, -2, 0, 1, 0, 1], [-2, -1, 1, 0, 0, 1], [-2, -1, 1, 1, -1, 1], [-1, 1, 1, 0, -1, -1],
   [0, 1, 1, 0, -1, -1], [1, 1, 0, 0, -1, -1]]

theorem twE6Eighteen_wordMat :
    wordMat TwistTag.E6.tag twE6EighteenWord =
      toMat TwistTag.E6.tag.rank (lmul TwistTag.E6.tag.rank twE6EighteenMat twE6PermList) :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem twE6Eighteen_pow : (toMat TwistTag.E6.tag.rank twE6EighteenMat) ^ 18 = 1 := by
  rw [← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat TwistTag.E6.tag.rank) (by decide +kernel)

theorem twE6Eighteen_charpoly :
    (toMat TwistTag.E6.tag.rank twE6EighteenMat).charpoly =
      ([18].map fun d => cyclotomic d ℤ).prod :=
  charpoly_of_basis twE6EighteenMat twE6EighteenBasis twE6EighteenBasisInv [18]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_twistedE6_eighteen
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 18) :
    SylowTorus (twistedE6RootGroup K σ) p 1 := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6EighteenWord) • x =
      toMat TwistTag.E6.tag.rank twE6EighteenMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Eighteen_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (-1 : ZMod p) ≠ 1 := neg_one_ne_one_zmod hp (by omega)
  have he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = 9 := by
    have h := orderOf_neg_of_two_mod_four he (by norm_num)
    push_cast
    simpa using h
  have hΦ : ∀ x : ℤ, ((cyclotomic 9 ℤ).eval (-x)).natAbs =
      ((cyclotomic 18 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_nine_eq, cyclotomic_eighteen_eq]
    simp
    congr 1
    ring
  have h := sylowTorus_twistedE6_of_blocks hℓ hf K hK σ hσ hp _ hv [18]
    twE6Eighteen_charpoly (by norm_num) twE6Eighteen_pow (Or.inl rfl) he (by norm_num) he' hΦ
    (by decide) (by decide) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
