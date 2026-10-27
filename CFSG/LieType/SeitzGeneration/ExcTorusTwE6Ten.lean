module

public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.LieType.SeitzGeneration.ExcTorusNeg
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

@[expose] def twE6TenWord : List (Fin TwistTag.E6.tag.rank) :=
  [0, 1, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0]

@[expose] def twE6TenMat : List (List ℤ) :=
  [[1, 0, -1, 0, 0, 0], [0, -1, 0, 0, 0, 0], [1, -1, -1, 1, -1, 0], [0, -1, -1, 1, -1, 0],
   [0, -1, -1, 1, 0, -1], [0, 0, 0, 0, 0, -1]]

@[expose] def twE6TenBasis : List (List ℤ) :=
  [[2, -1, 0, 1, 0, 1], [9, -5, -1, 1, -1, 1], [4, -2, -1, 1, -1, 1], [6, -3, -1, 1, -2, 1],
   [-1, 1, 0, 1, -1, 0], [-8, 5, 0, 0, 0, 0]]

@[expose] def twE6TenBasisInv : List (List ℤ) :=
  [[0, 5, -5, 0, 0, 3], [0, 8, -8, 0, 0, 5], [1, 0, -2, 1, 0, 0], [0, -1, 2, -1, 1, -1],
   [0, 2, -1, -1, 0, 1], [1, -1, 0, 1, -1, 0]]

theorem twE6Ten_wordMat :
    wordMat TwistTag.E6.tag twE6TenWord =
      toMat TwistTag.E6.tag.rank (lmul TwistTag.E6.tag.rank twE6TenMat twE6PermList) :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem twE6Ten_pow : (toMat TwistTag.E6.tag.rank twE6TenMat) ^ 10 = 1 := by
  rw [← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat TwistTag.E6.tag.rank) (by decide +kernel)

theorem twE6Ten_charpoly :
    (toMat TwistTag.E6.tag.rank twE6TenMat).charpoly =
      ([2, 2, 10].map fun d => cyclotomic d ℤ).prod :=
  charpoly_of_basis twE6TenMat twE6TenBasis twE6TenBasisInv [2, 2, 10]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_twistedE6_ten
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 10) :
    SylowTorus (twistedE6RootGroup K σ) p 1 := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6TenWord) • x =
      toMat TwistTag.E6.tag.rank twE6TenMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Ten_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (-1 : ZMod p) ≠ 1 := neg_one_ne_one_zmod hp (by omega)
  have he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = 5 := by
    have h := orderOf_neg_of_two_mod_four he (by norm_num)
    push_cast
    simpa using h
  have hΦ : ∀ x : ℤ, ((cyclotomic 5 ℤ).eval (-x)).natAbs =
      ((cyclotomic 10 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_five_eq, cyclotomic_ten_eq]
    simp
    congr 1
    ring
  have h := sylowTorus_twistedE6_of_blocks hℓ hf K hK σ hσ hp _ hv [2, 2, 10]
    twE6Ten_charpoly (by norm_num) twE6Ten_pow (Or.inl rfl) he (by norm_num) he' hΦ
    (by decide) (by decide) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
