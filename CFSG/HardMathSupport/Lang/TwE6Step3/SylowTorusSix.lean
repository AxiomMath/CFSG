module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow

public section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge Polynomial
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix


theorem sylowTorus_twistedE6_six {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 6) :
    SylowTorus (twistedE6RootGroup K σ) p 3 := by
  have hp3 : 3 < p := by omega
  have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
  rw [show ennola 6 = 3 by decide] at he'
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) • x =
      toMat TwistTag.E6.tag.rank twE6SixMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Six_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hΦ : ∀ x : ℤ, ((cyclotomic 3 ℤ).eval (-x)).natAbs =
      ((cyclotomic 6 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_six_eq, cyclotomic_three_eq]
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
    congr 1
    ring
  exact sylowTorus_twistedE6_of_blocks_of_three_lt hℓ hf K hK σ hσ hp hp3 hpq _ hv
    [6, 6, 6] twE6Six_charpoly (by norm_num) twE6Six_pow (Or.inr (by decide)) he he'
    hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)

end CFSG.HardMathSupport.Lang.TwE6Step3
