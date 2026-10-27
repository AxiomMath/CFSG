module

public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique

open scoped MatrixGroups

open CFSG.Assembly.LowTwoRank

theorem catalog_of_mulEquiv_psl {X : Type} [Group X] {n p f : ℕ} {K : Type} [Field K] [Finite K]
    (hadm : StatedLieAdmissible .PSL n p f) (hK : Nat.card K = p ^ f) (e : X ≃* PSL(n, K)) :
    CFSG.Blueprint.Catalog X :=
  Or.inr (Or.inr (Or.inl ⟨.PSL, n, p, f, hadm, K, inferInstance, inferInstance, hK,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj n K)⟩⟩))

theorem catalog_of_mulEquiv_psl_two_galoisField_two {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSL(2, GaloisField 2 f)) : CFSG.Blueprint.Catalog X := by
  have h4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  refine catalog_of_mulEquiv_psl ?_ (GaloisField.card 2 f (by omega)) e
  refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩ <;> intro h <;>
    simp only [Prod.mk.injEq] at h <;> generalize 2 ^ f = N at * <;> omega

theorem catalog_of_mulEquiv_psl_two_zmod {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 < p) (e : X ≃* PSL(2, ZMod p)) : CFSG.Blueprint.Catalog X := by
  have : Fact p.Prime := ⟨hp⟩
  refine catalog_of_mulEquiv_psl (p := p) (f := 1) ?_ (by rw [Nat.card_zmod, pow_one]) e
  refine ⟨hp, le_rfl, le_rfl, ?_, ?_⟩ <;> intro h <;>
    simp only [Prod.mk.injEq, pow_one] at h <;> omega

theorem catalog_of_mulEquiv_psl_three_zmod_three {X : Type} [Group X]
    (e : X ≃* PSL(3, ZMod 3)) : CFSG.Blueprint.Catalog X := by
  refine catalog_of_mulEquiv_psl (p := 3) (f := 1) ?_ (by rw [Nat.card_zmod, pow_one]) e
  refine ⟨Nat.prime_three, le_rfl, by norm_num, ?_, ?_⟩ <;> intro h <;>
    simp only [Prod.mk.injEq, pow_one] at h <;> omega

end CFSG.QuasithinUnique
