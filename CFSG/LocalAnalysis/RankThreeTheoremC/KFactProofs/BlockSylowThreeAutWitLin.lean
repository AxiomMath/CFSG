module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutWitCommon

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

namespace WitLin

def orderNineBlock : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0]

theorem orderNineBlock_pow_nine : orderNineBlock ^ 9 = 1 := by decide +kernel

theorem orderNineBlock_pow_three_ne_one : orderNineBlock ^ 3 ≠ 1 := by decide +kernel

theorem orderOf_orderNineBlock : orderOf orderNineBlock = 9 := by
  have h := orderOf_eq_prime_pow (p := 3) (n := 1) (x := orderNineBlock)
    (by simpa using orderNineBlock_pow_three_ne_one) (by simpa using orderNineBlock_pow_nine)
  simpa using h

section Extend

variable {R : Type} [CommRing R]

def extendByOne (m : ℕ) :
    Matrix (Fin 6) (Fin 6) R →* Matrix (Fin (6 + m)) (Fin (6 + m)) R where
  toFun A := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 1)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' A B := by
    simp [Matrix.reindex_apply, Matrix.fromBlocks_multiply, Matrix.submatrix_mul_equiv]

theorem extendByOne_injective (m : ℕ) : Function.Injective (extendByOne (R := R) m) := by
  intro A B h
  have h' := (Matrix.reindex (finSumFinEquiv : Fin 6 ⊕ Fin m ≃ Fin (6 + m))
    finSumFinEquiv).injective h
  exact (Matrix.fromBlocks_inj.1 h').1

end Extend

theorem exists_gl_orderOf_eq_nine {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 6 ≤ n) : ∃ g : GL (Fin n) K, orderOf g = 9 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hcard
  let u : GL (Fin 6) (ZMod 2) := Units.ofPowEqOne orderNineBlock 9 orderNineBlock_pow_nine
    (by norm_num)
  refine ⟨Units.map (extendByOne m) (Matrix.GeneralLinearGroup.map (e : ZMod 2 →+* K) u), ?_⟩
  have h1 : Function.Injective
      (Units.map (extendByOne (R := K) m : Matrix (Fin 6) (Fin 6) K →* _)) :=
    Units.map_injective (extendByOne_injective m)
  have h2 : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin 6) (e : ZMod 2 →+* K)) :=
    Units.map_injective (Matrix.map_injective e.injective)
  rw [orderOf_injective _ h1, orderOf_injective _ h2, ← orderOf_units, Units.val_ofPowEqOne]
  exact orderOf_orderNineBlock

theorem det_eq_one_of_card_two {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) (g : GL ι K) : (g : Matrix ι ι K).det = 1 := by
  have := subsingleton_units_of_card_two hK
  rw [← Matrix.GeneralLinearGroup.val_det_apply,
    Subsingleton.elim (Matrix.GeneralLinearGroup.det g) 1, Units.val_one]

end WitLin

theorem exists_orderOf_eq_nine_psl_two {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSL n 2 1) (hn : 6 ≤ n) :
    ∃ x : X, orderOf x = 9 := by
  obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  obtain ⟨g, hg⟩ := WitLin.exists_gl_orderOf_eq_nine hK hn
  have hmem : g ∈ StatedSL n K := Subgroup.subset_closure (WitLin.det_eq_one_of_card_two hK g)
  exact exists_orderOf_eq_of_equiv_statedProj hK e ⟨g, hmem⟩
    (by rw [Subgroup.orderOf_mk]; exact hg)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
