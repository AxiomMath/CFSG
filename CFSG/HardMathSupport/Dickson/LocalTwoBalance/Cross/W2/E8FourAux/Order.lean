module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix


theorem exists_lang_conjugator_E8 (K : Type) [Field K] [Finite K] (w : WeylGroup Tag.E8) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup Tag.E8 (AlgebraicClosure K),
        Units.map (entrywiseHom Fr) g0 =
          g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator Tag.E8 K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  exact ⟨Fr, hFr, g0, hg0C, hg0⟩

theorem card_twistedTorus_E8_four (K : Type) [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    Nat.card (twistedTorus (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K)
        e8PhiFourWeyl) Fr) =
      ((wordMat Tag.E8 e8FourWord).charpoly.eval (Nat.card K : ℤ)).natAbs := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := wordMat Tag.E8 e8FourWord with hM
  have hw : ∀ u, e8PhiFourWeyl • u = M *ᵥ u := wordProd_smul_eq_wordMat_mulVec Tag.E8 e8FourWord
  have hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 :=
    charpoly_eval_ne_zero_of_blocks Finite.one_lt_card _ e8Four_charpoly
  have hT0 : twistedTorus (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K)
      e8PhiFourWeyl) Fr = (fixedCharTuples M Fr).map (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
      refine ⟨a, ?_, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
      exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
    · rintro ⟨a, ha, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr] at ha
      exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a,
        mem_twistedFixedTuples_iff_conj.1 ha⟩
  set B : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
    M - (Nat.card K : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval (Nat.card K : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ hℓq M (n := 4) (by norm_num) e8Four_pow
  rw [hT0, Subgroup.card_map_of_injective CFSG.LieType.Chevalley.rootDiagUnit_injective,
    natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]

theorem factorization_card_torus_E8_four (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K ^ 2 + 1) :
    (((wordMat Tag.E8 e8FourWord).charpoly.eval (Nat.card K : ℤ)).natAbs).factorization 5 =
      4 * (Nat.card K ^ 4 - 1).factorization 5 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have he := orderOf_natCast_zmod_five_of_dvd_sq_add_one h5
  have h2 := ordProj_charpoly_eval_of_blocks Nat.prime_five le_rfl hq2 he (by norm_num) _
    e8Four_charpoly (by decide)
  have h3 : [4, 4, 4, 4].count 4 = 4 := by decide
  rw [h3, ← pow_mul] at h2
  rw [Nat.pow_right_injective (by norm_num : 2 ≤ 5) h2, mul_comm]

theorem factorization_card_adjointE8_eq_torus_add_one (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K ^ 2 + 1) :
    (Nat.card (adjointGroup Tag.E8 K)).factorization 5 =
      (((wordMat Tag.E8 e8FourWord).charpoly.eval (Nat.card K : ℤ)).natAbs).factorization 5 + 1 := by
  rw [factorization_five_card_adjointGroup_E8_of_dvd_sq_add_one K h5,
    factorization_card_torus_E8_four K h5]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
