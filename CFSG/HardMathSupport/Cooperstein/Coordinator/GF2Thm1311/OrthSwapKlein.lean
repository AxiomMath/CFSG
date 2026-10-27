module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthSwap
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthKlein
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.LinearFour
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.SwapExists

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.OutStructure CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem exists_hermitian_seven {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) :
    ∃ M M' : Matrix (Fin 3) (Fin 3) K, (M'.map σ)ᵀ = M' ∧ (M.map σ)ᵀ = M ∧ M * M' = 1 ∧
      M ^ 7 = 1 ∧ ∀ c : K, M ≠ Matrix.scalar (Fin 3) c := by
  classical
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  obtain ⟨hT, h7, -, h01⟩ := symm3_spec
  have hσι : ∀ x : ZMod 2, σ (ι x) = ι x := fun x => by
    have := RingHom.ext_zmod ((σ : K →+* K).comp ι) ι
    exact congrArg (fun f => f x) this
  have hmapσ : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), ((A.map ι).map σ) = A.map ι := by
    intro A
    ext i j
    simp [Matrix.map_apply, hσι]
  have hsymm6 : (symm3 ^ 6)ᵀ = symm3 ^ 6 := by rw [Matrix.transpose_pow, hT]
  refine ⟨symm3.map ι, (symm3 ^ 6).map ι, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmapσ, ← Matrix.transpose_map, hsymm6]
  · rw [hmapσ, ← Matrix.transpose_map, hT]
  · have := congrArg (ι.mapMatrix) (show symm3 * symm3 ^ 6 = 1 by rw [← pow_succ']; exact h7)
    simpa [RingHom.mapMatrix_apply, Matrix.map_mul] using this
  · have := congrArg (ι.mapMatrix) h7
    simpa [RingHom.mapMatrix_apply, map_pow] using this
  · intro c h
    have := congrFun (congrFun h 0) 1
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply] at this
    simp [Matrix.map_apply, h01] at this

theorem kleinBigInv_orth_swap {K : Type} [Field K] [Fintype K] [CharP K 2] {d : ℕ}
    (hK4 : Nat.card K = 4)
    (Q : QuadraticForm K (Fin d → K)) (hd : 8 ≤ d)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    (hconj : ∀ B : Subgroup (MulAut (matrixProjectiveDerived Q)),
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) → Nat.card B = 4 →
        B ⊓ Inn (matrixProjectiveDerived Q) = ⊥ →
        ∃ β : MulAut (matrixProjectiveDerived Q), ∀ b ∈ B, β * b * β⁻¹ ∈ matrixProjectiveImage Q)
    :
    KleinBigInv (matrixProjectiveDerived Q) := by
  classical
  intro B hcomm hsq hcard hinn
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [← Nat.card_eq_fintype_card] at hf; exact hf
  have hR := evenOrthogonalRealization_of_regular f.pos hK (by omega) Q hQ hT hE
  obtain ⟨hZ, -, -, huniq, -, -, -, -, hinv⟩ := hR
  have hQ0 : ∃ v, Q v ≠ 0 := exists_ne_zero_of_polar_nondegenerate (by omega) hQ
  obtain ⟨β, hβ⟩ := hconj B hcomm hsq hcard hinn
  set P := matrixProjectiveDerived Q with hP
  let B' : Subgroup (MulAut P) := B.map (MulAut.conj β).toMonoidHom
  have hB'mem : ∀ α' ∈ B', ∃ b ∈ B, α' = β * b * β⁻¹ := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, hb, by simp [MulAut.conj_apply]⟩
  have hB'E : ∀ α' ∈ B', α' ∈ matrixProjectiveImage Q := by
    intro α' hα'
    obtain ⟨b, hb, rfl⟩ := hB'mem α' hα'
    exact hβ b hb
  have hB'comm : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hB'sq : ∀ a ∈ B', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  have hB'card : Nat.card B' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj β).injective]; exact hcard
  have hB'inn : B' ⊓ Inn P = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rintro _ ⟨hα', hI⟩
    obtain ⟨b, hb, rfl⟩ := hB'mem _ hα'
    have hnorm : (Inn P).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal P
    have hbI : b ∈ Inn P := by
      have := hnorm.conj_mem _ hI β⁻¹
      simpa [mul_assoc] using this
    have : b ∈ B ⊓ Inn P := ⟨hb, hbI⟩
    rw [hinn] at this
    have hb1 : b = 1 := by simpa using this
    rw [hb1]; simp
  obtain ⟨α', hα'B, hα'D⟩ : ∃ α' ∈ B', α' ∉ orthD Q := by
    by_contra hall
    push Not at hall
    have hrel := CFSG.RankThree.PartOne.KLC.relIndex_inner_orthD_le_two Q hQ0 hab
    have hle : B' ≤ orthD Q := fun a ha => hall a ha
    have : Finite (MulAut P) := inferInstance
    have hcardD : Nat.card (B'.subgroupOf (orthD Q)) = 4 := by
      rw [← hB'card]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    obtain ⟨b, ⟨hbB, hbI⟩, hb1⟩ := exists_mem_inf_of_index_le_two (B'.subgroupOf (orthD Q))
      ((Inn P).subgroupOf (orthD Q)) hrel (by omega)
    have h1 : (b : MulAut P) ∈ B' ⊓ Inn P := ⟨hbB, hbI⟩
    rw [hB'inn] at h1
    exact hb1 (Subtype.ext (by simpa using h1))
  obtain ⟨g, ⟨hg, hgκ⟩, -⟩ := huniq α' (hB'E α' hα'B)
  have hα'sq := hB'sq α' hα'B
  have hα'1 : α' ≠ 1 := fun h => hα'D (h ▸ (orthD Q).one_mem)
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf α' = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hα'sq) hα'1
  obtain ⟨hgg, -, hcase⟩ := hinv α' (hB'E α' hα'B) hord g hg hgκ
  have hσ1 : g.val.right ≠ 1 := by
    intro h1
    apply hα'D
    exact (mem_orthD_iff Q α').mpr ⟨⟨g, (mem_linearSimilarityPairs_iff Q g).mpr h1⟩, hgκ⟩
  have hσσ' : g.val.right * g.val.right = 1 := by
    have := congrArg (fun x : similarityPairs Q => x.val.right) hgg
    simpa using this
  have hσσ : ∀ x, g.val.right (g.val.right x) = x := fun x => by
    rw [← RingAut.mul_apply, hσσ']; rfl
  obtain ⟨hfe, hσpow⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution
    f.pos hK hσ1 hσσ'
  have hf2 : (f : ℕ) = 2 := by
    have h4 : 2 ^ (f : ℕ) = 2 ^ 2 := by rw [← hK, hK4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h4
  have hσsq : ∀ x, g.val.right x = x ^ 2 := by
    intro x
    rw [hσpow x, hf2]
    norm_num
  have hTQ : ∀ v, Q (coordSemilinear g.val v) = g.val.right (Q v) := fun v =>
    (mem_unitMultiplierPairs_iff Q g).mp hg v
  have hTT : ∀ v, coordSemilinear g.val (coordSemilinear g.val v) = v := by
    intro v
    have h1 := coordinateSemilinearMap_mul g.val g.val v
    have h2 : g.val * g.val = 1 := congrArg Subtype.val hgg
    rw [h2, coordinateSemilinearMap_one] at h1
    exact h1.symm
  have hfr := exists_swap_frame hK4 hσsq hQ hTT hTQ 3 (by rw [Module.finrank_fin_fun]; omega)
  obtain ⟨F, hF⟩ := hfr
  obtain ⟨M, M', hN, hN', hMM', hM7, hns⟩ := exists_hermitian_seven g.val.right
  have hbig := bigInv_of_swapframe Q g hgg hZ hab hσσ hTQ F hF (p := 7) (by norm_num)
    (Or.inr rfl) M M' hN hN' hMM' hM7 hns
  rw [hgκ] at hbig
  obtain ⟨b, hb, rfl⟩ := hB'mem α' hα'B
  exact ⟨b, hb, BigInv.of_conj β b hbig⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
