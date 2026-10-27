module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.FrobSum
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKlein
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthProj
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.RankThree.PartOne.KLC.D4OutCentral

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.OutStructure CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem kleinBigInv_orth_of_negSum {K : Type} [Field K] [Fintype K] [CharP K 2] {d : ℕ}
    (hK4 : Nat.card K = 4)
    (Q : QuadraticForm K (Fin d → K)) (hd : 1 ≤ d)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    (hconj : ∀ B : Subgroup (MulAut (matrixProjectiveDerived Q)),
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) → Nat.card B = 4 →
        B ⊓ Inn (matrixProjectiveDerived Q) = ⊥ →
        ∃ β : MulAut (matrixProjectiveDerived Q), ∀ b ∈ B, β * b * β⁻¹ ∈ matrixProjectiveImage Q)
    (hS : ∑ v : (Fin d → K), chi (Q v) < 0) :
    KleinBigInv (matrixProjectiveDerived Q) := by
  classical
  intro B hcomm hsq hcard hinn
  exfalso
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [← Nat.card_eq_fintype_card] at hf; exact hf
  have hR := evenOrthogonalRealization_of_regular f.pos hK hd Q hQ hT hE
  obtain ⟨hZ, -, -, huniq, -, -, -, -, hinv⟩ := hR
  have hQ0 : ∃ v, Q v ≠ 0 := exists_ne_zero_of_polar_nondegenerate hd hQ
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
  have hpos := sum_chi_pos hK4 Q (g.val.right : K →+* K) hσsq (coordSemilinear g.val) hTT
    (fun v => by rw [hTQ]; exact hσsq _)
    (fun w hw => hQ.1 w (fun y => by
      have := hw y
      rw [polar_comm] at this
      simpa [polarBilin_apply_apply] using this))
  exact absurd hS (not_lt.mpr hpos.le)

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
