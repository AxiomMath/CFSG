module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthProj
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKlein
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.TorusInv
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NumTheory
public import CFSG.RankThree.PartOne.KLC.D4OutCentral
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.OutStructure CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem BigInv.of_conj {Y : Type} [Group Y] (β b : MulAut Y) (h : BigInv (β * b * β⁻¹)) :
    BigInv b := by
  obtain ⟨x, p, hp, h11, hord⟩ := h
  refine ⟨β⁻¹ x, p, hp, h11, ?_⟩
  rw [← hord]
  have : (β * b * β⁻¹) x * x⁻¹ = β (b (β⁻¹ x) * (β⁻¹ x)⁻¹) := by
    simp [MulAut.mul_apply, map_mul, map_inv]
  rw [this]
  exact (orderOf_injective β.toMonoidHom β.injective _).symm


theorem kleinBigInv_orth {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hd : 8 ≤ d) (hd12 : Nat.card K = 4 → 12 ≤ d)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    (hconj : ∀ B : Subgroup (MulAut (matrixProjectiveDerived Q)),
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) → Nat.card B = 4 →
        B ⊓ Inn (matrixProjectiveDerived Q) = ⊥ →
        ∃ β : MulAut (matrixProjectiveDerived Q), ∀ b ∈ B, β * b * β⁻¹ ∈ matrixProjectiveImage Q) :
    KleinBigInv (matrixProjectiveDerived Q) := by
  classical
  intro B hcomm hsq hcard hinn
  have : Fintype K := Fintype.ofFinite K
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
  obtain ⟨j, hj⟩ := hfe
  have hj2 : (f : ℕ) / 2 = j := by omega
  rw [hj2] at hσpow
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, hj]; ring_nf
  have hj1' : 1 ≤ j := by have := f.pos; omega
  have hTQ : ∀ v, Q (coordSemilinear g.val v) = g.val.right (Q v) := fun v =>
    (mem_unitMultiplierPairs_iff Q g).mp hg v
  have hTT : ∀ v, coordSemilinear g.val (coordSemilinear g.val v) = v := by
    intro v
    have h1 := coordinateSemilinearMap_mul g.val g.val v
    have h2 : g.val * g.val = 1 := congrArg Subtype.val hgg
    rw [h2, coordinateSemilinearMap_one] at h1
    exact h1.symm
  obtain ⟨r, hr, p, hp, h11, hpd, hpq, hrd⟩ : ∃ r : ℕ, Odd r ∧ ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧
      p ∣ (2 ^ j) ^ r + 1 ∧ ¬ p ∣ 2 ^ (2 * j) - 1 ∧ 2 * r + 2 ≤ d := by
    rcases Nat.lt_or_ge j 2 with hj3 | hj3
    · have hj1 : j = 1 := by omega
      subst hj1
      have h4 : Nat.card K = 4 := by rw [hK']; norm_num
      obtain ⟨hp, h11, hpd, hpq⟩ := good_prime_two
      exact ⟨5, by decide, 11, hp, h11, hpd, hpq, by have := hd12 h4; omega⟩
    · obtain ⟨p, hp, h11, hpd, hpq⟩ := exists_good_prime_three j hj3
      exact ⟨3, by decide, p, hp, h11, hpd, hpq, by omega⟩
  have hfr := exists_frame (T := coordSemilinear g.val) hQ hσσ hσ1 hTT hTQ r (by
    rw [Module.finrank_fin_fun]; omega)
  obtain ⟨F⟩ := hfr
  obtain ⟨M, M', hMσ, hMM', hMp, -, hns⟩ := exists_inverted_matrix g.val.right hσσ hσ1 j r r
    hσpow hK' hr le_rfl hp hpd (by rw [hK']; exact hpq)
  have hbig := bigInv_of_frame Q g hgg hZ hab hσσ hTQ F hp h11 M M' hMσ hMM' hMp hns
  rw [hgκ] at hbig
  obtain ⟨b, hb, rfl⟩ := hB'mem α' hα'B
  exact ⟨b, hb, BigInv.of_conj β b hbig⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
