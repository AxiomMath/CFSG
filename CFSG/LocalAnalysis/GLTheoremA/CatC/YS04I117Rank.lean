module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Out
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Defs
public import CFSG.HardMathSupport.Timmesfeld.DFour.Triality
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.HardMathSupport.Timmesfeld.DFour
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

@[expose] def D4TrialityCentRank : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r f : ℕ), r.Prime → r ≠ 2 → r ≠ 3 → Nat.card K = r ^ f →
    ∀ t : MulAut (D4Model K), t ^ 3 = 1 → t ∉ D4Img K →
      ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → (∀ a ∈ A, t a = a) → Nat.card A ≤ 9

@[expose] def D4FourRank : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r f : ℕ), r.Prime → r ≠ 2 → r ≠ 3 → Nat.card K = r ^ f →
    ∃ (F : Subgroup (D4Model K)) (z : D4Model K), IsElemAbelian 3 F ∧ 3 ^ 4 ≤ Nat.card F ∧
      z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ s ∈ F, s * z = z * s

@[expose] def D4FieldFour : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r f : ℕ), r.Prime → r ≠ 2 → r ≠ 3 → Nat.card K = r ^ f →
    ∀ y : MulAut (D4Model K), y ∈ D4Img K → y ∉ Inn (D4Model K) → y ^ 3 = 1 →
      ∃ (F : Subgroup (D4Model K)) (z : D4Model K), IsElemAbelian 3 F ∧ 3 ^ 4 ≤ Nat.card F ∧
        z ^ 2 = 1 ∧ z ≠ 1 ∧ (∀ s ∈ F, s * z = z * s) ∧ y z = z ∧ ∀ s ∈ F, y s = s

theorem d4Facts2 {K : Type} [Field K] [Finite K] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) :
    coordinateQuadPlus 4 K ≠ 0 ∧
      (∃ m : ℕ, Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) = 2 ^ m) ∧
      Subgroup.center (D4Model K) = ⊥ := by
  let e : D4Model K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
  have hm : StatedClassicalModel (D4Model K) .POmegaPlus 4 r f :=
    ⟨⟨hr, hf, le_refl 4⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus hm K hK e
  obtain ⟨hQ0, hab, -⟩ := coordinate_facts_four hm K hK e
  exact ⟨hQ0, hab, CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot
    (by norm_num) hnd hT⟩

theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {r f : ℕ} (hK : Nat.card K = r ^ f) :
    1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with h | h
  · subst h
    have : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at this
    simp at this
  · exact h

theorem d4TrialityRankData_of (h1 : D4TrialityCentRank) (h2 : D4FourRank) (h3 : D4FieldFour) :
    D4TrialityRankData := by
  intro K _ _ r f hr hr2 hr3 hK X hX hXE
  have hf : 1 ≤ f := one_le_of_card_field hK
  obtain ⟨hQ0, hab2, hcen⟩ := d4Facts2 hr hr2 hf hK
  obtain ⟨-, -, -, -, hidx⟩ := d4Facts hr hr2 hf hK
  set Q := coordinateQuadPlus 4 K with hQdef
  have hQv := CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value Q hQ0
  obtain ⟨g, hgE, hg⟩ := exists_gen_image Q
  obtain ⟨hEX, hXI⟩ := card_le_of_tower Nat.prime_three le_rfl (linearRange_normal Q) hidx g hgE hg
    (fun δ hδ hδp => mem_inner_of_mem_linearRange Q hQv hab2 Nat.prime_three (by norm_num) hδ hδp)
    hX.2
  have hEX' : Nat.card (D4Img K ⊓ X : Subgroup (MulAut (D4Model K))) ≤
      3 * Nat.card (X ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) := hEX
  have hXI' : Nat.card X ≤ 9 * Nat.card (X ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) := by
    have := hXI
    simpa [mul_assoc] using this
  obtain ⟨t, htX, htE⟩ := Set.not_subset.mp hXE
  obtain ⟨A, hA, hfix, hcardA⟩ := exists_fixed_of_mem hcen hX htX
  have hA9 : Nat.card (X ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) ≤ 9 := by
    rw [← hcardA]
    exact h1 K r f hr hr2 hr3 hK t (hX.2 t htX) htE A hA hfix
  have hrel : (D4Img K).relIndex X * Nat.card (D4Img K ⊓ X : Subgroup (MulAut (D4Model K)))
      = Nat.card X := Subgroup.relIndex_mul_card _ _
  have hrel3 := relIndex_le_three hidx X
  have hXE3 : Nat.card X ≤ 3 * Nat.card (D4Img K ⊓ X : Subgroup (MulAut (D4Model K))) := by
    rw [← hrel]
    exact Nat.mul_le_mul_right _ hrel3
  by_cases hsmall : Nat.card (D4Img K ⊓ X : Subgroup (MulAut (D4Model K))) ≤ 9
  ·
    obtain ⟨F, z, hF, hFc, hz2, hz1, hFz⟩ := h2 K r f hr hr2 hr3 hK
    refine ⟨⊥, F, z, bot_le, by simp, hF, hz2, hz1, hFz, ?_, ?_, ?_⟩
    · intro a ha
      rw [Subgroup.mem_bot] at ha
      rw [ha, MulAut.one_apply]
    · intro a ha s _
      rw [Subgroup.mem_bot] at ha
      rw [ha, MulAut.one_apply]
    · rw [Subgroup.card_bot]
      norm_num at hFc
      omega
  ·
    push Not at hsmall
    have hex : ∃ y ∈ X, y ∈ matrixProjectiveImage Q ∧ y ∉ Inn (D4Model K) := by
      by_contra hcon
      push Not at hcon
      have hle : (D4Img K ⊓ X : Subgroup (MulAut (D4Model K))) ≤ X ⊓ Inn (D4Model K) := fun y hy =>
        ⟨hy.2, hcon y hy.2 hy.1⟩
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨y, hyX, hyE, hyI⟩ := hex
    have hy3 : y ^ 3 = 1 := hX.2 y hyX
    have hy1 : y ≠ 1 := fun h => hyI (h ▸ (Inn (D4Model K)).one_mem)
    obtain ⟨F, z, hF, hFc, hz2, hz1, hFz, hyz, hys⟩ := h3 K r f hr hr2 hr3 hK y hyE hyI hy3
    have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hstab : ∀ w : D4Model K, y w = w → Subgroup.zpowers y ≤ MulAction.stabilizer
        (MulAut (D4Model K)) w := fun w hw =>
      Subgroup.zpowers_le.2 (by
        rw [MulAction.mem_stabilizer_iff]
        exact hw)
    refine ⟨Subgroup.zpowers y, F, z, Subgroup.zpowers_le.2 hyX, ?_, hF, hz2, hz1, hFz, ?_, ?_, ?_⟩
    · rw [eq_bot_iff]
      rintro a ⟨ha1, ha2⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha1
      rw [Subgroup.mem_bot]
      rw [← zpow_mod_orderOf, hord] at ha2 ⊢
      have h0 : (0 : ℤ) ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
      have h3' : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
      generalize k % ((3 : ℕ) : ℤ) = m at h0 h3' ha2 ⊢
      interval_cases m
      · simp
      · exact absurd (by simpa using ha2) hyI
      · exfalso
        apply hyI
        have h4 : y = (y ^ (2 : ℤ)) ^ 2 := by
          rw [← zpow_natCast, ← zpow_mul]
          have : y ^ (4 : ℤ) = y := by
            rw [show (4 : ℤ) = (3 : ℕ) + 1 by norm_num, zpow_add, zpow_natCast, hy3, one_mul,
              zpow_one]
          simpa using this.symm
        rw [h4]
        exact (Inn (D4Model K)).pow_mem ha2 2
    · intro a ha
      exact (hstab z hyz ha : a ∈ MulAction.stabilizer _ z)
    · intro a ha s hs
      exact (hstab s (hys s hs) ha : a ∈ MulAction.stabilizer _ s)
    · rw [Nat.card_zpowers, hord]
      norm_num at hFc
      omega

end CFSG.LocalAnalysis.GLTheoremA
