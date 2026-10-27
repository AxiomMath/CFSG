module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4FixedLine
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnPerX
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem cube_root_cases {L : Type} [Field L] {A B : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) : B = A ∨ B = A⁻¹ := by
  have cube : ∀ C : Lˣ, C ^ 3 = 1 → (C : L) ^ 3 = 1 := fun C hC => by
    have := congrArg Units.val hC
    simpa using this
  have key : ∀ C : Lˣ, C ^ 3 = 1 → C ≠ 1 → (C : L) ^ 2 + C + 1 = 0 := by
    intro C hC3 hC1
    have h3 := cube C hC3
    have h : ((C : L) - 1) * ((C : L) ^ 2 + C + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (Units.ext (by simpa [sub_eq_zero] using h)) hC1
    · exact h
  have hA := key A hA3 hA1
  have hB := key B hB3 hB1
  have h3A := cube A hA3
  have hAinv : A⁻¹ = A ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hA3)
  have hprod : ((B : L) - A) * ((B : L) - A ^ 2) = 0 := by
    linear_combination hB - (B : L) * hA + h3A
  rcases mul_eq_zero.1 hprod with h | h
  · exact Or.inl (Units.ext (sub_eq_zero.1 h))
  · right
    rw [hAinv]
    exact Units.ext (by simpa using sub_eq_zero.1 h)

theorem d4LongA2_basis_not_mem :
    ∀ i : Fin 4, i ≠ 2 → (Pi.single i 1 : Fin 4 → ℤ) ∉ d4LongA2 := by
  intro i hi hmem
  have h : (Pi.single i 1 : Fin 4 → ℤ) = ![0, 0, 1, 0] ∨
      (Pi.single i 1 : Fin 4 → ℤ) = ![1, 1, 1, 1] ∨
      (Pi.single i 1 : Fin 4 → ℤ) = ![1, 1, 2, 1] ∨
      (Pi.single i 1 : Fin 4 → ℤ) = ![0, 0, -1, 0] ∨
      (Pi.single i 1 : Fin 4 → ℤ) = ![-1, -1, -1, -1] ∨
      (Pi.single i 1 : Fin 4 → ℤ) = ![-1, -1, -2, -1] := d4LongA2_mem_iff.1 hmem
  clear hmem
  revert h hi
  revert i
  decide

theorem d4_tuple_of_kernel_longA2 {L : Type} [Field L]
    {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1)
    (hker : ∀ α, α ∈ rootCharKernel a ↔ α ∈ d4LongA2) :
    ∃ B : Lˣ, B ^ 3 = 1 ∧ B ≠ 1 ∧ a = ![B, B, 1, B] := by
  have hin : ∀ i : Fin TwistTag.D4.tag.rank, rootChar a (Pi.single i 1) = 1 →
      (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4LongA2 :=
    fun i h => (hker _).1 ⟨IsRoot.basis (τ := TwistTag.D4.tag) i, h⟩
  have hnot : ∀ i : Fin TwistTag.D4.tag.rank, i ≠ 2 →
      (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∉ d4LongA2 := fun i hi hmem =>
    d4LongA2_basis_not_mem i hi hmem
  have h2 : a 2 = 1 := by
    have hm : (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4LongA2 :=
      d4LongA2_mem_iff.2 (Or.inl (by funext j; fin_cases j <;> rfl))
    have := ((hker _).2 hm).2
    rwa [CTTorus.rootChar_single] at this
  have hne : ∀ i : Fin TwistTag.D4.tag.rank, i ≠ 2 → a i ≠ 1 := fun i hi h =>
    hnot i hi (hin i (by rw [CTTorus.rootChar_single]; exact h))
  have hsum' : a (0 : Fin 4) * a (1 : Fin 4) * a (3 : Fin 4) = 1 := by
    have hm : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4LongA2 :=
      d4LongA2_mem_iff.2 (Or.inr (Or.inl rfl))
    have := ((hker _).2 hm).2
    have e := rootChar_d4_apply a (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → ℤ)
    rw [e] at this
    have h2' : a (2 : Fin 4) = 1 := h2
    simpa [h2'] using this
  have hsum : a 0 * a 1 * a 3 = 1 := hsum'
  have hB3 : a 0 ^ 3 = 1 := ha3 0
  have h1 : a 1 = a 0 := by
    rcases cube_root_cases hB3 (hne 0 (by decide)) (ha3 1) (hne 1 (by decide)) with h | h
    · exact h
    · exfalso
      rw [h, mul_inv_cancel] at hsum
      simp at hsum
      exact hne 3 (by decide) hsum
  have h3 : a 3 = a 0 := by
    rcases cube_root_cases hB3 (hne 0 (by decide)) (ha3 3) (hne 3 (by decide)) with h | h
    · exact h
    · exfalso
      rw [h1, h, mul_inv_cancel_right] at hsum
      exact hne 0 (by decide) hsum
  refine ⟨a 0, hB3, hne 0 (by decide), ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact h1
  · exact h2
  · exact h3

theorem d4A2Sigma_eq' : (d4A2Sigma : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
    {Pi.single 0 1, -Pi.single 0 1, Pi.single 2 1, -Pi.single 2 1,
      Pi.single 0 1 + Pi.single 2 1, -(Pi.single 0 1 + Pi.single 2 1)} := rfl

theorem d4A2Sigma_image_longA2 {v₀ : WeylGroup TwistTag.D4.tag}
    (hv0 : v₀ • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 0 1)
    (hv2 : v₀ • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 1 1) :
    (fun α : Fin TwistTag.D4.tag.rank → ℤ => v₀ • α) '' d4A2Sigma = d4LongA2 := by
  have hsum : v₀ • ((Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) + Pi.single 2 1) =
      d4LongVec 1 2 := by
    rw [smul_add, hv0, hv2, d4LongVec_add]
    rfl
  have n0 : v₀ • (-(Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ)) = d4LongVec 0 (-1) := by
    rw [smul_neg, hv0, d4LongVec_neg]
    rfl
  have n2 : v₀ • (-(Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ)) = d4LongVec (-1) (-1) := by
    rw [smul_neg, hv2, d4LongVec_neg]
  have n02 : v₀ • (-((Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) + Pi.single 2 1)) =
      d4LongVec (-1) (-2) := by
    rw [smul_neg, hsum, d4LongVec_neg]
  rw [d4LongA2_eq, d4A2Sigma_eq']
  ext α
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hv0
    · exact Or.inr (Or.inr (Or.inr (Or.inl n0)))
    · exact Or.inr (Or.inl hv2)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl n2))))
    · exact Or.inr (Or.inr (Or.inl hsum))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr n02))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, hv0⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), hv2⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hsum⟩
    · exact ⟨_, Or.inr (Or.inl rfl), n0⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), n2⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), n02⟩

section Weyl

theorem exists_weylTuple_longA2 {L : Type} [Field L] {a : Fin TwistTag.D4.tag.rank → Lˣ}
    {i : Fin 4} (hi : survivingRoots a = trialitySigma i) :
    ∃ W : WeylGroup TwistTag.D4.tag, ∀ α, α ∈ rootCharKernel (weylTuple W a) ↔ α ∈ d4LongA2 := by
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup TwistTag.D4.tag,
      (fun α : Fin TwistTag.D4.tag.rank → ℤ => v • α) '' d4A2Sigma = survivingRoots a := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
    exact ⟨w, by rw [hi, d4A2Sigma_eq_trialityStdA2, ← hw]; rfl⟩
  obtain ⟨v₀, hv0, hv2⟩ := exists_smul_d4LongA2
  have hv₀ := d4A2Sigma_image_longA2 hv0 hv2
  refine ⟨v₀ * v⁻¹, fun α => ?_⟩
  constructor
  · rintro ⟨hα, h1⟩
    rw [rootChar_weylTuple] at h1
    have hβ : v • (v₀⁻¹ • α) ∈ survivingRoots a :=
      ⟨IsRoot.smul (IsRoot.smul hα _) _, by simpa [mul_smul] using h1⟩
    rw [← hv] at hβ
    obtain ⟨β, hβσ, hββ⟩ := hβ
    have hβα : β = v₀⁻¹ • α := MulAction.injective v hββ
    rw [← hv₀]
    exact ⟨β, hβσ, by rw [hβα]; exact smul_inv_smul v₀ α⟩
  · intro hα
    have hα' := hα
    rw [← hv₀] at hα'
    obtain ⟨β, hβσ, rfl⟩ := hα'
    have hβr : v • β ∈ survivingRoots a := by
      rw [← hv]
      exact ⟨β, hβσ, rfl⟩
    refine ⟨d4LongA2_isRoot hα, ?_⟩
    rw [rootChar_weylTuple]
    have e : (v₀ * v⁻¹)⁻¹ • (v₀ • β) = v • β := by
      rw [mul_inv_rev, inv_inv, mul_smul, inv_smul_smul]
    rw [e]
    exact hβr.2

end Weyl

end CFSG.GH74.GLS.Stage2.Bender.Thm1
