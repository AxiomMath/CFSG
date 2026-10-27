module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralTwoCoverTransfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open scoped commutatorElement

variable {P R : Type*} [Group P] [Group R]

theorem commutatorElement_mul_left_of_central {x y w : P}
    (hy : ∀ g, g * ⁅y, w⁆ = ⁅y, w⁆ * g) : ⁅x * y, w⁆ = ⁅y, w⁆ * ⁅x, w⁆ := by
  calc ⁅x * y, w⁆ = x * (⁅y, w⁆ * w) * x⁻¹ * w⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
    _ = ⁅y, w⁆ * ⁅x, w⁆ := by rw [← mul_assoc, hy x, commutatorElement_def]; group

theorem commutatorElement_sq_of_central {x w : P} (hx : ∀ g, g * ⁅x, w⁆ = ⁅x, w⁆ * g) :
    ⁅x, w * w⁆ = ⁅x, w⁆ * ⁅x, w⁆ := by
  have h1 : x * w * x⁻¹ = ⁅x, w⁆ * w := by rw [commutatorElement_def]; group
  calc ⁅x, w * w⁆ = (x * w * x⁻¹) * (x * w * x⁻¹) * w⁻¹ * w⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅x, w⁆ * (w * ⁅x, w⁆) * w⁻¹ := by rw [h1]; group
    _ = ⁅x, w⁆ * ⁅x, w⁆ := by rw [hx w]; group

variable (ψ : P →* R) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
include hcen

omit hcen in
theorem map_commutatorElement_eq_one {x w : P} (hw : ψ w ∈ Subgroup.center R) :
    ψ ⁅x, w⁆ = 1 := by
  rw [map_commutatorElement, commutatorElement_def, Subgroup.mem_center_iff.mp hw (ψ x),
    mul_inv_cancel_right, mul_inv_cancel]

theorem commutatorElement_sq_eq_one {x w : P} (hw : ψ w ∈ Subgroup.center R)
    (hw2 : ψ w * ψ w = 1) : ⁅x, w⁆ * ⁅x, w⁆ = 1 := by
  rw [← commutatorElement_sq_of_central (hcen _ (map_commutatorElement_eq_one ψ hw)),
    commutatorElement_def, hcen (w * w) (by rw [map_mul, hw2]) x, mul_inv_cancel_right,
    mul_inv_cancel]

theorem commute_of_map_mem_center (hψ : Function.Surjective ψ)
    (hinv : ∀ z z' : P, ψ z = 1 → ψ z' = 1 → z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 → z = z')
    (hZR : Subgroup.center R ≤ commutator R) (hsq : ∀ r ∈ Subgroup.center R, r * r = 1)
    {w₁ w₂ : P} (hw₁ : ψ w₁ ∈ Subgroup.center R) (hw₂ : ψ w₂ ∈ Subgroup.center R) :
    w₁ * w₂ = w₂ * w₁ := by
  by_contra hne
  set c := ⁅w₁, w₂⁆ with hc_def
  have hc1 : c ≠ 1 := fun h => hne (by
    rw [hc_def, commutatorElement_eq_one_iff_mul_comm] at h; exact h)
  have hcent : ∀ {x w}, ψ w ∈ Subgroup.center R → ∀ g, g * ⁅x, w⁆ = ⁅x, w⁆ * g :=
    fun hw g => hcen _ (map_commutatorElement_eq_one ψ hw) g
  have hval : ∀ (x : P) {w}, ψ w ∈ Subgroup.center R → ⁅x, w⁆ = 1 ∨ ⁅x, w⁆ = c := by
    intro x w hw
    by_cases h1 : ⁅x, w⁆ = 1
    · exact Or.inl h1
    · exact Or.inr (hinv _ _ (map_commutatorElement_eq_one ψ hw)
        (map_commutatorElement_eq_one ψ hw₂)
        (commutatorElement_sq_eq_one ψ hcen hw (hsq _ hw))
        (commutatorElement_sq_eq_one ψ hcen hw₂ (hsq _ hw₂)) h1 hc1)
  have hcc : c * c = 1 := commutatorElement_sq_eq_one ψ hcen hw₂ (hsq _ hw₂)
  have hc21 : ⁅w₂, w₁⁆ = c := by
    rw [← commutatorElement_inv, ← hc_def]
    exact inv_eq_of_mul_eq_one_right hcc
  set Y := Subgroup.centralizer ({w₁, w₂} : Set P)
  have hmemY : ∀ y, ⁅y, w₁⁆ = 1 → ⁅y, w₂⁆ = 1 → y ∈ Y := by
    intro y h1 h2
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | hg
    · exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hdec : ∀ x : P, ∃ w : P, ψ w ∈ Subgroup.center R ∧ w⁻¹ * x ∈ Y := by
    intro x
    have key : ∀ w, ψ w ∈ Subgroup.center R → ⁅x, w₁⁆ = ⁅w, w₁⁆ → ⁅x, w₂⁆ = ⁅w, w₂⁆ →
        w⁻¹ * x ∈ Y := by
      intro w hw h1 h2
      have hinv1 : ∀ v, ψ v ∈ Subgroup.center R → ⁅w⁻¹, v⁆ * ⁅w, v⁆ = 1 := fun v hv => by
        rw [← commutatorElement_mul_left_of_central (hcent hv), mul_inv_cancel,
          commutatorElement_one_left]
      apply hmemY
      · rw [commutatorElement_mul_left_of_central (hcent hw₁), h1, ← hcent hw₁, hinv1 _ hw₁]
      · rw [commutatorElement_mul_left_of_central (hcent hw₂), h2, ← hcent hw₂, hinv1 _ hw₂]
    rcases hval x hw₁ with h1 | h1 <;> rcases hval x hw₂ with h2 | h2
    · exact ⟨1, by rw [map_one]; exact Subgroup.one_mem _,
        key 1 (by rw [map_one]; exact Subgroup.one_mem _)
          (by rw [h1, commutatorElement_one_left]) (by rw [h2, commutatorElement_one_left])⟩
    · exact ⟨w₁, hw₁, key w₁ hw₁ (by rw [h1, commutatorElement_self]) (by rw [h2])⟩
    · exact ⟨w₂, hw₂, key w₂ hw₂ (by rw [h1, hc21]) (by rw [h2, commutatorElement_self])⟩
    · have hw12 : ψ (w₁ * w₂) ∈ Subgroup.center R := by
        rw [map_mul]; exact Subgroup.mul_mem _ hw₁ hw₂
      refine ⟨w₁ * w₂, hw12, key _ hw12 ?_ ?_⟩
      · rw [h1, commutatorElement_mul_left_of_central (hcent hw₁), commutatorElement_self,
          mul_one, hc21]
      · rw [h2, commutatorElement_mul_left_of_central (hcent hw₂), commutatorElement_self,
          one_mul]
  have hRY : commutator R ≤ Y.map ψ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro r _ r' _
    obtain ⟨x, rfl⟩ := hψ r
    obtain ⟨x', rfl⟩ := hψ r'
    obtain ⟨w, hw, hy⟩ := hdec x
    obtain ⟨w', hw', hy'⟩ := hdec x'
    refine ⟨⁅w⁻¹ * x, w'⁻¹ * x'⁆, ?_, ?_⟩
    · rw [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy hy') (Y.inv_mem hy)) (Y.inv_mem hy')
    · have hx : ψ x = ψ w * ψ (w⁻¹ * x) := by rw [← map_mul, mul_inv_cancel_left]
      have hx' : ψ x' = ψ w' * ψ (w'⁻¹ * x') := by rw [← map_mul, mul_inv_cancel_left]
      rw [map_commutatorElement, hx, hx',
        CFSG.ProperTwoGeneratedCore.CentralTwoCover.commutatorElement_central_mul_left
          (fun g => (Subgroup.mem_center_iff.mp hw g)),
        CFSG.ProperTwoGeneratedCore.CentralTwoCover.commutatorElement_central_mul_right
          (fun g => (Subgroup.mem_center_iff.mp hw' g))]
  obtain ⟨y, hyY, hyw⟩ := hRY (hZR hw₁)
  have hz : ψ (y⁻¹ * w₁) = 1 := by rw [map_mul, map_inv, hyw, inv_mul_cancel]
  have hyw₂ : w₂ * y = y * w₂ := (Subgroup.mem_centralizer_iff.mp hyY) w₂ (by simp)
  apply hne
  calc w₁ * w₂ = y * (y⁻¹ * w₁) * w₂ := by rw [mul_inv_cancel_left]
    _ = y * w₂ * (y⁻¹ * w₁) := by rw [mul_assoc, ← hcen _ hz w₂, ← mul_assoc]
    _ = w₂ * (y * (y⁻¹ * w₁)) := by rw [← hyw₂, mul_assoc]
    _ = w₂ * w₁ := by rw [mul_inv_cancel_left]

end CFSG.ProperTwoGeneratedCore.Lemma37
