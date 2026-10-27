module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BCentProd

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private lemma sec5b513_mul_comm_prod {K₃ K₄ : Subgroup G}
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a)
    {a a' : G} (ha' : a' ∈ K₃) {b b' : G} (hb : b ∈ K₄) :
    (a * b) * (a' * b') = (a * a') * (b * b') := by
  rw [mul_assoc a b (a' * b'), ← mul_assoc b a' b', (hcomm a' ha' b hb).symm,
    mul_assoc a' b b', ← mul_assoc a a' (b * b')]

theorem sec5b513_decomp {K₃ K₄ : Subgroup G} (e₃ : ↥K₃ ≃* SL23) (e₄ : ↥K₄ ≃* SL23)
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a) {z : G} (hz3 : z ∈ K₃) (hz4 : z ∈ K₄)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {t : G} (ht : t ∈ K₃ ⊔ K₄) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htz : t ≠ z) :
    ∃ a₀ ∈ K₃, ∃ b₀ ∈ K₄, t = a₀ * b₀ ∧ a₀ * a₀ = z ∧ b₀ * b₀ = z := by
  obtain ⟨a₀, ha₀, b₀, hb₀, ht_eq⟩ := sec5b_mem_sup_of_comm hcomm ht
  subst ht_eq
  have hww : a₀ * a₀ * (b₀ * b₀) = 1 := by
    rw [← sec5b513_mul_comm_prod hcomm ha₀ hb₀]
    exact ht2
  have hw4 : a₀ * a₀ ∈ K₄ := by
    have h : a₀ * a₀ = (b₀ * b₀)⁻¹ := eq_inv_of_mul_eq_one_left hww
    rw [h]
    exact K₄.inv_mem (K₄.mul_mem hb₀ hb₀)
  have hw_central : ∀ c : SL23,
      e₃ ⟨a₀ * a₀, K₃.mul_mem ha₀ ha₀⟩ * c = c * e₃ ⟨a₀ * a₀, K₃.mul_mem ha₀ ha₀⟩ := by
    intro c
    obtain ⟨c', rfl⟩ := e₃.surjective c
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hcomm c'.1 c'.2 (a₀ * a₀) hw4).symm
  have hζ₃ : e₃ ⟨z, hz3⟩ * e₃ ⟨z, hz3⟩ = 1 := by
    rw [← map_mul, ← map_one e₃]
    congr 1
    apply Subtype.ext
    simpa using hz2
  have hζ₃1 : e₃ ⟨z, hz3⟩ ≠ 1 := by
    intro hc
    have hsub : (⟨z, hz3⟩ : ↥K₃) = 1 := e₃.injective (by rw [hc, map_one])
    exact hz1 (congrArg Subtype.val hsub)
  have hζ₄ : e₄ ⟨z, hz4⟩ * e₄ ⟨z, hz4⟩ = 1 := by
    rw [← map_mul, ← map_one e₄]
    congr 1
    apply Subtype.ext
    simpa using hz2
  have hζ₄1 : e₄ ⟨z, hz4⟩ ≠ 1 := by
    intro hc
    have hsub : (⟨z, hz4⟩ : ↥K₄) = 1 := e₄.injective (by rw [hc, map_one])
    exact hz1 (congrArg Subtype.val hsub)
  have hwz : a₀ * a₀ = 1 ∨ a₀ * a₀ = z := by
    rcases sec5b_sl23_eq_of_central hζ₃ hζ₃1 hw_central with h1 | h1
    · left
      have hsub : (⟨a₀ * a₀, K₃.mul_mem ha₀ ha₀⟩ : ↥K₃) = 1 :=
        e₃.injective (by rw [h1, map_one])
      exact congrArg Subtype.val hsub
    · right
      have hsub : (⟨a₀ * a₀, K₃.mul_mem ha₀ ha₀⟩ : ↥K₃) = ⟨z, hz3⟩ := e₃.injective h1
      exact congrArg Subtype.val hsub
  rcases hwz with hw1 | hwz'
  · exfalso
    have hb0sq : b₀ * b₀ = 1 := by
      rw [hw1, one_mul] at hww
      exact hww
    have ha0 : a₀ = 1 ∨ a₀ = z := by
      have hsq : e₃ ⟨a₀, ha₀⟩ * e₃ ⟨a₀, ha₀⟩ = 1 := by
        rw [← map_mul, ← map_one e₃]
        congr 1
        apply Subtype.ext
        simpa using hw1
      rcases sec5b_sl23_eq_of_sq_eq_one hζ₃ hζ₃1 hsq with h1 | h1
      · left
        have hsub : (⟨a₀, ha₀⟩ : ↥K₃) = 1 := e₃.injective (by rw [h1, map_one])
        exact congrArg Subtype.val hsub
      · right
        have hsub : (⟨a₀, ha₀⟩ : ↥K₃) = ⟨z, hz3⟩ := e₃.injective h1
        exact congrArg Subtype.val hsub
    have hb0 : b₀ = 1 ∨ b₀ = z := by
      have hsq : e₄ ⟨b₀, hb₀⟩ * e₄ ⟨b₀, hb₀⟩ = 1 := by
        rw [← map_mul, ← map_one e₄]
        congr 1
        apply Subtype.ext
        simpa using hb0sq
      rcases sec5b_sl23_eq_of_sq_eq_one hζ₄ hζ₄1 hsq with h1 | h1
      · left
        have hsub : (⟨b₀, hb₀⟩ : ↥K₄) = 1 := e₄.injective (by rw [h1, map_one])
        exact congrArg Subtype.val hsub
      · right
        have hsub : (⟨b₀, hb₀⟩ : ↥K₄) = ⟨z, hz4⟩ := e₄.injective h1
        exact congrArg Subtype.val hsub
    rcases ha0 with rfl | rfl <;> rcases hb0 with rfl | rfl
    · exact ht1 (by rw [one_mul])
    · exact htz (by rw [one_mul])
    · exact htz (by rw [mul_one])
    · exact ht1 (by rw [hz2])
  · refine ⟨a₀, ha₀, b₀, hb₀, rfl, hwz', ?_⟩
    have h1 : (b₀ * b₀)⁻¹ = z := by rw [← eq_inv_of_mul_eq_one_left hww, hwz']
    calc b₀ * b₀ = ((b₀ * b₀)⁻¹)⁻¹ := (inv_inv _).symm
      _ = z⁻¹ := by rw [h1]
      _ = z := inv_eq_of_mul_eq_one_right hz2

end CFSG.OddStandard.SmallF3.Omega
