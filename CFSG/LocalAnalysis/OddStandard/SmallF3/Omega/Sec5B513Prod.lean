module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Dec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Iso

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private lemma sec5b513_prod_mul {K₃ K₄ : Subgroup G}
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a)
    {a a' : G} (ha : a ∈ K₃) (ha' : a' ∈ K₃) {b b' : G} (hb : b ∈ K₄) (hb' : b' ∈ K₄) :
    (a * b) * (a' * b') = (a * a') * (b * b') := by
  rw [mul_assoc a b (a' * b'), ← mul_assoc b a' b', (hcomm a' ha' b hb).symm,
    mul_assoc a' b b', ← mul_assoc a a' (b * b')]

private lemma sec5b513_conj_eq_of_comm {a x : G} (h : a * x = x * a) : x⁻¹ * a * x = a := by
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

private lemma sec5b513_conj_prod {K₃ K₄ : Subgroup G}
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a)
    {a u₃ : G} (ha : a ∈ K₃) (hu₃ : u₃ ∈ K₃) {b u₄ : G} (hb : b ∈ K₄) (hu₄ : u₄ ∈ K₄) :
    (u₃ * u₄)⁻¹ * (a * b) * (u₃ * u₄) = (u₃⁻¹ * a * u₃) * (u₄⁻¹ * b * u₄) := by
  have hu₃X : u₃⁻¹ * a * u₃ ∈ K₃ :=
    K₃.mul_mem (K₃.mul_mem (K₃.inv_mem hu₃) ha) hu₃
  have h1 : u₃⁻¹ * b * u₃ = b := sec5b513_conj_eq_of_comm (hcomm u₃ hu₃ b hb).symm
  have h2 : u₄⁻¹ * (u₃⁻¹ * a * u₃) * u₄ = u₃⁻¹ * a * u₃ :=
    sec5b513_conj_eq_of_comm (hcomm (u₃⁻¹ * a * u₃) hu₃X u₄ hu₄)
  have hconj₃ : u₃⁻¹ * (a * b) * u₃ = (u₃⁻¹ * a * u₃) * (u₃⁻¹ * b * u₃) := by
    simpa [inv_inv] using (conj_mul (b := u₃⁻¹) (a := a) (c := b)).symm
  have hconj₄ : u₄⁻¹ * ((u₃⁻¹ * a * u₃) * b) * u₄ =
      (u₄⁻¹ * (u₃⁻¹ * a * u₃) * u₄) * (u₄⁻¹ * b * u₄) := by
    simpa [inv_inv] using
      (conj_mul (b := u₄⁻¹) (a := u₃⁻¹ * a * u₃) (c := b)).symm
  rw [mul_inv_rev]
  calc (u₄⁻¹ * u₃⁻¹) * (a * b) * (u₃ * u₄)
      = u₄⁻¹ * (u₃⁻¹ * (a * b) * u₃) * u₄ := by simp only [mul_assoc]
    _ = u₄⁻¹ * ((u₃⁻¹ * a * u₃) * (u₃⁻¹ * b * u₃)) * u₄ := by rw [hconj₃]
    _ = u₄⁻¹ * ((u₃⁻¹ * a * u₃) * b) * u₄ := by rw [h1]
    _ = (u₃⁻¹ * a * u₃) * (u₄⁻¹ * b * u₄) := by rw [hconj₄, h2]

private lemma sec5b513_gen_comm {K₃ K₄ : Subgroup G} (e₃ : ↥K₃ ≃* SL23) (e₄ : ↥K₄ ≃* SL23)
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a) {z : G} (hz3 : z ∈ K₃) (hz4 : z ∈ K₄)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {a₀ b₀ : G} (ha₀ : a₀ ∈ K₃) (hb₀ : b₀ ∈ K₄)
    (ha0 : a₀ * a₀ = z) (hb0 : b₀ * b₀ = z)
    {v₃ v₄ : G} (hv₃ : v₃ ∈ K₃) (hv₄ : v₄ ∈ K₄) (hv₃4 : v₃ ^ 4 ≠ 1) (hv₄4 : v₄ ^ 4 ≠ 1) :
    ((v₃ * v₄)⁻¹ * (a₀ * b₀) * (v₃ * v₄)) * (a₀ * b₀) =
      (a₀ * b₀) * ((v₃ * v₄)⁻¹ * (a₀ * b₀) * (v₃ * v₄)) := by
  set a' : G := v₃⁻¹ * a₀ * v₃ with ha'_def
  set b' : G := v₄⁻¹ * b₀ * v₄ with hb'_def
  have ha'_mem : a' ∈ K₃ := K₃.mul_mem (K₃.mul_mem (K₃.inv_mem hv₃) ha₀) hv₃
  have hb'_mem : b' ∈ K₄ := K₄.mul_mem (K₄.mul_mem (K₄.inv_mem hv₄) hb₀) hv₄
  have hy : (v₃ * v₄)⁻¹ * (a₀ * b₀) * (v₃ * v₄) = a' * b' := by
    rw [ha'_def, hb'_def]
    exact sec5b513_conj_prod hcomm ha₀ hv₃ hb₀ hv₄
  have ha_anti : a₀ * a' = z * (a' * a₀) := by
    rw [ha'_def]
    exact sec5b513_anti e₃ hz3 hz2 hz1 ha₀ hv₃ ha0 hv₃4
  have hb_anti : b₀ * b' = z * (b' * b₀) := by
    rw [hb'_def]
    exact sec5b513_anti e₄ hz4 hz2 hz1 hb₀ hv₄ hb0 hv₄4
  have hX : a' * a₀ ∈ K₃ := K₃.mul_mem ha'_mem ha₀
  have hY : b' * b₀ ∈ K₄ := K₄.mul_mem hb'_mem hb₀
  have hzX : z * (a' * a₀) = (a' * a₀) * z := (hcomm (a' * a₀) hX z hz4).symm
  have hzY : z * (b' * b₀) = (b' * b₀) * z := hcomm z hz3 (b' * b₀) hY
  have key : (z * (a' * a₀)) * (z * (b' * b₀)) = (a' * a₀) * (b' * b₀) := by
    rw [hzX, mul_assoc, ← mul_assoc z z (b' * b₀), hz2, one_mul]
  calc ((v₃ * v₄)⁻¹ * (a₀ * b₀) * (v₃ * v₄)) * (a₀ * b₀)
      = (a' * b') * (a₀ * b₀) := by rw [hy]
    _ = (a' * a₀) * (b' * b₀) := sec5b513_prod_mul hcomm ha'_mem ha₀ hb'_mem hb₀
    _ = (z * (a' * a₀)) * (z * (b' * b₀)) := key.symm
    _ = (a₀ * a') * (b₀ * b') := by rw [← ha_anti, ← hb_anti]
    _ = (a₀ * b₀) * (a' * b') := (sec5b513_prod_mul hcomm ha₀ ha'_mem hb₀ hb'_mem).symm
    _ = (a₀ * b₀) * ((v₃ * v₄)⁻¹ * (a₀ * b₀) * (v₃ * v₄)) := by rw [hy]

theorem sec5b513_trans {K₃ K₄ : Subgroup G} (e₃ : ↥K₃ ≃* SL23) (e₄ : ↥K₄ ≃* SL23)
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a) {z : G} (hz3 : z ∈ K₃) (hz4 : z ∈ K₄)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {t : G} (ht : t ∈ K₃ ⊔ K₄) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htz : t ≠ z) {t' : G} (ht' : t' ∈ K₃ ⊔ K₄) (ht'2 : t' * t' = 1) (ht'1 : t' ≠ 1)
    (ht'z : t' ≠ z) : ∃ y ∈ K₃ ⊔ K₄, y⁻¹ * t * y = t' := by
  obtain ⟨a₀, ha₀, b₀, hb₀, ht_eq, ha0, hb0⟩ :=
    sec5b513_decomp e₃ e₄ hcomm hz3 hz4 hz2 hz1 ht ht2 ht1 htz
  obtain ⟨a₁, ha₁, b₁, hb₁, ht'_eq, ha1, hb1⟩ :=
    sec5b513_decomp e₃ e₄ hcomm hz3 hz4 hz2 hz1 ht' ht'2 ht'1 ht'z
  obtain ⟨u₃, hu₃, hu₃_eq⟩ := sec5b513_conj_of_sq e₃ hz3 hz2 hz1 ha₀ ha₁ ha0 ha1
  obtain ⟨u₄, hu₄, hu₄_eq⟩ := sec5b513_conj_of_sq e₄ hz4 hz2 hz1 hb₀ hb₁ hb0 hb1
  refine ⟨u₃ * u₄, ?_, ?_⟩
  · exact Subgroup.mul_mem (K₃ ⊔ K₄) (Subgroup.mem_sup_left hu₃) (Subgroup.mem_sup_right hu₄)
  · calc (u₃ * u₄)⁻¹ * t * (u₃ * u₄)
        = (u₃ * u₄)⁻¹ * (a₀ * b₀) * (u₃ * u₄) := by rw [ht_eq]
      _ = (u₃⁻¹ * a₀ * u₃) * (u₄⁻¹ * b₀ * u₄) := sec5b513_conj_prod hcomm ha₀ hu₃ hb₀ hu₄
      _ = a₁ * b₁ := by rw [hu₃_eq, hu₄_eq]
      _ = t' := ht'_eq.symm

theorem sec5b513_gen {K₃ K₄ : Subgroup G} (e₃ : ↥K₃ ≃* SL23) (e₄ : ↥K₄ ≃* SL23)
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a) {z : G} (hz3 : z ∈ K₃) (hz4 : z ∈ K₄)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {t : G} (ht : t ∈ K₃ ⊔ K₄) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htz : t ≠ z) {g : G} (hg : g ∈ K₃ ⊔ K₄) :
    ∃ y₁ ∈ K₃ ⊔ K₄, ∃ y₂ ∈ K₃ ⊔ K₄,
      (y₁⁻¹ * t * y₁) * t = t * (y₁⁻¹ * t * y₁) ∧
        (y₂⁻¹ * t * y₂) * t = t * (y₂⁻¹ * t * y₂) ∧ g = y₁ * y₂ := by
  obtain ⟨a₀, ha₀, b₀, hb₀, ht_eq, ha0, hb0⟩ :=
    sec5b513_decomp e₃ e₄ hcomm hz3 hz4 hz2 hz1 ht ht2 ht1 htz
  obtain ⟨g₃, hg₃, g₄, hg₄, hg_eq⟩ := sec5b_mem_sup_of_comm hcomm hg
  obtain ⟨u₃, hu₃, hu₃4, hu₃g₃4⟩ := sec5b513_split e₃ hg₃
  obtain ⟨u₄, hu₄, hu₄4, hu₄g₄4⟩ := sec5b513_split e₄ hg₄
  have hX : u₃⁻¹ * g₃ ∈ K₃ := K₃.mul_mem (K₃.inv_mem hu₃) hg₃
  have hY : u₄⁻¹ * g₄ ∈ K₄ := K₄.mul_mem (K₄.inv_mem hu₄) hg₄
  have hstep : u₄ * ((u₃⁻¹ * g₃) * (u₄⁻¹ * g₄)) = (u₃⁻¹ * g₃) * g₄ := by
    rw [← mul_assoc u₄ (u₃⁻¹ * g₃) (u₄⁻¹ * g₄),
      (hcomm (u₃⁻¹ * g₃) hX u₄ hu₄).symm,
      mul_assoc (u₃⁻¹ * g₃) u₄ (u₄⁻¹ * g₄), ← mul_assoc u₄ u₄⁻¹ g₄,
      mul_inv_cancel, one_mul]
  refine ⟨u₃ * u₄, ?_, (u₃⁻¹ * g₃) * (u₄⁻¹ * g₄), ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem (K₃ ⊔ K₄) (Subgroup.mem_sup_left hu₃) (Subgroup.mem_sup_right hu₄)
  · exact Subgroup.mul_mem (K₃ ⊔ K₄) (Subgroup.mem_sup_left hX) (Subgroup.mem_sup_right hY)
  · simpa [ht_eq] using
      sec5b513_gen_comm e₃ e₄ hcomm hz3 hz4 hz2 hz1 ha₀ hb₀ ha0 hb0 hu₃ hu₄ hu₃4 hu₄4
  · simpa [ht_eq] using
      sec5b513_gen_comm e₃ e₄ hcomm hz3 hz4 hz2 hz1 ha₀ hb₀ ha0 hb0 hX hY hu₃g₃4 hu₄g₄4
  · rw [hg_eq]
    symm
    calc (u₃ * u₄) * ((u₃⁻¹ * g₃) * (u₄⁻¹ * g₄))
        = u₃ * (u₄ * ((u₃⁻¹ * g₃) * (u₄⁻¹ * g₄))) := by rw [mul_assoc]
      _ = u₃ * ((u₃⁻¹ * g₃) * g₄) := by rw [hstep]
      _ = g₃ * g₄ := by
            rw [← mul_assoc u₃ (u₃⁻¹ * g₃) g₄, ← mul_assoc u₃ u₃⁻¹ g₃,
              mul_inv_cancel, one_mul]

end CFSG.OddStandard.SmallF3.Omega
