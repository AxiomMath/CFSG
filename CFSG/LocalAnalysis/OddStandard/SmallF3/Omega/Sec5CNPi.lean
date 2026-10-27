module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Pair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec5CNPi (π : SL23 × SL23 →* G) (K₃ K₄ : Subgroup G) (z : G) : Prop where
  range : π.range = K₃ ⊔ K₄
  left : π ((-1 : SL23), (1 : SL23)) = z
  right : π ((1 : SL23), (-1 : SL23)) = z
  ker : ∀ w : SL23 × SL23, π w = 1 → w = 1 ∨ w = ((-1 : SL23), (-1 : SL23))

theorem sec5cn_neg_one_comm (u : SL23) : (-1 : SL23) * u = u * (-1 : SL23) :=
  (by decide : ∀ u : SL23, (-1 : SL23) * u = u * (-1 : SL23)) u

theorem sec5cn_exists_pi {K₃ K₄ : Subgroup G} {z : G} (hp : Sec5Pair K₃ K₄ z) :
    ∃ π : SL23 × SL23 →* G, Sec5CNPi π K₃ K₄ z := by
  obtain ⟨e₃⟩ := hp.iso₁
  obtain ⟨e₄⟩ := hp.iso₂
  let φ₃ : SL23 →* G := K₃.subtype.comp e₃.symm.toMonoidHom
  let φ₄ : SL23 →* G := K₄.subtype.comp e₄.symm.toMonoidHom
  have hφ₃ : ∀ u, φ₃ u = (e₃.symm u : G) := fun u => rfl
  have hφ₄ : ∀ u, φ₄ u = (e₄.symm u : G) := fun u => rfl
  have hc : ∀ (u v : SL23), Commute (φ₃ u) (φ₄ v) := fun u v => by
    rw [hφ₃, hφ₄]
    exact hp.comm _ (e₃.symm u).2 _ (e₄.symm v).2
  have hr₃ : φ₃.range = K₃ := by
    ext x
    refine ⟨?_, fun hx => ⟨e₃ ⟨x, hx⟩, by simp [hφ₃]⟩⟩
    rintro ⟨u, rfl⟩
    rw [hφ₃]
    exact (e₃.symm u).2
  have hr₄ : φ₄.range = K₄ := by
    ext x
    refine ⟨?_, fun hx => ⟨e₄ ⟨x, hx⟩, by simp [hφ₄]⟩⟩
    rintro ⟨u, rfl⟩
    rw [hφ₄]
    exact (e₄.symm u).2
  have hinj₃ : Function.Injective φ₃ := fun u u' h =>
    e₃.symm.injective (Subtype.ext (by rwa [hφ₃, hφ₃] at h))
  have hinj₄ : Function.Injective φ₄ := fun u u' h =>
    e₄.symm.injective (Subtype.ext (by rwa [hφ₄, hφ₄] at h))
  have hz₃ : φ₃ (-1) = z := by
    have hsq : e₃ ⟨z, hp.z_mem₁⟩ * e₃ ⟨z, hp.z_mem₁⟩ = 1 := by
      rw [← map_mul, ← map_one e₃]
      congr 1
      exact Subtype.ext (by simpa using hp.z_sq)
    have hne : e₃ ⟨z, hp.z_mem₁⟩ ≠ 1 := by
      intro hc'
      have hsub : (⟨z, hp.z_mem₁⟩ : ↥K₃) = 1 := e₃.injective (by rw [hc', map_one])
      exact hp.z_ne (congrArg Subtype.val hsub)
    have h1 : e₃ ⟨z, hp.z_mem₁⟩ = -1 := (sl23_unique_involution _ hsq).resolve_left hne
    rw [hφ₃, ← h1]
    simp
  have hz₄ : φ₄ (-1) = z := by
    have hsq : e₄ ⟨z, hp.z_mem₂⟩ * e₄ ⟨z, hp.z_mem₂⟩ = 1 := by
      rw [← map_mul, ← map_one e₄]
      congr 1
      exact Subtype.ext (by simpa using hp.z_sq)
    have hne : e₄ ⟨z, hp.z_mem₂⟩ ≠ 1 := by
      intro hc'
      have hsub : (⟨z, hp.z_mem₂⟩ : ↥K₄) = 1 := e₄.injective (by rw [hc', map_one])
      exact hp.z_ne (congrArg Subtype.val hsub)
    have h1 : e₄ ⟨z, hp.z_mem₂⟩ = -1 := (sl23_unique_involution _ hsq).resolve_left hne
    rw [hφ₄, ← h1]
    simp
  refine ⟨MonoidHom.noncommCoprod φ₃ φ₄ hc, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.noncommCoprod_range, hr₃, hr₄]
  · simp [hz₃]
  · simp [hz₄]
  · intro w hw
    obtain ⟨u, v⟩ := w
    simp only [MonoidHom.noncommCoprod_apply] at hw
    have hmem₃ : φ₃ u ∈ K₃ := hr₃ ▸ ⟨u, rfl⟩
    have hmem₄ : φ₄ v⁻¹ ∈ K₄ := hr₄ ▸ ⟨v⁻¹, rfl⟩
    have heq : φ₃ u = φ₄ v⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hw
    rcases hp.inf_eq hmem₃ (heq ▸ hmem₄) with h1 | h1
    · left
      have hu : u = 1 := hinj₃ (by rw [h1, map_one])
      have hv : v = 1 := hinj₄ (by
        rw [map_one, ← inv_eq_one, ← map_inv, ← heq, h1])
      rw [hu, hv]
      rfl
    · right
      have hu : u = -1 := hinj₃ (by rw [h1, hz₃])
      have hv' : φ₄ v⁻¹ = z := by rw [← heq, h1]
      have hv : v⁻¹ = -1 := hinj₄ (by rw [hv', hz₄])
      have hv'' : v = -1 := by
        have := congrArg (fun x => x⁻¹) hv
        simpa using this
      rw [hu, hv'']

variable {π : SL23 × SL23 →* G} {K₃ K₄ : Subgroup G} {z : G}

theorem Sec5CNPi.mem_iff (h : Sec5CNPi π K₃ K₄ z) {x : G} :
    x ∈ K₃ ⊔ K₄ ↔ ∃ w, π w = x := by
  rw [← h.range]
  exact MonoidHom.mem_range

theorem Sec5CNPi.eq_iff (h : Sec5CNPi π K₃ K₄ z) {w w' : SL23 × SL23} :
    π w = π w' ↔ w' = w ∨ w' = w * ((-1 : SL23), (-1 : SL23)) := by
  constructor
  · intro hw
    have h1 : π (w⁻¹ * w') = 1 := by rw [map_mul, map_inv, hw, inv_mul_cancel]
    rcases h.ker _ h1 with h2 | h2
    · left
      exact (inv_mul_eq_one.mp h2).symm
    · right
      have := congrArg (fun x => w * x) h2
      simpa using this
  · rintro (rfl | rfl)
    · rfl
    · have h1 : π ((-1 : SL23), (-1 : SL23)) = 1 := by
        have h2 : π ((-1 : SL23), (-1 : SL23)) =
            π ((-1 : SL23), (1 : SL23)) * π ((1 : SL23), (-1 : SL23)) := by
          rw [← map_mul]
          simp
        rw [h2, h.left, h.right]
        have h3 : z * z = 1 := by
          rw [← h.left, ← map_mul]
          have : (((-1 : SL23), (1 : SL23)) * ((-1 : SL23), (1 : SL23)) : SL23 × SL23) = 1 := by
            ext <;> simp
          rw [this, map_one]
        exact h3
      rw [map_mul, h1, mul_one]

theorem Sec5CNPi.z_sq (h : Sec5CNPi π K₃ K₄ z) : z * z = 1 := by
  rw [← h.left, ← map_mul]
  have : (((-1 : SL23), (1 : SL23)) * ((-1 : SL23), (1 : SL23)) : SL23 × SL23) = 1 := by
    ext <;> simp
  rw [this, map_one]

theorem Sec5CNPi.neg_neg (h : Sec5CNPi π K₃ K₄ z) :
    π ((-1 : SL23), (-1 : SL23)) = 1 := by
  have h2 : π ((-1 : SL23), (-1 : SL23)) =
      π ((-1 : SL23), (1 : SL23)) * π ((1 : SL23), (-1 : SL23)) := by
    rw [← map_mul]
    simp
  rw [h2, h.left, h.right]
  exact h.z_sq

theorem Sec5CNPi.z_comm (h : Sec5CNPi π K₃ K₄ z) {x : G} (hx : x ∈ K₃ ⊔ K₄) :
    z * x = x * z := by
  obtain ⟨⟨u, v⟩, rfl⟩ := h.mem_iff.mp hx
  rw [← h.left, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext ?_ ?_
  · exact sec5cn_neg_one_comm u
  · simp

theorem Sec5CNPi.sign_mem (h : Sec5CNPi π K₃ K₄ z) {u v : SL23} (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) : π (u, v) = 1 ∨ π (u, v) = z := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · left
    rw [show ((1 : SL23), (1 : SL23)) = 1 from rfl, map_one]
  · right
    exact h.right
  · right
    exact h.left
  · left
    exact h.neg_neg

end CFSG.OddStandard.SmallF3.Omega
