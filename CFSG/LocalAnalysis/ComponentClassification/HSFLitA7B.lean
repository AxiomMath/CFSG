module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7T

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

noncomputable def coords : S.data.T ≃* DihedralGroup 4 × DihedralGroup 2 :=
  Classical.choose S.exists_coords

theorem coords_x : S.coords ⟨S.x, S.x_mem.1⟩ = (r 1, 1) :=
  (Classical.choose_spec S.exists_coords).1

theorem coords_y : S.coords ⟨S.y, S.y_mem.1⟩ = (sr 0, 1) :=
  (Classical.choose_spec S.exists_coords).2.1

theorem coords_t : S.coords ⟨S.t, S.data.t_mem_T⟩ = (1, r 1) :=
  (Classical.choose_spec S.exists_coords).2.2.1

theorem coords_k : S.coords ⟨S.k, S.k_mem⟩ = (1, sr 0) :=
  (Classical.choose_spec S.exists_coords).2.2.2

theorem coords_z : S.coords ⟨S.z, S.z_mem.1⟩ = (r 2, 1) := by
  have : (⟨S.z, S.z_mem.1⟩ : S.data.T) = (⟨S.x, S.x_mem.1⟩ : S.data.T) ^ 2 := rfl
  rw [this, map_pow, S.coords_x]
  rfl

theorem commute_of_coords {a b : X} (ha : a ∈ S.data.T) (hb : b ∈ S.data.T)
    (h : S.coords ⟨a, ha⟩ * S.coords ⟨b, hb⟩ = S.coords ⟨b, hb⟩ * S.coords ⟨a, ha⟩) :
    a * b = b * a := by
  have : (⟨a, ha⟩ : S.data.T) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    S.coords.injective (by rw [map_mul, map_mul, h])
  exact congrArg Subtype.val this

theorem B_le_T : S.B ≤ S.data.T := by
  rw [B, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact S.z_mem.1
  · exact S.data.t_mem_T
  · exact S.k_mem

theorem central_of_mem_B {g : X} (hg : g ∈ S.B) {h : X} (hh : h ∈ S.data.T) : g * h = h * g := by
  have hle : S.B ≤ centralizer (S.data.T : Set X) := by
    rw [B, closure_le]
    intro c hc
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl
    · refine (S.commute_of_coords S.z_mem.1 hh ?_).symm
      rw [S.coords_z]
      obtain ⟨p, q⟩ := S.coords ⟨h, hh⟩
      revert p q
      decide
    · exact S.data.commute_t hh
    · refine (S.commute_of_coords S.k_mem hh ?_).symm
      rw [S.coords_k]
      obtain ⟨p, q⟩ := S.coords ⟨h, hh⟩
      revert p q
      decide
  exact ((mem_centralizer_iff.mp (hle hg)) h hh).symm

theorem mem_B_iff {g : X} (hg : g ∈ S.data.T) : (∀ h ∈ S.data.T, g * h = h * g) ↔ g ∈ S.B := by
  refine ⟨fun hc => ?_, fun hB h hh => S.central_of_mem_B hB hh⟩
  have hcq : ∀ q : DihedralGroup 4 × DihedralGroup 2, S.coords ⟨g, hg⟩ * q =
      q * S.coords ⟨g, hg⟩ := by
    intro q
    obtain ⟨h, rfl⟩ := S.coords.surjective q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc h h.2)
  have key : ∀ q : DihedralGroup 4 × DihedralGroup 2,
      (∀ h : DihedralGroup 4 × DihedralGroup 2, q * h = h * q) →
      ∃ a b c : Fin 2, q = (r 2, 1) ^ (a : ℕ) * (1, r 1) ^ (b : ℕ) * (1, sr 0) ^ (c : ℕ) := by
    decide
  obtain ⟨a, b, c, habc⟩ := key _ hcq
  have hmem : S.z ^ (a : ℕ) * S.t ^ (b : ℕ) * S.k ^ (c : ℕ) ∈ S.data.T :=
    mul_mem (mul_mem (pow_mem S.z_mem.1 _) (pow_mem S.data.t_mem_T _)) (pow_mem S.k_mem _)
  have hg' : g = S.z ^ (a : ℕ) * S.t ^ (b : ℕ) * S.k ^ (c : ℕ) := by
    have : (⟨g, hg⟩ : S.data.T) = ⟨_, hmem⟩ := by
      apply S.coords.injective
      rw [habc]
      have e : (⟨S.z ^ (a : ℕ) * S.t ^ (b : ℕ) * S.k ^ (c : ℕ), hmem⟩ : S.data.T) =
          (⟨S.z, S.z_mem.1⟩ : S.data.T) ^ (a : ℕ) * (⟨S.t, S.data.t_mem_T⟩ : S.data.T) ^ (b : ℕ) *
            (⟨S.k, S.k_mem⟩ : S.data.T) ^ (c : ℕ) := rfl
      rw [e, map_mul, map_mul, map_pow, map_pow, map_pow, S.coords_z, S.coords_t, S.coords_k]
    exact congrArg Subtype.val this
  rw [hg', B]
  exact mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
    (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)

theorem sq_of_mem_B {g : X} (hg : g ∈ S.B) : g ^ 2 = 1 := by
  have hgT := S.B_le_T hg
  have hc : ∀ h ∈ S.data.T, g * h = h * g := (S.mem_B_iff hgT).mpr hg
  have hcq : ∀ q : DihedralGroup 4 × DihedralGroup 2, S.coords ⟨g, hgT⟩ * q =
      q * S.coords ⟨g, hgT⟩ := by
    intro q
    obtain ⟨h, rfl⟩ := S.coords.surjective q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc h h.2)
  have key : ∀ q : DihedralGroup 4 × DihedralGroup 2,
      (∀ h : DihedralGroup 4 × DihedralGroup 2, q * h = h * q) → q ^ 2 = 1 := by decide
  have h1 := key _ hcq
  have : (⟨g, hgT⟩ : S.data.T) ^ 2 = 1 := S.coords.injective (by rw [map_pow, h1, map_one])
  exact congrArg Subtype.val this

theorem commutator_eq {a b : X} (ha : a ∈ S.data.T) (hb : b ∈ S.data.T) :
    a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = S.z := by
  have key : ∀ p q : DihedralGroup 4 × DihedralGroup 2,
      p * q * p⁻¹ * q⁻¹ = 1 ∨ p * q * p⁻¹ * q⁻¹ = (r 2, 1) := by decide
  have hm : a * b * a⁻¹ * b⁻¹ ∈ S.data.T :=
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have e : (⟨a * b * a⁻¹ * b⁻¹, hm⟩ : S.data.T) =
      ⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : S.data.T)⁻¹ * (⟨b, hb⟩ : S.data.T)⁻¹ := rfl
  rcases key (S.coords ⟨a, ha⟩) (S.coords ⟨b, hb⟩) with h | h
  · left
    have : (⟨a * b * a⁻¹ * b⁻¹, hm⟩ : S.data.T) = 1 := S.coords.injective (by
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨a * b * a⁻¹ * b⁻¹, hm⟩ : S.data.T) = ⟨S.z, S.z_mem.1⟩ := S.coords.injective (by
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h, S.coords_z])
    exact congrArg Subtype.val this

theorem commutator_x_y : S.x * S.y * S.x⁻¹ * S.y⁻¹ = S.z := by
  have hy : S.y * S.x⁻¹ * S.y⁻¹ = S.x := by
    have := S.y_x_y
    calc S.y * S.x⁻¹ * S.y⁻¹ = (S.y * S.x * S.y⁻¹)⁻¹ := by group
      _ = S.x := by rw [this, inv_inv]
  calc S.x * S.y * S.x⁻¹ * S.y⁻¹ = S.x * (S.y * S.x⁻¹ * S.y⁻¹) := by group
    _ = S.x ^ 2 := by rw [hy, pow_two]

theorem conj_z_eq {w : X} (hw : w ∈ normalizer (S.data.T : Set X)) : w * S.z * w⁻¹ = S.z := by
  have hx := S.data.conj_mem_T hw S.x_mem.1
  have hy := S.data.conj_mem_T hw S.y_mem.1
  have h := S.commutator_eq hx hy
  have e : (w * S.x * w⁻¹) * (w * S.y * w⁻¹) * (w * S.x * w⁻¹)⁻¹ * (w * S.y * w⁻¹)⁻¹ =
      w * S.z * w⁻¹ := by rw [← S.commutator_x_y]; group
  rw [e] at h
  rcases h with h | h
  · exfalso
    apply S.z_ne_one
    calc S.z = w⁻¹ * (w * S.z * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem conj_mem_B {w : X} (hw : w ∈ normalizer (S.data.T : Set X)) {b : X} (hb : b ∈ S.B) :
    w * b * w⁻¹ ∈ S.B := by
  have hbT := S.B_le_T hb
  rw [← S.mem_B_iff (S.data.conj_mem_T hw hbT)]
  intro h hh
  have hh' := S.data.conj_inv_mem_T hw hh
  have := S.central_of_mem_B hb hh'
  calc w * b * w⁻¹ * h = w * (b * (w⁻¹ * h * w)) * w⁻¹ := by group
    _ = w * ((w⁻¹ * h * w) * b) * w⁻¹ := by rw [this]
    _ = h * (w * b * w⁻¹) := by group

end A7Base

end CFSG.ComponentClassification.HSFLit
