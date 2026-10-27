module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CGT.Foote81L6.TStruct.Classes

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct CFSG.ABGLocalTools

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem zpowers_b_le_B₀B₁ : zpowers D.b₀ ⊔ zpowers D.b₁ ≤ D.B₀ ⊔ D.B₁ :=
  sup_le (zpowers_le.2 (mem_sup_left D.b₀_mem)) (zpowers_le.2 (mem_sup_right D.b₁_mem))

theorem comm_of_mem_zpowers_b {z w : G} (hz : z ∈ zpowers D.b₀ ⊔ zpowers D.b₁)
    (hw : w ∈ D.B₀ ⊔ D.B₁) : w * z = z * w := by
  refine (comm_of_mem_sup (g := w) (fun x hx => ?_) (fun x hx => ?_) hz).symm
  · rcases eq_one_or_eq_of_mem_zpowers D.b₀_mul_b₀ hx with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (D.b₀_comm_B₀B₁ hw).symm
  · rcases eq_one_or_eq_of_mem_zpowers D.b₁_mul_b₁ hx with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (D.b₁_comm_B₀B₁ hw).symm

theorem conj_mem_zpowers_b {g z : G} (hg : g ∈ T) (hz : z ∈ zpowers D.b₀ ⊔ zpowers D.b₁) :
    g * z * g⁻¹ ∈ zpowers D.b₀ ⊔ zpowers D.b₁ := by
  have hmem := D.conj_mem_B₀B₁ hg (D.zpowers_b_le_B₀B₁ hz)
  have hcen : ∀ w ∈ D.B₀ ⊔ D.B₁, w * (g * z * g⁻¹) = (g * z * g⁻¹) * w := by
    intro w hw
    have hw' : g⁻¹ * w * g ∈ D.B₀ ⊔ D.B₁ := by
      have := D.conj_mem_B₀B₁ (inv_mem hg) hw
      rwa [inv_inv] at this
    have h := D.comm_of_mem_zpowers_b hz hw'
    calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
      _ = (g * z * g⁻¹) * w := by group
  rcases D.eq_of_comm_B₀B₁ hmem hcen with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact mem_sup_left (mem_zpowers _)
  · exact mem_sup_right (mem_zpowers _)
  · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem le_normalizer_Z :
    T ≤ normalizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_self_of_mem_normalizer (D.T_le_normalizer_A hg)]
  congr 1
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact D.conj_mem_zpowers_b hg hz
  · intro z hz
    refine ⟨g⁻¹ * z * g, ?_, by simp [mul_assoc]⟩
    have := D.conj_mem_zpowers_b (inv_mem hg) hz
    rwa [inv_inv] at this

theorem centralizer_Z (hm : m = 2) :
    T ⊓ centralizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G) = D.T₁ := by
  have hAA : IsFourIn D.A D.A := D.repU_eq_A hm ▸ D.isFourIn_repU
  have hAc : ∀ x ∈ D.A, ∀ y ∈ D.A, x * y = y * x := fun x hx y hy =>
    comm_of_mul_self hAA.2.1 hx hy
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxc⟩ := mem_inf.1 hx
    have hc : ∀ z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), z * x = x * z :=
      mem_centralizer_iff.1 hxc
    have hx0 : x ∈ D.T₀ := D.mem_T₀_of_comm_four hAA hxT fun u hu => (hc u (mem_sup_left hu)).symm
    by_contra hx1
    have h := D.conj_b₀_of_not_mem_T₁ hx0 hx1
    rw [← hc D.b₀ (mem_sup_right (mem_sup_left (mem_zpowers _))), mul_inv_cancel_right] at h
    exact D.b₀_ne_b₁ h
  · intro x hx
    refine mem_inf.2 ⟨D.T₁_le_T hx, mem_centralizer_iff.2 fun z hz => ?_⟩
    obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hx
    refine comm_of_mem_sup (g := α * w) (fun y hy => ?_) (fun y hy => ?_) hz
    · calc y * (α * w) = (y * α) * w := by group
        _ = (α * y) * w := by rw [hAc y hy α hα]
        _ = α * (y * w) := by group
        _ = α * (w * y) := by rw [D.A_comm_B₀B₁ y hy w hw]
        _ = α * w * y := by group
    · have h1 : y * w = w * y := (D.comm_of_mem_zpowers_b hy hw).symm
      have h2 : y * α = α * y :=
        (D.A_comm_B α hα y (D.B₀B₁_le_B (D.zpowers_b_le_B₀B₁ hy))).symm
      calc y * (α * w) = (y * α) * w := by group
        _ = α * (y * w) := by rw [h2]; group
        _ = α * w * y := by rw [h1]; group

end FooteCore

theorem FooteCore.sylow_centralizer_Z {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {m n : ℕ}
    (D : FooteCore G (T : Subgroup G) m n) (hm : m = 2) :
    ∃ P : Sylow 2 ↥(centralizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G)),
      (P : Subgroup _) = D.T₁.subgroupOf
        (centralizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G)) := by
  have hTK : IsSylowOf 2 (T : Subgroup G)
      (normalizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G)) := by
    rw [isSylowOf_iff]
    exact ⟨D.le_normalizer_Z, T.isPGroup', fun h =>
      T.not_dvd_index (h.trans (relIndex_dvd_index_of_le D.le_normalizer_Z))⟩
  have hNK := centralizer_le_normalizer
    ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G)
  have hKN : normalizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G) ≤
      normalizer ((centralizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G) :
        Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hNK).1 inferInstance
  have h := hTK.inf_of_le_normalizer hNK hKN
  rw [D.centralizer_Z hm] at h
  exact h.exists_sylow_eq_subgroupOf

end CFSG.CGT.Foote81L6
