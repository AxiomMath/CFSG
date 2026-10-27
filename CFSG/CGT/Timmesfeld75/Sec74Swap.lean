module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem mem_normalizer_conj_involution {U V : Subgroup G} {α b : G} (hb2 : b * b = 1)
    (hV : conjSubgroup b U = V) (hα : α ∈ Subgroup.normalizer (U : Set G)) :
    b * α * b ∈ Subgroup.normalizer (V : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq] at hα ⊢
  rw [← hV, conjSubgroup_conjSubgroup]
  have e : b * α * b * b = b * α := by
    calc b * α * b * b = b * α * (b * b) := by group
      _ = b * α := by rw [hb2, mul_one]
  rw [e, ← conjSubgroup_conjSubgroup, hα]

theorem Sec6Ctx.conjSubgroup_swap (hc : Sec6Ctx T T₁ n m) {a b : G} (ha : a ∈ T) (ha1 : a ≠ 1)
    (hb2 : b * b = 1) (hab : b * a * b ∈ T₁) : conjSubgroup b T = T₁ := by
  have := hc.finite
  have hP := hc.hy.pair
  have hS3 := hc.sec3
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hy1 : b * a * b ≠ 1 := by
    intro h
    apply ha1
    calc a = (b * b) * a * (b * b) := by rw [hb2]; group
      _ = b * (b * a * b) * b := by group
      _ = 1 := by rw [h, mul_one, hb2]
  have hcent : conjSubgroup b T ≤ Subgroup.centralizer ({b * a * b} : Set G) := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ht : b * y * b ∈ T := by simpa [hbi] using hy
    have hcomm : (b * y * b) * a = a * (b * y * b) := elemAbelian_mul_comm hP.wc.1 ht ha
    calc y * (b * a * b) = b * ((b * y * b) * a) * b := by
          calc y * (b * a * b) = (b * b) * y * (b * a * b) := by rw [hb2, one_mul]
            _ = b * ((b * y * b) * a) * b := by
                calc (b * b) * y * (b * a * b) = b * (b * y * b) * (a * b) := by group
                  _ = b * ((b * y * b) * a) * b := by group
      _ = b * (a * (b * y * b)) * b := by rw [hcomm]
      _ = (b * a * b) * y := by
          calc b * (a * (b * y * b)) * b = (b * a * b) * y * (b * b) := by group
            _ = (b * a * b) * y := by rw [hb2, mul_one]
  obtain ⟨x, hx⟩ := hP.conj
  have hT : T = conjSubgroup x⁻¹ T₁ := by
    rw [hx, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hle : conjSubgroup (b * x⁻¹) T₁ ≤ Subgroup.centralizer ({b * a * b} : Set G) := by
    rw [← conjSubgroup_conjSubgroup, ← hT]
    exact hcent
  have := (hS3.cfg.wc₁.2 (b * a * b) hab hy1).2 (b * x⁻¹) hle
  rw [← conjSubgroup_conjSubgroup, ← hT] at this
  exact this

theorem conjSubgroup_swap_symm {b : G} (hb2 : b * b = 1) (h : conjSubgroup b T = T₁) :
    conjSubgroup b T₁ = T := by
  rw [← h, conjSubgroup_conjSubgroup, hb2, conjSubgroup_one]

theorem mem_normIn_swap {b α : G} (hb2 : b * b = 1) (h : conjSubgroup b T = T₁)
    (hα : α ∈ normIn T T₁) : b * α * b ∈ normIn T₁ T := by
  obtain ⟨hαT, hαN⟩ := mem_normIn.1 hα
  refine mem_normIn.2 ⟨?_, mem_normalizer_conj_involution hb2 (conjSubgroup_swap_symm hb2 h) hαN⟩
  rw [← h, mem_conjSubgroup]
  have e : b⁻¹ * (b * α * b) * b = α := by
    calc b⁻¹ * (b * α * b) * b = (b⁻¹ * b) * α * (b * b) := by group
      _ = α := by rw [hb2, inv_mul_cancel, one_mul, mul_one]
  rw [e]
  exact hαT

theorem mem_normIn_swap' {b α : G} (hb2 : b * b = 1) (h : conjSubgroup b T = T₁)
    (hα : α ∈ normIn T₁ T) : b * α * b ∈ normIn T T₁ := by
  obtain ⟨hαT, hαN⟩ := mem_normIn.1 hα
  refine mem_normIn.2 ⟨?_, mem_normalizer_conj_involution hb2 h hαN⟩
  rw [← conjSubgroup_swap_symm hb2 h, mem_conjSubgroup]
  have e : b⁻¹ * (b * α * b) * b = α := by
    calc b⁻¹ * (b * α * b) * b = (b⁻¹ * b) * α * (b * b) := by group
      _ = α := by rw [hb2, inv_mul_cancel, one_mul, mul_one]
  rw [e]
  exact hαT

end CFSG.CGT.Timmesfeld75
