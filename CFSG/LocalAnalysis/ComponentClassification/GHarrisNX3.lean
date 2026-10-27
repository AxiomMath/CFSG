module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisNX2

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

abbrev Nx : Subgroup G := centralizer ({D.x} : Set G)

abbrev Lx : Subgroup ↥D.Nx := D.VA.ker ⊓ D.VB.ker

instance Lx_normal : D.Lx.Normal := normal_inf_normal _ _

omit [Finite G]
  in
theorem x_mem_X : D.x ∈ D.X :=
  ⟨D.toG_mem _, mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite G]
  in
theorem y_mem_X : D.y ∈ D.X := ⟨D.toG_mem _, mem_centralizer_singleton_iff.mpr (by
  rw [← map_mul, ← map_mul, show SE.invRep 6 * SE.gen 6 = SE.gen 6 * SE.invRep 6 by decide])⟩

theorem V_x_y (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) :
    D.VA ⟨D.x, D.X_le_N D.x_mem_X⟩ = Multiplicative.ofAdd 1 ∧
      D.VB ⟨D.x, D.X_le_N D.x_mem_X⟩ = 1 ∧
      D.VB ⟨D.y, D.X_le_N D.y_mem_X⟩ = Multiplicative.ofAdd 1 := by
  have hx2 : SE.gen 6 * SE.gen 6 = 1 := by decide
  have hx1 : SE.gen 6 ≠ 1 := by decide
  have hy2 : SE.invRep 6 * SE.invRep 6 = 1 := by decide
  have hy1 : SE.invRep 6 ≠ 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [D.VA_toG hP h6 D.x_mem_X hx2 hx1 (by decide), SE.f_gen6.1]
  · rw [D.VB_toG hP h6 D.x_mem_X hx2 hx1, SE.f_gen6.2]
    rfl
  · rw [D.VB_toG hP h6 D.y_mem_X hy2 hy1, SE.f_LXX _ SE.y_mem_LXX]

theorem mem_L_mul_X (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) (n : ↥D.Nx) : ∃ l ∈ D.Lx, ∃ w : G, w ∈ D.X ∧ (n : G) = l * w := by
  obtain ⟨hAx, hBx, hBy⟩ := D.V_x_y hP h6
  set xn : ↥D.Nx := ⟨D.x, D.X_le_N D.x_mem_X⟩
  set yn : ↥D.Nx := ⟨D.y, D.X_le_N D.y_mem_X⟩
  have hsq : ∀ m : Multiplicative (ZMod 2), m ≠ 1 → m = Multiplicative.ofAdd 1 := by decide
  have h1 : ∃ n₁ : ↥D.Nx, ∃ w₁ : G, w₁ ∈ D.X ∧ (n : G) = n₁ * w₁ ∧ D.VB n₁ = 1 := by
    by_cases hb : D.VB n = 1
    · exact ⟨n, 1, one_mem _, by simp, hb⟩
    · refine ⟨n * yn, D.y⁻¹, inv_mem D.y_mem_X, by simp [yn], ?_⟩
      rw [map_mul, hsq _ hb, hBy]
      rfl
  obtain ⟨n₁, w₁, hw₁, hn₁, hb₁⟩ := h1
  by_cases ha : D.VA n₁ = 1
  · exact ⟨n₁, ⟨ha, hb₁⟩, w₁, hw₁, hn₁⟩
  · refine ⟨n₁ * xn, ⟨?_, ?_⟩, D.x⁻¹ * w₁, mul_mem (inv_mem D.x_mem_X) hw₁, ?_⟩
    · change D.VA (n₁ * xn) = 1
      rw [map_mul, hsq _ ha, hAx]
      rfl
    · change D.VB (n₁ * xn) = 1
      rw [map_mul, hb₁, hBx, one_mul]
    · rw [hn₁]
      simp [xn, mul_assoc]

theorem mem_LZX_of_mem_L (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {s : SE} (hs : D.toG s ∈ D.X) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hL : (⟨D.toG s, D.X_le_N hs⟩ : ↥D.Nx) ∈ D.Lx) : s ∈ SE.LZX := by
  obtain ⟨hA, hB⟩ := mem_inf.mp hL
  rw [MonoidHom.mem_ker] at hA hB
  rcases D.X_inv_type hP h6 hs hs2 hs1 with ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · subst h
    rw [D.VA_toG hP h6 hs hs2 hs1 (by decide), SE.f_gen6.1] at hA
    exact absurd hA (by decide)
  · rw [D.VA_toG hP h6 hs hs2 hs1 (fun h' => absurd (SE.f_LXX s h') (by
      rw [(SE.f_LXZ s h).2]; decide)), (SE.f_LXZ s h).1] at hA
    exact absurd hA (by decide)
  · rw [D.VB_toG hP h6 hs hs2 hs1, SE.f_LXX s h] at hB
    exact absurd hB (by decide)

theorem mem_L_of_LZX (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {s : SE} (hs : s ∈ SE.LZX) :
    ∃ hX : D.toG s ∈ D.X, (⟨D.toG s, D.X_le_N hX⟩ : ↥D.Nx) ∈ D.Lx := by
  have hX : D.toG s ∈ D.X := ⟨D.toG_mem s, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul]
    exact congrArg D.toG (SE.mem_Xlist_comm s (SE.LZX_sub s hs)))⟩
  have hs2 : s * s = 1 := SE.LZX_inv s hs
  have hs1 : s ≠ 1 := fun h => by subst h; exact absurd hs (by decide)
  have hXX : s ∉ SE.LXX := fun h => absurd (SE.f_LXX s h) (by rw [(SE.f_LZX s hs).2]; decide)
  refine ⟨hX, mem_inf.mpr ⟨?_, ?_⟩⟩
  · rw [MonoidHom.mem_ker, D.VA_toG hP h6 hX hs2 hs1 hXX, (SE.f_LZX s hs).1]
    rfl
  · rw [MonoidHom.mem_ker, D.VB_toG hP h6 hX hs2 hs1, (SE.f_LZX s hs).2]
    rfl

end GHSylow

end CFSG.ComponentClassification.GHarris
