module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.CentralCover
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup

variable {G : Type} [Group G]

instance normal_centralizer (M : Subgroup G) [M.Normal] : (centralizer (M : Set G)).Normal where
  conj_mem x hx g := by
    rw [mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ M := by
      simpa using (inferInstance : M.Normal).conj_mem y hy g⁻¹
    have h := hx _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group

section Quot

variable (M : Subgroup G) [M.Normal]

abbrev CQ : Type := G ⧸ centralizer (M : Set G)

abbrev cq : G →* CQ M := QuotientGroup.mk' (centralizer (M : Set G))

abbrev cqM : ↥M →* CQ M := (cq M).comp M.subtype

theorem mem_ker_cq {x : G} : x ∈ (cq M).ker ↔ x ∈ centralizer (M : Set G) := by
  rw [QuotientGroup.ker_mk']

theorem cq_eq_one_iff {x : G} : cq M x = 1 ↔ x ∈ centralizer (M : Set G) :=
  QuotientGroup.eq_one_iff x

theorem ker_cqM_le_center : (cqM M).ker ≤ center ↥M := by
  intro x hx
  have hx' : (x : G) ∈ centralizer (M : Set G) := (cq_eq_one_iff M).1 hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (mem_centralizer_iff.1 hx' y y.2)

theorem range_cqM : (cqM M).range = M.map (cq M) := by
  ext y
  simp [MonoidHom.mem_range, Subgroup.mem_map]

end Quot

end CFSG.EvenSporadicStandard.Induction.Junction
