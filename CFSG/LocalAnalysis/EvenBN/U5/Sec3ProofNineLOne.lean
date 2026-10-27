module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace S3e2

open Subgroup
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

variable {G : Type} [Group G] [Finite G]

abbrev L1 (D N₁ : Subgroup G) : Subgroup G :=
  D ⊔ closure {x | ∃ g ∈ normalizer (D : Set G), ∃ n ∈ N₁, x = g * n * g⁻¹}

theorem bar_L1 {D N₁ : Subgroup G} (hN : N₁ ≤ normalizer (D : Set G)) :
    bar D (L1 D N₁) = normalClosure ((bar D N₁ : Subgroup (Bar D)) : Set (Bar D)) := by
  apply le_antisymm
  ·
    have hle : L1 D N₁ ≤ lift (normalClosure ((bar D N₁ : Subgroup (Bar D)) : Set (Bar D))) := by
      refine sup_le (le_lift _) ((closure_le _).2 ?_)
      rintro _ ⟨g, hg, n, hn, rfl⟩
      have hx : g * n * g⁻¹ ∈ normalizer (D : Set G) :=
        mul_mem (mul_mem hg (hN hn)) (inv_mem hg)
      refine mem_lift_of_proj_mem (x := ⟨g * n * g⁻¹, hx⟩) ?_
      have : (⟨g * n * g⁻¹, hx⟩ : normalizer (D : Set G)) =
          ⟨g, hg⟩ * ⟨n, hN hn⟩ * ⟨g, hg⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      exact (normalClosure_normal).conj_mem _
        (subset_normalClosure (proj_mem_bar (x := ⟨n, hN hn⟩) hn)) (proj D ⟨g, hg⟩)
    calc bar D (L1 D N₁) ≤ bar D (lift (normalClosure ((bar D N₁ : Subgroup (Bar D)) :
          Set (Bar D)))) := bar_mono hle
      _ = _ := bar_lift _
  · haveI : (bar D (L1 D N₁)).Normal := ⟨by
      intro x hx g
      obtain ⟨g₀, rfl⟩ := proj_surjective g
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : (y : G) ∈ L1 D N₁ := hy
      have hconj : (g₀ : G) * (y : G) * (g₀ : G)⁻¹ ∈ L1 D N₁ :=
        (mem_normalizer_iff.1 (normalizer_le_normalizer_sup_closure D N₁ g₀.2) _).1 hy'
      have : proj D g₀ * proj D y * (proj D g₀)⁻¹ = proj D (g₀ * y * g₀⁻¹) := by simp
      rw [this]
      exact proj_mem_bar (x := g₀ * y * g₀⁻¹) hconj⟩
    exact normalClosure_le_normal (bar_mono (le_sup_closure D N₁))

theorem lift_bar_eq_sup {D M : Subgroup G} (hM : M ≤ normalizer (D : Set G)) :
    lift (bar D M) = D ⊔ M := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, hgM⟩ := mem_lift_iff.1 hg
    obtain ⟨m', hm', hmg⟩ := hgM
    have h1 : (m' : G)⁻¹ * g ∈ D := proj_eq_proj_iff.1 hmg
    have hm'M : (m' : G) ∈ M := hm'
    have : g = (m' : G) * ((m' : G)⁻¹ * g) := by group
    rw [this]
    exact mul_mem (mem_sup_right hm'M) (mem_sup_left h1)
  · refine sup_le (le_lift _) ?_
    intro m hm
    exact mem_lift_of_proj_mem (x := ⟨m, hM hm⟩) (proj_mem_bar (x := ⟨m, hM hm⟩) hm)

end S3e2

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec39_lOne (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (hr : d.Sec39Reduced) (hl : d.Sec39Layer) : d.L₁ = d.D ⊔ d.M₁ := by
  have hN₁D : d.N₁ ≤ normalizer (d.D : Set G) := hp.hyp.N₁_le_normalizer_D
  calc d.L₁ = lift (bar d.D d.L₁) := (lift_bar d.D_le_L₁ hp.hyp.L₁_le_normalizer_D).symm
    _ = lift (bar d.D d.M₁) := by
        rw [show bar d.D d.L₁ = bar d.D d.M₁ from
          (S3e2.bar_L1 hN₁D).trans hl.normalClosure_eq]
    _ = d.D ⊔ d.M₁ := S3e2.lift_bar_eq_sup hr.M₁_le

end Data

namespace CaseBParts

theorem sec39LOne : Sec39LOneStatement :=
  fun _ _ _ _ _ _ _ _ hp k he hr hl => Data.sec39_lOne hp k he hr hl

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
