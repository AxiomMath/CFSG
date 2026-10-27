module

public import CFSG.LocalAnalysis.GH72.Sec5DBasic
public import CFSG.LocalAnalysis.GH72.OuterFacts

public section

namespace CFSG.GH72

open Subgroup

namespace G5d

variable {G : Type} [Group G]

theorem isL2OrA7_bar_of_covers {H W M₀ OM : Subgroup G} {q : ℕ} (hWH : W ≤ H) (hWM₀ : W ≤ M₀)
    (hM₀OM : M₀ ≤ normalizer (OM : Set G)) (hcov : Covers W M₀ OM) (hO : O H ⊓ W = W ⊓ OM)
    (hq : QuotIs M₀ OM (fun L _ => IsL2OrA7 L q)) : IsL2OrA7 (bar H W) q := by
  obtain ⟨L, _, f, hf, hker, hL⟩ := hq
  set π : W →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion hWH) with hπ
  set g : W →* L := f.comp (inclusion hWM₀) with hg
  have hπrange : π.range = bar H W := by
    rw [hπ, MonoidHom.range_comp, inclusion_range]
    rfl
  have hπker : ∀ w : W, w ∈ π.ker ↔ (w : G) ∈ O H := by
    intro w
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hw
      exact ⟨_, hw, rfl⟩
    · rintro ⟨y, hy, hyw⟩
      have : y = inclusion hWH w := Subtype.ext hyw
      rwa [← this]
  have hgker : ∀ w : W, w ∈ g.ker ↔ (w : G) ∈ OM := by
    intro w
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, mem_subgroupOf]
    rfl
  have hkereq : π.ker = g.ker := by
    ext w
    rw [hπker, hgker]
    constructor
    · intro hw
      have : (w : G) ∈ O H ⊓ W := ⟨hw, w.2⟩
      rw [hO] at this
      exact this.2
    · intro hw
      have : (w : G) ∈ W ⊓ OM := ⟨w.2, hw⟩
      rw [← hO] at this
      exact this.1
  have hgsurj : Function.Surjective g := by
    intro l
    obtain ⟨⟨m, hm⟩, rfl⟩ := hf l
    obtain ⟨w, ⟨hwW, hwM₀⟩, o, ho, hwo⟩ :=
      mem_sup_of_le_normalizer' (inf_le_right.trans hM₀OM) (hcov hm)
    have hoM₀ : o ∈ M₀ := by
      have : o = w⁻¹ * m := by
        rw [← hwo]
        group
      rw [this]
      exact M₀.mul_mem (M₀.inv_mem hwM₀) hm
    have hfo : f ⟨o, hoM₀⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
      exact ho
    refine ⟨⟨w, hwW⟩, ?_⟩
    have hm' : (⟨m, hm⟩ : M₀) = ⟨w, hwM₀⟩ * ⟨o, hoM₀⟩ := Subtype.ext hwo.symm
    rw [hm', map_mul, hfo, mul_one]
    rfl
  exact CFSG.GH72.isL2OrA7_of_mulEquiv ((MulEquiv.subgroupCongr hπrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange π).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkereq).trans
        (QuotientGroup.quotientKerEquivOfSurjective g hgsurj)))) hL

end G5d

end CFSG.GH72
