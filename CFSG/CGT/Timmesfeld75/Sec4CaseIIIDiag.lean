module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB3

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T L V V₁ V₂ : Subgroup G}

theorem conj_mul_typ (hT : IsElemAbelian 2 T) (hLT : L ≤ T)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {x x' s s' : G}
    (hx : ∀ r ∈ T, x * r * x⁻¹ * r⁻¹ ∈ L) (hs' : s' ∈ T) (hs : s ∈ T)
    (hxs : conjSubgroup x V = conjSubgroup s V) (hxs' : conjSubgroup x' V = conjSubgroup s' V) :
    conjSubgroup (x * x') V = conjSubgroup (s' * s) V := by
  have hw : x * s' * x⁻¹ * s'⁻¹ ∈ L := hx s' hs'
  set w : G := x * s' * x⁻¹ * s'⁻¹ with hwdef
  have hxs'eq : x * s' = w * s' * x := by rw [hwdef]; group
  have hwV : conjSubgroup w V = V := mem_normalizer_iff_conjSubgroup_eq.1 (hLV hw)
  have hcomm : w * (s' * s) = (s' * s) * w :=
    elemAbelian_mul_comm hT (hLT hw) (T.mul_mem hs' hs)
  calc conjSubgroup (x * x') V = conjSubgroup x (conjSubgroup x' V) :=
        (conjSubgroup_conjSubgroup _ _ _).symm
    _ = conjSubgroup x (conjSubgroup s' V) := by rw [hxs']
    _ = conjSubgroup (x * s') V := conjSubgroup_conjSubgroup _ _ _
    _ = conjSubgroup (w * s' * x) V := by rw [hxs'eq]
    _ = conjSubgroup w (conjSubgroup s' (conjSubgroup x V)) := by
        rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    _ = conjSubgroup w (conjSubgroup s' (conjSubgroup s V)) := by rw [hxs]
    _ = conjSubgroup (w * (s' * s)) V := by
        rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
        congr 1
        group
    _ = conjSubgroup ((s' * s) * w) V := by rw [hcomm]
    _ = conjSubgroup (s' * s) (conjSubgroup w V) := (conjSubgroup_conjSubgroup _ _ _).symm
    _ = conjSubgroup (s' * s) V := by rw [hwV]

theorem conj_eq_of_mem {V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {x s₁ s₂ : G}
    (h : s₁⁻¹ * s₂ ∈ L) (hx : conjSubgroup x V = conjSubgroup s₂ V) :
    conjSubgroup x V = conjSubgroup s₁ V := by
  have hV : conjSubgroup (s₁⁻¹ * s₂) V = V := mem_normalizer_iff_conjSubgroup_eq.1 (hLV h)
  rw [hx]
  calc conjSubgroup s₂ V = conjSubgroup (s₁ * (s₁⁻¹ * s₂)) V := by rw [mul_inv_cancel_left]
    _ = conjSubgroup s₁ (conjSubgroup (s₁⁻¹ * s₂) V) := (conjSubgroup_conjSubgroup _ _ _).symm
    _ = conjSubgroup s₁ V := by rw [hV]

theorem exists_diag_conj [Finite G] (hT : IsElemAbelian 2 T) (hLT : L ≤ T)
    (hcard : Nat.card T = Nat.card L * 2) (hLV₁ : L ≤ Subgroup.normalizer (V₁ : Set G))
    (hLV₂ : L ≤ Subgroup.normalizer (V₂ : Set G)) {x y : G}
    (hx : ∀ r ∈ T, x * r * x⁻¹ * r⁻¹ ∈ L)
    (hx₁ : ∃ s ∈ T, conjSubgroup x V₁ = conjSubgroup s V₁)
    (hx₂ : ∃ s ∈ T, conjSubgroup x V₂ = conjSubgroup s V₂)
    (hy₁ : ∃ s ∈ T, conjSubgroup y V₁ = conjSubgroup s V₁)
    (hy₂ : ∃ s ∈ T, conjSubgroup y V₂ = conjSubgroup s V₂) :
    (∃ s ∈ T, conjSubgroup x V₁ = conjSubgroup s V₁ ∧ conjSubgroup x V₂ = conjSubgroup s V₂) ∨
    (∃ s ∈ T, conjSubgroup y V₁ = conjSubgroup s V₁ ∧ conjSubgroup y V₂ = conjSubgroup s V₂) ∨
    (∃ s ∈ T, conjSubgroup (x * y) V₁ = conjSubgroup s V₁ ∧
      conjSubgroup (x * y) V₂ = conjSubgroup s V₂) := by
  obtain ⟨s₁, hs₁, hxs₁⟩ := hx₁
  obtain ⟨s₂, hs₂, hxs₂⟩ := hx₂
  obtain ⟨r₁, hr₁, hyr₁⟩ := hy₁
  obtain ⟨r₂, hr₂, hyr₂⟩ := hy₂
  by_cases hδx : s₁⁻¹ * s₂ ∈ L
  · exact Or.inl ⟨s₁, hs₁, hxs₁, conj_eq_of_mem hLV₂ hδx hxs₂⟩
  by_cases hδy : r₁⁻¹ * r₂ ∈ L
  · exact Or.inr (Or.inl ⟨r₁, hr₁, hyr₁, conj_eq_of_mem hLV₂ hδy hyr₂⟩)
  refine Or.inr (Or.inr ⟨r₁ * s₁, T.mul_mem hr₁ hs₁, ?_, ?_⟩)
  · exact conj_mul_typ hT hLT hLV₁ hx hr₁ hs₁ hxs₁ hyr₁
  · have h1 : conjSubgroup (x * y) V₂ = conjSubgroup (r₂ * s₂) V₂ :=
      conj_mul_typ hT hLT hLV₂ hx hr₂ hs₂ hxs₂ hyr₂
    refine conj_eq_of_mem hLV₂ ?_ h1
    have hp : s₁⁻¹ * s₂ ∈ T := T.mul_mem (T.inv_mem hs₁) hs₂
    have hq : r₁⁻¹ * r₂ ∈ T := T.mul_mem (T.inv_mem hr₁) hr₂
    have hpq := mul_mem_of_not_mem_of_card hLT hcard hp hq hδx hδy
    have hc : (r₁⁻¹ * r₂) * s₂ = s₂ * (r₁⁻¹ * r₂) := elemAbelian_mul_comm hT hq hs₂
    have e : (r₁ * s₁)⁻¹ * (r₂ * s₂) = (s₁⁻¹ * s₂) * (r₁⁻¹ * r₂) := by
      calc (r₁ * s₁)⁻¹ * (r₂ * s₂) = s₁⁻¹ * ((r₁⁻¹ * r₂) * s₂) := by group
        _ = s₁⁻¹ * (s₂ * (r₁⁻¹ * r₂)) := by rw [hc]
        _ = (s₁⁻¹ * s₂) * (r₁⁻¹ * r₂) := by group
    rw [e]
    exact hpq

end CFSG.CGT.Timmesfeld75
