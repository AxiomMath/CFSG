module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Alt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67J1Red

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint

@[expose] def CF67NonAltJ1 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (J : Subgroup N), IsComponent J →
    GHList (↥J ⧸ Subgroup.center ↥J) →
    (∀ n : ℕ, 7 ≤ n → n ≤ 11 → ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin n))) →
    ¬ NativeSporadic.IsSporadic (↥J ⧸ Subgroup.center ↥J) .J1 →
    ∀ (r : ℕ), r.Prime → Odd r → ∀ (V Z : Subgroup N),
      IsElementaryAbelian r ↥V → Nat.card ↥V = r ^ 2 →
      (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → Odd (Nat.card ↥Z) → Nat.Coprime (Nat.card ↥Z) r →
      (∀ v ∈ V, ∀ w ∈ Z, v * w = w * v) →
      V ≤ normalizer (J : Set N) → Z ≤ normalizer (J : Set N) →
      (∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N)) →
      ¬ J ≤ centralizer (Z : Set N) →
      (∀ v ∈ V, v ≠ 1 → ∀ c ∈ J, c ∈ centralizer ({v} : Set N) → c ∈ normalizer (Z : Set N)) →
      False

theorem cf67NonAlt_of_nonAltJ1
    (h : CF67NonAltJ1) : CF67NonAlt := by
  intro N _ _ J hJ hGH halt r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  by_cases hj1 : NativeSporadic.IsSporadic (↥J ⧸ Subgroup.center ↥J) .J1
  · obtain ⟨θ⟩ := hj1
    exact cf67_j1 J hJ θ hr hr2 V hVc hVn hfaith
  · exact h N J hJ hGH halt hj1 r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3

end CFSG.GH74.GLS.Stage2.Bender.Thm1
