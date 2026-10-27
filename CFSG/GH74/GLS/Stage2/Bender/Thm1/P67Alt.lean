module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67AltRed
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74

@[expose] def CF67NonAlt : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (J : Subgroup N), IsComponent J →
    GHList (↥J ⧸ Subgroup.center ↥J) →
    (∀ n : ℕ, 7 ≤ n → n ≤ 11 → ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin n))) →
    ∀ (r : ℕ), r.Prime → Odd r → ∀ (V Z : Subgroup N),
      IsElementaryAbelian r ↥V → Nat.card ↥V = r ^ 2 →
      (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → Odd (Nat.card ↥Z) → Nat.Coprime (Nat.card ↥Z) r →
      (∀ v ∈ V, ∀ w ∈ Z, v * w = w * v) →
      V ≤ normalizer (J : Set N) → Z ≤ normalizer (J : Set N) →
      (∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N)) →
      ¬ J ≤ centralizer (Z : Set N) →
      (∀ v ∈ V, v ≠ 1 → ∀ c ∈ J, c ∈ centralizer ({v} : Set N) → c ∈ normalizer (Z : Set N)) →
      False

theorem cf67_of_nonAlt (h : CF67NonAlt) : CF67 := by
  intro N _ _ J hJ hGH r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  by_cases halt : ∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin n))
  · obtain ⟨n, hn7, hn11, ⟨θ⟩⟩ := halt
    exact cf67_alt J hJ hn7 hn11 θ r hr hr2 V Z hVe hVc hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact h N J hJ hGH (fun n h7 h11 hn => halt ⟨n, h7, h11, hn⟩) r hr hr2 V Z hVe hVc hZab hZodd hZcop
      hcomm hVn hZn hfaith hZnt hP3

end CFSG.GH74.GLS.Stage2.Bender.Thm1
