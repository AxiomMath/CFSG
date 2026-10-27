module

public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem inCatalog_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.Assembly.InCatalog Y) : CFSG.Assembly.InCatalog X :=
  CFSG.Assembly.inCatalog_isoInvariant e h

theorem k_proper_local {G : Type} [Group G] [Finite G] (hG : CFSG.IsKProper G) :
    (∀ H : Subgroup G, H < ⊤ → CFSG.IsKGroup H) ∧
      (IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
        (∀ x : G, x ≠ 1 → CFSG.IsKGroup (centralizer ({x} : Set G))) ∧
        ∀ P : Subgroup G, P ≠ ⊥ → P ≠ ⊤ → CFSG.IsKGroup (normalizer (P : Set G))) := by
  refine ⟨fun H hH => hG H hH.ne, fun hs hnab => ⟨fun x hx => hG _ ?_, fun P hP1 hP2 => hG _ ?_⟩⟩
  · intro htop
    have hxc : x ∈ center G := by
      rw [mem_center_iff]
      intro g
      have : g ∈ centralizer ({x} : Set G) := htop ▸ mem_top g
      exact (mem_centralizer_iff.1 this x rfl).symm
    have hcbot : center G = ⊥ := by
      have := hs
      rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hnab
        exact absurd (mem_center_iff.1 (h ▸ mem_top b : b ∈ center G) a) hab
    rw [hcbot, mem_bot] at hxc
    exact hx hxc
  · intro htop
    have hPn : P.Normal := normalizer_eq_top_iff.1 htop
    have := hs
    rcases hPn.eq_bot_or_eq_top with h | h
    · exact hP1 h
    · exact hP2 h

theorem isKProper_of_kProper {G : Type} [Group G] [Finite G]
    (h : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) : CFSG.IsKProper G :=
  CFSG.KCore.KProperNonab.kProperAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple h

end CFSG.LocalAnalysis.ComponentInitial
