module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapSetting
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem false_of_shapeTwo_of_wreath (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n))
    (hdich : CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z n H)
    (hW : ∀ H : Subgroup G, WreathPair L z n H →
      ∃ (M : Subgroup G) (hC : centralizer ({z} : Set G) ≤ M) (χ : M →* Multiplicative (ZMod 2)),
        (∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m) ∧
          χ ⟨z, hC (mem_centralizer_singleton_iff.2 rfl)⟩ ≠ 1) : False := by
  rcases hdich with h1 | h1 | ⟨H, hH⟩
  · exact false_of_caseII_or h d hQ2 hu huL hu2 e (Or.inl h1)
  · exact false_of_caseII_or h d hQ2 hu huL hu2 e (Or.inr h1)
  · obtain ⟨M, hC, χ, hfus, hχ⟩ := hW H hH
    have := h.std.simple
    exact false_of_fixedPoint_thompson h.std.nonab d.order hC hfus
      (A := Multiplicative (ZMod 2))
      ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)) χ hχ

end CFSG.OddStandard.AltStdSec
