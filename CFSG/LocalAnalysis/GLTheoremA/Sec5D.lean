module

public import CFSG.LocalAnalysis.GLTheoremA.Sec5B

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def Prop55At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0Max p B x L ∧
    ∃ T : Subgroup G, T ≤ L ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) ∧
      T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)

variable {G : Type} [Group G] [Finite G]

theorem prop58 {p : ℕ} (hc : Sec5Ctx G p) (h51 : Prop51At G p) (h55 : Prop55At G p) :
    ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L := by
  obtain ⟨B, x, L, hBxL, hT⟩ := h55
  exact ⟨B, x, L, hBxL, prop53 hc h51 hBxL hT⟩

theorem stage5_of {p : ℕ} (hc : Sec5Ctx G p) (h51 : Prop51At G p) (h55 : Prop55At G p) :
    Stage5 G p :=
  ⟨prop58 hc h51 h55, h51, fun _ _ _ hBxL hT => prop53 hc h51 hBxL hT⟩

end CFSG.LocalAnalysis.GLTheoremA
