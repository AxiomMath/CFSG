module

public import CFSG.Fischer.Classification.PartIII.Symp.Residual
public import CFSG.Fischer.Classification.PartIII.Symp.Minus

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open Matrix

@[expose] def MinusSixLocal (H : Type) [Group H] (F : Set H) : Prop :=
  ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2),
    (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
    2 ^ (2 * 3 - 1) < {v | Q v = 1}.ncard ∧
    fischerLinearModel F
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)

@[expose] def ThreeCommutingLines {X : Type} [Group X] (M : Set X) : Prop :=
  ∃ a₁ b₁ a₂ b₂ a₃ b₃ : X, b₁ * a₁ ≠ a₁ * b₁ ∧ b₂ * a₂ ≠ a₂ * b₂ ∧ b₃ * a₃ ≠ a₃ * b₃ ∧
    M = {a₁, b₁, a₁ * b₁ * a₁} ∪ {a₂, b₂, a₂ * b₂ * a₂} ∪ {a₃, b₃, a₃ * b₃ * a₃} ∧
    (∀ x ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set X), ∀ y ∈ ({a₂, b₂, a₂ * b₂ * a₂} : Set X),
      x * y = y * x) ∧
    (∀ x ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set X), ∀ y ∈ ({a₃, b₃, a₃ * b₃ * a₃} : Set X),
      x * y = y * x) ∧
    (∀ x ∈ ({a₂, b₂, a₂ * b₂ * a₂} : Set X), ∀ y ∈ ({a₃, b₃, a₃ * b₃ * a₃} : Set X),
      x * y = y * x)

variable {G : Type} [Group G] {D : Set G}

theorem minusSixLocal_of_localSymp (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (hloc : LocalSympCases (LocalQuotient D d) (LocalImages D d)) :
    MinusSixLocal (LocalQuotient D d) (LocalImages D d) := by
  rcases sympResidual_of_localSymp hH hna hnot hd hloc with ⟨φ, hφ⟩ |
    ⟨m, hm, Q, hnd, -, hQ, hmod⟩
  · exact (false_of_localSym5 hH hna hnot hd φ hφ).elim
  · rcases Nat.lt_or_ge m 4 with h4 | h4
    · by_cases h3 : m = 3
      · subst h3
        exact ⟨Q, hnd, hQ, hmod⟩
      · exact (false_of_localO_residual hH hna hnot hd (Or.inl (by omega)) hnd hQ hmod).elim
    · exact (false_of_localO_residual hH hna hnot hd (Or.inr h4) hnd hQ hmod).elim

theorem threeCommutingLines_of_minusSixLocal (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (h6 : MinusSixLocal (LocalQuotient D d) (LocalImages D d)) :
    D.ncard = 117 ∧ ∀ c ∈ D, c * d ≠ d * c → ThreeCommutingLines (muSet D d c) := by
  obtain ⟨Q, hnd, hQ, hmod⟩ := h6
  exact ⟨(params_of_localO6 hH hna hnot hd hnd hQ hmod).1, fun c hc hcd =>
    muSet_eq_three_lines_of_localO6 hH hna hnot hd hnd hQ hmod hc hcd⟩

theorem classicalPartIII_symp_of_minusSix
    (h6 : ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
      NonabelianCommutator G → ¬ IsSymplecticType D →
      ∀ d ∈ D, (LocalClass D d).Nonempty → Hyp (LocalQuotient D d) (LocalImages D d) →
        Nat.card (LocalQuotient D d) < Nat.card G →
        MinusSixLocal (LocalQuotient D d) (LocalImages D d) → D.ncard = 117 →
        (∀ c ∈ D, c * d ≠ d * c → ThreeCommutingLines (muSet D d c)) →
        ClassicalConclusion G D) :
    ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
      NonabelianCommutator G → ¬ IsSymplecticType D →
      ∀ d ∈ D, (LocalClass D d).Nonempty → Hyp (LocalQuotient D d) (LocalImages D d) →
        Nat.card (LocalQuotient D d) < Nat.card G →
        LocalSympCases (LocalQuotient D d) (LocalImages D d) → ClassicalConclusion G D := by
  intro G _ D hb hH hna hnot d hd hne hHl hlt hloc
  have hm6 := minusSixLocal_of_localSymp hH hna hnot hd hloc
  obtain ⟨h117, hlines⟩ := threeCommutingLines_of_minusSixLocal hH hna hnot hd hm6
  exact h6 G D hb hH hna hnot d hd hne hHl hlt hm6 h117 hlines

end CFSG.Fischer.Classification
