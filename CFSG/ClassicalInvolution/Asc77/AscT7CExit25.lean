module

public import CFSG.ClassicalInvolution.Asc77.AscT7CSetup25

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_19_chain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp23Setting p f Ω K K' z → Hyp25Data Ω K K' W S R R' z t u₁ u₂ →
      ¬ Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∃ U V W' : Subgroup G, SymplecticBlockPair (GaloisField p f) W' U V ∧ U ⊔ V = ⊤

@[expose] def C25_21_chain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp23Setting p f Ω K K' z → Hyp25Data Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        (piSign p f = true → ∃ U : Fin 3 → Subgroup G, PhanChain3 p f U) ∧
        (piSign p f = false → ∃ U : Fin 3 → Subgroup G, LinearChain3 p f U)

variable {p f}

theorem c25_19_of (hchain : C25_19_chain p f) : C25_19 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  by_cases h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')
  · exact Or.inl h4
  · right
    have hst : AscStand p f Ω K := hyp.std.1.stand
    obtain ⟨U, V, W', hpair, hgen⟩ := hchain G Ω K K' W S R R' z t u₁ u₂ hyp.std.setting
      hyp.data h4
    exact Or.inl (Or.inl (oddLieType_of_symplecticPair hst.odd hst.five
      (T7C.exists_not_commute_of_stand hst) hpair hgen))

theorem c25_21_of (hchain : C25_21_chain p f) : C25_21 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  have hst : AscStand p f Ω K := hyp.std.1.stand
  have hnab : ∃ a b : G, a * b ≠ b * a := T7C.exists_not_commute_of_stand hst
  obtain ⟨hphan, hlin⟩ := hchain G Ω K K' W S R R' z t u₁ u₂ hyp.std.setting hyp.data h4
  refine Or.inl (Or.inl ?_)
  cases hπ : piSign p f
  · obtain ⟨U, hU⟩ := hlin hπ
    exact oddLieType_of_linearChain3 hst.odd hst.five hnab hU
  · obtain ⟨U, hU⟩ := hphan hπ
    exact oddLieType_of_phanChain3 hst.odd hst.five hnab hU

theorem c25_E4_of_inputs (hRS : C25_RS p f) (h19 : C25_19_chain p f) (h21 : C25_21_chain p f) :
    C25_E4 p f :=
  c25_E4_of_steps (c25_setup_of hRS) (c25_19_of h19) (c25_21_of h21)

end CFSG.ClassicalInvolution.Asc77
