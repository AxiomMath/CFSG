module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def Cell87Simple (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  Prop4_1a → Prop4_1b →
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X → Hyp42 (zSec z H₀ hz H₁) X →
      center ↥(layer (Sec H₀ H₁)) = ⊥ →
      F (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) →
      Concl42 k (zSec z H₀ hz H₁) p X

theorem not_kindFactorAll {k : Kind} {T : Type} [Group T] [Finite T] {p0 : ℕ} [Fact p0.Prime]
    (hp0 : p0 ≠ 2)
    (hinv : CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p0) T)
    (hord : ¬ Nat.card T ∣ Nat.factorial 11) : ¬ KindFactorAll k T := by
  intro h
  cases k with
  | g2 => exact not_isL2_of_involved hp0 hinv h
  | psp4 => exact not_isL2_of_involved hp0 hinv h
  | m12 => exact not_isL2_of_involved hp0 hinv h
  | l4 ε =>
    rcases h with h | h
    · exact not_isL2_of_involved hp0 hinv h
    · exact hord (h.card_dvd.trans ((card_alt_dvd_factorial 7 (by norm_num)).trans
        (Nat.factorial_dvd_factorial (by norm_num))))
  | mcl => exact hord (h.card_dvd (Or.inl rfl))
  | ly => exact hord (h.card_dvd (Or.inr rfl))

theorem involved_of_injective {p0 : ℕ} {T : Type} [Group T]
    (ψ : CFSG.Glauberman.qdSL p0 →* T) (hψ : Function.Injective ψ) :
    CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p0) T :=
  ⟨ψ.range, ⊥, Subgroup.normal_bot,
    ⟨(QuotientGroup.quotientBot).trans (MonoidHom.ofInjective hψ).symm⟩⟩

theorem cell87_of_simple (hInv : InvSec) {F : (Y : Type) → [Group Y] → Prop}
    (hbad : ∀ (k : Kind) (Y : Type) [Group Y], F Y → ¬ KindFactorAll k Y)
    (h : Cell87Simple F) : Cell87 F := by
  intro h1 h2 G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hF
  by_cases hZ : center ↥(layer (Sec H₀ H₁)) = ⊥
  · exact h h1 h2 G z k S hctx H₀ H₁ hz p X hsig hyp hZ hF
  · exact (hbad k _ hF (layerBar_kindFactor hInv hctx hsig hyp hZ)).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
