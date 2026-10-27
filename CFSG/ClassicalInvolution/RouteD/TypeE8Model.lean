module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternBasic
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal (UniversalRootDatum)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.Timmesfeld (edgeE)

variable (p f : ℕ) [Fact p.Prime]

abbrev K7 : Type := (modelUniv .E7 0 p f Fact.out).K

noncomputable abbrev D7 : UniversalRootDatum (K7 p f) := (modelUniv .E7 0 p f Fact.out).D

noncomputable abbrev F7 : Set (Subgroup (K7 p f)) := fundamentalSubgroups .E7 (D7 p f)

@[expose] def E7PairFrame : Prop :=
  ∀ R₁ ∈ F7 p f, ∀ R₂ ∈ F7 p f, Gaps.ModelAdj (Subgroup.center (K7 p f)) R₁ R₂ →
    (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂) → ∀ a b : Fin 7, edgeE 7 a b →
      ∃ g : K7 p f, R₁ = conjSub g (rankOne (D7 p f).rootGroup a) ∧
        R₂ = conjSub g (rankOne (D7 p f).rootGroup b)

@[expose] def E7Sign : Prop :=
  ∀ R₁ ∈ F7 p f, ∀ R₂ ∈ F7 p f, ∀ R₃ ∈ F7 p f,
    Gaps.ModelAdj (Subgroup.center (K7 p f)) R₁ R₂ →
    Gaps.ModelAdj (Subgroup.center (K7 p f)) R₃ R₂ → Commutes R₁ R₃ →
    (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂) →
    ∃ W, LinearBlockStandardPair (GaloisField p f) W R₂ R₃

@[expose] def E7Perp2 : Prop :=
  ∀ R₁ ∈ F7 p f, ∀ R₂ ∈ F7 p f, Gaps.ModelAdj (Subgroup.center (K7 p f)) R₁ R₂ →
    (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂) →
    ∃ S₁ ∈ F7 p f, ∃ S₂ ∈ F7 p f, S₁ ≠ S₂ ∧ Commutes R₁ S₁ ∧ Commutes R₁ S₂ ∧
      ¬ Commutes R₂ S₁ ∧ ¬ Commutes R₂ S₂

theorem signPerp_iff :
    SignPerp (F7 p f) (GaloisField p f) ↔ E7Sign p f ∧ E7Perp2 p f :=
  ⟨fun h => ⟨h.sign, h.perp2⟩, fun h => ⟨h.1, h.2⟩⟩

end CFSG.ClassicalInvolution.RouteD.TypeE8
