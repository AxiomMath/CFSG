module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Census

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits

theorem monoW_map_iff {W U : Type*} [Group W] [Group U] (ι : W →* U)
    (hι : Function.Injective ι) (X E : Subgroup W) (pw : Bool) :
    MonoW (X.map ι) pw (E.map ι) ↔ MonoW X pw E := by
  unfold MonoW
  rw [← map_nE ι hι, pWitness_map_iff ι hι]
  constructor
  · rintro (⟨_, ⟨w, hw, rfl⟩, h4⟩ | h)
    · exact Or.inl ⟨w, hw, by rwa [orderOf_injective ι hι] at h4⟩
    · exact Or.inr h
  · rintro (⟨w, hw, h4⟩ | h)
    · exact Or.inl ⟨ι w, ⟨w, hw, rfl⟩, by rwa [orderOf_injective ι hι]⟩
    · exact Or.inr h

variable {n : ℕ} [NeZero n] {ps : List ℕ} {fuel : ℕ} {inX inW : Array ℕ → Bool} {pw : Bool}
  {bmode : ℕ} {X W : Subgroup (Equiv.Perm (Fin n))} {rs : List RootCert}

omit [NeZero n] in
theorem card_centralizer_subtype (x : ↥W) :
    Nat.card ↥(centralizer ({x} : Set ↥W)) =
      Nat.card ↥(W ⊓ centralizer ({(x : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))) := by
  rw [← card_map_of_injective W.subtype_injective, map_centralizer_singleton W.subtype
    W.subtype_injective, range_subtype]
  rfl

end CFSG.ComponentClassification.RankTwoSporadic
