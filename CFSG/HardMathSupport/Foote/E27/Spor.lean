module

public import CFSG.HardMathSupport.Foote.E27.SporCore
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def E27SporBig : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X), E27Config X K R T z → z ∈ K →
    ∀ s : TauCeti.SporadicName, 3 ^ 5 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group →
      Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) → False

theorem e27SporSlice_of_outer_big
    (hOut : ∀ s : TauCeti.SporadicName,
      ¬ 3 ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)) (h : E27SporBig) :
    E27SporSlice := by
  intro X _ _ K R T z hc s ⟨e⟩
  have hOutK : ¬ 3 ∣ Nat.card (Outer ↥K) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact hOut s
  have h5 : 3 ^ 5 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group := by
    rw [← Nat.card_congr e.toEquiv]
    exact hc.three_pow_five_dvd_card_of_not_dvd_outer hOutK
  exact h X K R T z hc (hc.mem_of_not_dvd_outer hOutK) s h5 ⟨e⟩

section Certificates


theorem e27SporSlice_of_big (h : E27SporBig) : E27SporSlice :=
  e27SporSlice_of_outer_big
    (fun s => CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s 3 Nat.prime_three (by norm_num)) h

end Certificates

end CFSG.HardMathSupport.Foote.E27
