module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.OrbitReps
public import CFSG.Monster.GMS.RonanTriangulable

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.B.Recog CFSG.Monster.GMS

variable {X V : Type*} [Group X] [MulAction X V] [MulAction.IsPretransitive X V]
  {Δ : SimpleGraph V}

theorem triangulable_of_ronan_of_reps
    (hΔ : ∀ (g : X) (x y : V), Δ.Adj (g • x) (g • y) ↔ Δ.Adj x y) {a₀ : V}
    (K : Subgroup X) (hK : ∀ k ∈ K, k • a₀ = a₀) {d : ℕ} (hd : ∀ v, Δ.dist a₀ v ≤ d)
    {ι : Type*} [Membership V ι] {R : ι} (hR : ∀ v, ∃ r ∈ R, ∃ k ∈ K, k • r = v)
    (hnbrs : ∀ i, 2 ≤ i → i ≤ d → ∀ r ∈ R, Δ.dist a₀ r = i →
      (Δ.induce {c | Δ.Adj a₀ c ∧ Δ.dist c r = i - 1}).Preconnected)
    (htri : ∀ i, 2 ≤ i → i ≤ d → ∀ r ∈ R, Δ.dist a₀ r = i → ∀ g, Δ.dist a₀ g = i →
      Δ.Adj r g → ∃ c c', Δ.Adj a₀ c ∧ Δ.dist c r = i - 1 ∧ Δ.Adj a₀ c' ∧
        Δ.dist c' g = i - 1 ∧ (c = c' ∨ Δ.Adj c c')) :
    Triangulable Δ :=
  triangulable_of_ronan (dist_le_of_base hΔ a₀ hd)
    (fun i hi hid a b hab =>
      (ronan_i_iff_reps hΔ K hK (fun b _ => hR b)).2 (hnbrs i hi hid) a b hab)
    (fun i hi hid a b g hab hag hbg =>
      (ronan_ii_iff_reps hΔ K hK (fun b _ => hR b)).2 (htri i hi hid) a b g hab hag hbg)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
