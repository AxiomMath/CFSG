module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Glue
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

variable {M : Type*} [Group M]

theorem false_of_F3_inner_model (N : Subgroup M) [Finite N] {Y : Type} [Group Y] (e : Y ≃* ↥N)
    (hcenter : Subgroup.center ↥N = ⊥) (hcard : Nat.card (MulAut ↥N) ≤ Nat.card ↥N)
    (reps : List M)
    (hcover : ∀ u, u ∈ N → orderOf u = 2 → ∃ r ∈ reps, ∃ d ∈ N, u = d * r * d⁻¹)
    {ps : List ℕ} (hpsOdd : ∀ p ∈ ps, p.Prime ∧ p ≠ 2)
    (hps : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥N → p ∈ ps)
    (hF : ∀ r ∈ reps, ∀ p ∈ ps, F3S N r p) {p : ℕ} {α : MulAut Y} {Xh : Subgroup Y}
    (h : QuotCfg p α Xh) : False := by
  refine QuotCfg.false_of_F3_all e (ps := ps) ?_ hps h
  intro β hβ2 q hq
  have hin : β ∈ inner ↥N := by
    by_contra hn
    exact outer_vacuous_of_card_le hcenter hcard β hn
  obtain ⟨g, hg⟩ := hin
  refine F3.of_inner (hpsOdd q hq).1 (hpsOdd q hq).2 hcenter ?_ hg.symm hβ2
  intro t ht ho
  exact F3S.of_cover (N := N) (P := fun t => t ∈ N) reps hcover (fun r hr => hF r hr q hq) t ht ho

theorem false_of_F3_model (N : Subgroup M) [Finite N] {Y : Type} [Group Y] (e : Y ≃* ↥N)
    (hcenter : Subgroup.center ↥N = ⊥) (δ : M) (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut ↥N) ≤ 2 * Nat.card ↥N) (reps repsOut : List M)
    (hcover : ∀ u, u ∈ N → orderOf u = 2 → ∃ r ∈ reps, ∃ d ∈ N, u = d * r * d⁻¹)
    (hcoverOut : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ r ∈ repsOut, ∃ d ∈ N, u = d * r * d⁻¹)
    {ps : List ℕ} (hpsOdd : ∀ p ∈ ps, p.Prime ∧ p ≠ 2)
    (hps : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥N → p ∈ ps)
    (hF : ∀ r ∈ reps, ∀ p ∈ ps, F3S N r p) (hFout : ∀ r ∈ repsOut, ∀ p ∈ ps, F3S N r p)
    {p : ℕ} {α : MulAut Y} {Xh : Subgroup Y} (h : QuotCfg p α Xh) : False := by
  refine QuotCfg.false_of_F3_all e (ps := ps) ?_ hps h
  intro β hβ2 q hq
  by_cases hin : β ∈ inner ↥N
  · obtain ⟨g, hg⟩ := hin
    refine F3.of_inner (hpsOdd q hq).1 (hpsOdd q hq).2 hcenter ?_ hg.symm hβ2
    intro t ht ho
    exact F3S.of_cover (N := N) (P := fun t => t ∈ N) reps hcover (fun r hr => hF r hr q hq) t ht ho
  · refine F3.of_outer N δ hδ hδ2 hcenter houter hcard ?_ β hβ2 hin
    intro u hu ho
    exact F3S.of_cover (N := N) (P := fun u => δ⁻¹ * u ∈ N) repsOut hcoverOut
      (fun r hr => hFout r hr q hq) u hu ho

theorem false_of_F3_autModel {N R : Subgroup M} [Finite N]
    (hA : CFSG.Sporadic.SmallOddCore.AutModel N R) {Y : Type} [Group Y] (e : Y ≃* ↥N)
    (reps : List M) (hcover : ∀ t, t ∈ R → orderOf t = 2 → ∃ r ∈ reps, ∃ d ∈ N, t = d * r * d⁻¹)
    {ps : List ℕ} (hpsOdd : ∀ p ∈ ps, p.Prime ∧ p ≠ 2)
    (hps : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥N → p ∈ ps)
    (hF : ∀ r ∈ reps, ∀ p ∈ ps, F3S N r p) {p : ℕ} {α : MulAut Y} {Xh : Subgroup Y}
    (h : QuotCfg p α Xh) : False := by
  refine QuotCfg.false_of_F3_all e (ps := ps) ?_ hps h
  intro β hβ2 q hq
  obtain ⟨x, hxR, hx⟩ := hA.surj β
  have hxx : x * x = 1 := by
    refine hA.inj (x * x) (R.mul_mem hxR hxR) fun z hz => ?_
    have hz2 := congrArg (fun φ : MulAut ↥N => (φ ⟨z, hz⟩ : M)) hβ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at hz2
    rw [hx (β ⟨z, hz⟩), hx ⟨z, hz⟩] at hz2
    calc x * x * z = x * (x * z * x⁻¹) * x⁻¹ * (x * x) := by group
      _ = z * (x * x) := by rw [hz2]
  by_cases hx1 : x = 1
  · subst hx1
    exact F3.of_F3S β (u := 1) (fun g => by rw [hx]) (F3S.one_elt (hpsOdd q hq).1 (hpsOdd q hq).2)
  · have ho : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
    exact F3.of_F3S β hx
      (F3S.of_cover (N := N) (P := fun t => t ∈ R) reps hcover (fun r hr => hF r hr q hq) x hxR ho)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
