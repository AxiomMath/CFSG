module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SChar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4SParity

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

section Model


theorem td4_index_odd {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 r f) {u : Y} (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ k : ℕ, Odd k ∧ Nat.card Y = Nat.card ↥(centralizer ({u} : Set Y)) * k := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have htw : TwistedChevalleyModel Y .D4 (r ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_D4 hr hr2 hm u (orderOf_eq_two_of_inv hu hu1)
  have hq : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
  have hodd₁ : Odd (Nat.card F₁) := by rw [hc₁]; exact hq.pow
  have hodd₂ : Odd (Nat.card F₂) := by rw [hc₂]; exact hq
  have hD : Nat.card ↥(centralizer ({u} : Set Y)) =
      Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) * (Nat.card F₂ * (Nat.card F₂ ^ 2 - 1)) :=
    shape_card S hodd₁ hodd₂
  have hY : Nat.card Y = CFSG.Open.ordTrialityD4 (r ^ f) :=
    CFSG.ClassicalInvolution.card_of_twistedChevalleyModel_D4_of_ne_two hr hr2 hf htw
  refine ⟨(r ^ f) ^ 8 * ((r ^ f) ^ 8 + (r ^ f) ^ 4 + 1), ?_, ?_⟩
  · have hq8 : Odd ((r ^ f) ^ 8) := hq.pow
    have hq4 : Odd ((r ^ f) ^ 4) := hq.pow
    exact hq8.mul (Even.add_one (hq8.add_odd hq4))
  · rw [hY, hD, hc₁, hc₂]
    set q := r ^ f with hqdef
    have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hr.pos
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h6' : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    unfold CFSG.Open.ordTrialityD4
    zify [h2, h6, h6']
    ring

theorem td4_noPNorm_char {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 r f) {u : Y} (hu : u * u = 1) (hu1 : u ≠ 1)
    {X : Subgroup Y} (hX : IsPGroup r ↥X) (hX1 : X ≠ ⊥)
    (hN : centralizer ({u} : Set Y) ≤ normalizer (X : Set Y)) : False := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk, hY⟩ := td4_index_odd hr hr2 hf hm hu hu1
  exact noPNorm_char_glue hm (by decide) (fun S P hP hS => td4_parity hr hr2 hf hm S P hP hS) hk hY
    hX hX1 hN

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
