module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4ThreeSixAux.Three
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialSet

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.SimplyLacedCover
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words
open scoped commutatorElement

set_option linter.unusedSectionVars false

set_option maxRecDepth 200000 in
theorem certCheck_D4 : certCheck .D4 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel


theorem commute_xOp_yOp_D4 {R : Type} [CommRing R] (h2 : (2 : R) = 0)
    (z : Module.End R (RootModule Tag.D4 R))
    (hxj : Commute z (xOp Tag.D4 R ⟨0, by decide⟩ 1)) (hyj : Commute z (yOp Tag.D4 R ⟨0, by decide⟩ 1))
    (hxk : Commute z (xOp Tag.D4 R ⟨2, by decide⟩ 1)) (hyk : Commute z (yOp Tag.D4 R ⟨2, by decide⟩ 1))
    (c : R) :
    Commute z (xOp Tag.D4 R ⟨0, by decide⟩ c) ∧ Commute z (yOp Tag.D4 R ⟨0, by decide⟩ c) ∧
      Commute z (xOp Tag.D4 R ⟨2, by decide⟩ c) ∧ Commute z (yOp Tag.D4 R ⟨2, by decide⟩ c) :=
  commute_xOp_yOp_of_certCheck (RootOps.dataChecks Tag.D4) certCheck_D4 h2 z hxj hyj hxk hyk c

section Core

variable {τ : Tag} {L : Type} [Field L]

theorem core_two_negOne [CharP L 2] (hsl : ∀ i, τ.symmetrizer i i = 1)
    (hinj : PairInjectiveNegOne τ)
    {j k : Fin τ.rank} (hjk : iform (Pi.single j 1 : Fin τ.rank → ℤ) (Pi.single k 1) = -1)
    (hcert : ∀ z : Module.End L (RootModule τ L), Commute z (xOp τ L j 1) →
      Commute z (yOp τ L j 1) → Commute z (xOp τ L k 1) → Commute z (yOp τ L k 1) →
      ∀ c : L, Commute z (xOp τ L j c))
    (z : ModGL τ L) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hab : iform α β = -1)
    (h1 : z * pinnedX τ L α 1 = pinnedX τ L α 1 * z)
    (h2 : z * pinnedX τ L (-α) 1 = pinnedX τ L (-α) 1 * z)
    (h3 : z * pinnedX τ L β 1 = pinnedX τ L β 1 * z)
    (h4 : z * pinnedX τ L (-β) 1 = pinnedX τ L (-β) 1 * z) (c : L) :
    z * pinnedX τ L α c = pinnedX τ L α c * z := by
  have hj := isRoot_single τ j
  have hk := isRoot_single τ k
  have hne : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ Pi.single k 1 := fun e => by
    rw [e, iform_self_eq_two hsl hk] at hjk
    exact absurd hjk (by decide)
  have hne' : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ -Pi.single k 1 := fun e => by
    rw [e, SimplyLacedCover.iform_neg_left, iform_self_eq_two hsl hk] at hjk
    exact absurd hjk (by decide)
  have hne₂ : α ≠ β := fun e => by
    rw [e, iform_self_eq_two hsl hβ] at hab
    exact absurd hab (by decide)
  have hne₂' : α ≠ -β := fun e => by
    rw [e, SimplyLacedCover.iform_neg_left, iform_self_eq_two hsl hβ] at hab
    exact absurd hab (by decide)
  obtain ⟨w, hwj, hwk⟩ := exists_weyl_pair_negOne hinj hj hk hα hβ hne hne' hne₂ hne₂' hjk hab
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have hconj : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → ∀ c : L,
      n * pinnedX τ L γ c * n⁻¹ = pinnedX τ L (w • γ) c := fun hγ c =>
    canonicalRep_conj_pinnedX_two w hγ c
  have hback : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → ∀ c : L,
      pinnedX τ L γ c = n⁻¹ * pinnedX τ L (w • γ) c * n := fun hγ c => by
    rw [← hconj hγ c]; group
  have hcomm : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → ∀ {δ : Fin τ.rank → ℤ}, w • γ = δ →
      z * pinnedX τ L δ 1 = pinnedX τ L δ 1 * z →
      (n⁻¹ * z * n) * pinnedX τ L γ 1 = pinnedX τ L γ 1 * (n⁻¹ * z * n) := by
    intro γ hγ δ hδ h
    rw [hback hγ 1, hδ]
    exact commute_conj_aux n h
  have hnj : w • (-Pi.single j 1 : Fin τ.rank → ℤ) = -α := by rw [smul_neg, hwj]
  have hnk : w • (-Pi.single k 1 : Fin τ.rank → ℤ) = -β := by rw [smul_neg, hwk]
  have c1 := hcomm hj hwj h1
  have c2 := hcomm (IsRoot.neg hj) hnj h2
  have c3 := hcomm hk hwk h3
  have c4 := hcomm (IsRoot.neg hk) hnk h4
  rw [pinnedX_single] at c1 c3
  rw [pinnedX_neg_single] at c2 c4
  have e : ∀ (a b : ModGL τ L), a * b = b * a →
      Commute (a : Module.End L (RootModule τ L)) (b : Module.End L (RootModule τ L)) :=
    fun a b h => by
      have h' : (a : Module.End L (RootModule τ L)) * (b : Module.End L (RootModule τ L)) =
          (b : Module.End L (RootModule τ L)) * (a : Module.End L (RootModule τ L)) := by
        have := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L))) h
        simpa only [Units.val_mul] using this
      exact h'
  have hx := hcert ((n⁻¹ * z * n : ModGL τ L) : Module.End L (RootModule τ L))
    (e _ _ c1) (e _ _ c2) (e _ _ c3) (e _ _ c4) c
  have hx' : (n⁻¹ * z * n) * xUnit τ L j c = xUnit τ L j c * (n⁻¹ * z * n) := Units.ext hx.eq
  rw [← pinnedX_single, hback hj c, hwj] at hx'
  calc z * pinnedX τ L α c = n * ((n⁻¹ * z * n) * (n⁻¹ * pinnedX τ L α c * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * pinnedX τ L α c * n) * (n⁻¹ * z * n)) * n⁻¹ := by rw [hx']
    _ = pinnedX τ L α c * z := by group

end Core

section D4

variable {L : Type} [Field L]

theorem symmetrizer_diag_one_D4 : ∀ i, Tag.D4.symmetrizer i i = 1 := by
  intro i
  simp [Tag.symmetrizer]

theorem core_two_D4 [CharP L 2] (z : ModGL Tag.D4 L) {α β : Fin Tag.D4.rank → ℤ}
    (hα : IsRoot Tag.D4 α) (hβ : IsRoot Tag.D4 β) (hab : iform α β = -1)
    (h1 : z * pinnedX Tag.D4 L α 1 = pinnedX Tag.D4 L α 1 * z)
    (h2 : z * pinnedX Tag.D4 L (-α) 1 = pinnedX Tag.D4 L (-α) 1 * z)
    (h3 : z * pinnedX Tag.D4 L β 1 = pinnedX Tag.D4 L β 1 * z)
    (h4 : z * pinnedX Tag.D4 L (-β) 1 = pinnedX Tag.D4 L (-β) 1 * z) (c : L) :
    z * pinnedX Tag.D4 L α c = pinnedX Tag.D4 L α c * z := by
  have h2L : (2 : L) = 0 := CharTwo.two_eq_zero
  exact core_two_negOne symmetrizer_diag_one_D4 pairInjectiveNegOne_D4
    (j := ⟨0, by decide⟩) (k := ⟨2, by decide⟩) (by decide +kernel)
    (fun z a b c d e => (commute_xOp_yOp_D4 h2L z a b c d e).1) z hα hβ hab h1 h2 h3 h4 c

end D4

theorem d4TwoPoly_holds : D4TwoPoly := by
  intro L _ _ Ψ hΨ hneg hadj zu z hnorm hz g
  have hz' : ∀ γ ∈ Ψ, (zu⁻¹ * z * zu) * pinnedX Tag.D4 L γ 1 =
      pinnedX Tag.D4 L γ 1 * (zu⁻¹ * z * zu) := by
    intro γ hγ
    have := commute_conj_aux zu (hz γ hγ)
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one]
      using this
  have key : ∀ g ∈ rootSpan Tag.D4 L Ψ, Commute z g := by
    refine commute_rootSpan_of_conj_gens hnorm fun γ hγ c => ?_
    obtain ⟨δ, hδ, hγδ⟩ := hadj γ hγ
    have hδr := hΨ δ hδ
    have hγr := hΨ γ hγ
    have hab : iform γ (-δ) = -1 := by
      rw [SimplyLacedCover.iform_neg_right, hγδ]
    have key := core_two_D4 (zu⁻¹ * z * zu) hγr (IsRoot.neg hδr) hab (hz' γ hγ)
      (hz' _ (hneg γ hγ)) (hz' _ (hneg δ hδ)) (by simpa only [neg_neg] using hz' δ hδ) c
    calc z * (zu * pinnedX Tag.D4 L γ c * zu⁻¹)
        = zu * ((zu⁻¹ * z * zu) * pinnedX Tag.D4 L γ c) * zu⁻¹ := by group
      _ = zu * (pinnedX Tag.D4 L γ c * (zu⁻¹ * z * zu)) * zu⁻¹ := by rw [key]
      _ = (zu * pinnedX Tag.D4 L γ c * zu⁻¹) * z := by group
  exact key g

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
