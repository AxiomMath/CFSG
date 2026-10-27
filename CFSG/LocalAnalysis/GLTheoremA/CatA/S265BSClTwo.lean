module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Quad

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux
  (card_two_charP card_two_cases)

theorem exists_fixed_ne_zero_of_card_two {F V H : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite V] [Group H] (hF : Nat.card F = 2) (hH : IsPGroup 2 H) (φ : H →* (V ≃ₗ[F] V))
    {U : Submodule F V} (hU : ∀ x u, u ∈ U → φ x u ∈ U) (hne : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ x, φ x u = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction H U :=
    { smul := fun x u => ⟨φ x u, hU x u u.2⟩
      one_smul := fun u => Subtype.ext (by show φ 1 u = u; simp)
      mul_smul := fun x y u => Subtype.ext (by show φ (x * y) u = φ x (φ y u); rw [map_mul]; rfl) }
  have hsmul : ∀ (x : H) (u : U), ((x • u : U) : V) = φ x u := fun _ _ => rfl
  have h0 : (0 : U) ∈ MulAction.fixedPoints H U := fun x =>
    Subtype.ext (by rw [hsmul]; simp)
  have : Module.Finite F U := Module.Finite.of_finite
  have hdvd : 2 ∣ Nat.card U := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF]
    have : Module.finrank F U ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.mp h)
    exact dvd_pow_self 2 this
  obtain ⟨b, hb, hb0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdvd h0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun x => ?_⟩
  have := congrArg Subtype.val (hb x)
  rwa [hsmul] at this

theorem eq_zero_or_eq_or_eq_add_of_finrank_two {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (hF : Nat.card F = 2) {M : Submodule F V} (hM : Module.finrank F M = 2)
    {w w' : V} (hw : w ∈ M) (hw' : w' ∈ M) (hw0 : w ≠ 0) (hw'0 : w' ≠ 0) (hne : w ≠ w')
    {v : V} (hv : v ∈ M) : v = 0 ∨ v = w ∨ v = w' ∨ v = w + w' := by
  have h2 : (2 : F) = 0 := by
    haveI := card_two_charP hF
    exact CharP.cast_eq_zero F 2
  have hww : w + w = 0 := by rw [← two_smul F w, h2, zero_smul]
  have hli : LinearIndependent F ![w, w'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases card_two_cases hF s with rfl | rfl <;> rcases card_two_cases hF t with rfl | rfl
    · simp
    · simp at hst; exact absurd hst hw'0
    · simp at hst; exact absurd hst hw0
    · simp only [one_smul] at hst
      exact absurd (add_left_cancel (hst.trans hww.symm)) hne.symm
  haveI : Module.Finite F M := Module.finite_of_finrank_pos (by omega)
  have hrange : Set.range ![w, w'] = {w, w'} := by
    simp [Matrix.range_cons]
    exact Set.pair_comm _ _
  have hspan : Submodule.span F {w, w'} = M := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      exacts [hw, hw']
    · have h := finrank_span_eq_card hli
      rw [hrange] at h
      rw [h, hM]
      rfl
  rw [← hspan, Submodule.mem_span_pair] at hv
  obtain ⟨a, b, rfl⟩ := hv
  rcases card_two_cases hF a with rfl | rfl <;> rcases card_two_cases hF b with rfl | rfl <;>
    simp

theorem cast_three_ne_zero_of_card_two {F : Type*} [Field F] (hF : Nat.card F = 2) :
    ((3 : ℕ) : F) ≠ 0 := by
  haveI := card_two_charP hF
  intro h
  have h2 : 2 ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
