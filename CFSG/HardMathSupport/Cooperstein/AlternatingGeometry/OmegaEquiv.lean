module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.MatchingEquiv
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightOfData

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem exists_omegaEquiv {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : Ω → Prop) [DecidablePred P]
    (σ : Ω → Ω) (hσP : ∀ x, P x → P (σ x)) (hσ1 : ∀ x, P x → σ x ≠ x)
    (hσ2 : ∀ x, P x → σ (σ x) = x) :
    ∃ (r s : ℕ) (e : Ω ≃ OmegaE r s),
      (∀ x, P x ↔ ∃ p, e x = Sum.inl p) ∧
      ∀ x, P x → ∃ i b, e x = Sum.inl (i, b) ∧ e (σ x) = Sum.inl (i, !b) := by
  classical
  let σP : {a // P a} → {a // P a} := fun x => ⟨σ x.1, hσP x.1 x.2⟩
  have h1 : ∀ x, σP x ≠ x := fun x h => hσ1 x.1 x.2 (congrArg Subtype.val h)
  have h2 : ∀ x, σP (σP x) = x := fun x => Subtype.ext (hσ2 x.1 x.2)
  obtain ⟨ι, _, _, e1, hcard, he1⟩ := exists_blockEquiv σP h1 h2
  let r := Fintype.card ι
  let eι : ι ≃ Fin r := Fintype.equivFin ι
  let e1' : {a // P a} ≃ Fin r × Bool := e1.trans (Equiv.prodCongr eι (Equiv.refl Bool))
  let s := Fintype.card {a // ¬ P a}
  let e2 : {a // ¬ P a} ≃ Fin s := Fintype.equivFin _
  let e : Ω ≃ OmegaE r s := (Equiv.sumCompl P).symm.trans (Equiv.sumCongr e1' e2)
  refine ⟨r, s, e, fun x => ?_, fun x hx => ?_⟩
  · by_cases hx : P x
    · simp [e, Equiv.sumCompl, hx]
    · simp [e, Equiv.sumCompl, hx]
  · refine ⟨(e1' ⟨x, hx⟩).1, (e1' ⟨x, hx⟩).2, ?_, ?_⟩
    · simp [e, hx]
    · have := he1 ⟨x, hx⟩
      simp [e, hσP x hx, e1', σP] at this ⊢
      rw [this]; rfl

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
