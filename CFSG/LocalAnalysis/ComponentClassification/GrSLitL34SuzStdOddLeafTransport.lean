module

public import CFSG.Sporadic.SuzOddCore.SmallAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore

private theorem exists_mulEquiv_codRestrict {S : Type*} [Group S]
    {Ψ : S →* Equiv.Perm (Fin 1782)} (hinj : Function.Injective Ψ)
    (hΨM : ∀ x, Ψ x ∈ suzM) (hΨR : ∀ y ∈ suzM, ∃ x, Ψ x = y) :
    ∃ e : S ≃* suzM, ∀ x, e x = ⟨Ψ x, hΨM x⟩ := by
  have hsurj : Function.Surjective (Ψ.codRestrict suzM hΨM) := by
    intro y
    obtain ⟨x, hx⟩ := hΨR y.1 y.2
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨MulEquiv.ofBijective (Ψ.codRestrict suzM hΨM)
    ⟨fun a b h => hinj (congrArg Subtype.val h), hsurj⟩, fun x => rfl⟩

theorem exists_mem_suzT_mul_mul_inv_eq
    {S : Type*} [Group S] {Ψ : S →* Equiv.Perm (Fin 1782)} (hinj : Function.Injective Ψ)
    (hΨM : ∀ x, Ψ x ∈ suzM) (hΨR : ∀ y ∈ suzM, ∃ x, Ψ x = y) (β : MulAut S) :
    ∃ τ ∈ suzT, ∀ x : S, τ * Ψ x * τ⁻¹ = Ψ (β x) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_codRestrict hinj hΨM hΨR
  obtain ⟨τ, hτ⟩ := suzConjT_bijective.surjective (e.symm.trans (β.trans e))
  refine ⟨τ.1, τ.2, fun x => ?_⟩
  have h : suzConjT τ (e x) = e (β x) := by
    rw [hτ]
    simp
  have h2 := congrArg (fun m : suzM => (m : Equiv.Perm (Fin 1782))) h
  simpa [suzConjT_apply, he] using h2

theorem card_centralizer_eq_card_suzM_inf_centralizer {S : Type*} [Group S]
    {Ψ : S →* Equiv.Perm (Fin 1782)} (hinj : Function.Injective Ψ) (hΨM : ∀ x, Ψ x ∈ suzM)
    (hΨR : ∀ y ∈ suzM, ∃ x, Ψ x = y) (x : S) :
    Nat.card ↥(centralizer ({x} : Set S)) =
      Nat.card ↥(suzM ⊓ centralizer ({Ψ x} : Set (Equiv.Perm (Fin 1782)))) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_codRestrict hinj hΨM hΨR
  have h1 := CFSG.EvenSporadicStandard.Solomon78.card_centralizer_eq_of_mulEquiv e x
  have h2 := CFSG.EvenSporadicStandard.Solomon78.card_inf_centralizer_eq suzM (hΨM x)
  rw [h1, h2, he]

end CFSG.ComponentClassification.GrSLit.L34Sec5S
