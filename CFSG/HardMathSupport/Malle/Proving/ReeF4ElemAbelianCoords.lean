module

public import CFSG.HardMathSupport.Malle.Proving.ReeF4LinesGL2F5
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Malle.Proving

open CFSG.Open

variable {Y : Type} [Group Y]

open scoped IsMulCommutative in
theorem exists_coord_of_isElemAbelian {A : Subgroup Y} (hE : IsElemAbelian 5 A)
    (hc : Nat.card A = 5 ^ 2) : ∃ φ : A ≃ Vec5, ∀ a b : A, φ (a * b) = φ a + φ b := by
  obtain ⟨hcomm, hexp⟩ := hE
  have : IsMulCommutative A := hcomm
  have h5 : ∀ x : Additive A, (5 : ℕ) • x = 0 := by
    intro x
    have h1 : x.toMul ^ 5 = 1 := Subtype.ext (by simpa using hexp (x.toMul : Y) x.toMul.2)
    change Additive.ofMul (x.toMul ^ 5) = Additive.ofMul 1
    rw [h1]
  let _ : Module (ZMod 5) (Additive A) := AddCommGroup.zmodModule h5
  let e : A ≃ Additive A := ⟨Additive.ofMul, Additive.toMul, fun _ => rfl, fun _ => rfl⟩
  have hfin : Nat.card (Additive A) = 5 ^ 2 := (Nat.card_congr e).symm.trans hc
  have : Finite (Additive A) := Nat.finite_of_card_ne_zero (by rw [hfin]; norm_num)
  have : Module.Finite (ZMod 5) (Additive A) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 5) (Additive A) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 5) (V := Additive A)
    rw [hfin, Nat.card_zmod] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) h.symm
  let b : Module.Basis (Fin 2) (ZMod 5) (Additive A) :=
    Module.finBasisOfFinrankEq (ZMod 5) (Additive A) hrank
  refine ⟨e.trans b.equivFun.toEquiv, fun a c => ?_⟩
  show b.equivFun (Additive.ofMul (a * c)) =
    b.equivFun (Additive.ofMul a) + b.equivFun (Additive.ofMul c)
  rw [← map_add]
  rfl

end CFSG.HardMathSupport.Malle.Proving
