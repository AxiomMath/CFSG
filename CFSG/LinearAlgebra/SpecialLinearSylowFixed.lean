module

public import CFSG.LinearAlgebra.RootGroupSL.SLTransitive
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LinearAlgebra

theorem eq_zero_of_forall_apply_eq_of_odd_index
    {E W : Type} [Field E] [Fintype E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hm : 2 ≤ Module.finrank E W) (hch : ringChar E ≠ 2)
    (T : Subgroup (SpecialLinearGroup E W)) (hodd : Odd T.index)
    {v : W} (hv : ∀ t ∈ T, (t : W ≃ₗ[E] W) v = v) : v = 0 := by
  by_contra h0
  let b : Module.Basis (Fin (Module.finrank E W)) E W := Module.finBasis E W
  haveI : Fintype W := Module.fintypeOfFintype b
  haveI : Fintype {w : W // w ≠ 0} := Fintype.ofFinite _
  haveI : Fintype {w : W // w = 0} := Fintype.ofFinite _
  letI : MulAction (SpecialLinearGroup E W) {w : W // w ≠ 0} :=
    { smul := fun g w => ⟨g.1 w.1, by
        intro h
        apply w.2
        have := congrArg (fun x => g.1.symm x) h
        simpa using this⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun g h w => Subtype.ext (LinearEquiv.mul_apply g.1 h.1 w.1) }
  haveI : MulAction.IsPretransitive (SpecialLinearGroup E W) {w : W // w ≠ 0} :=
    ⟨fun a b => by
      obtain ⟨g, hg⟩ := CFSG.LinearAlgebra.RootGroupSL.exists_specialLinear_apply_eq hm a.2 b.2
      exact ⟨g, Subtype.ext hg⟩⟩
  have hstab : (MulAction.stabilizer (SpecialLinearGroup E W)
      (⟨v, h0⟩ : {w : W // w ≠ 0})).index = Fintype.card {w : W // w ≠ 0} := by
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card]
  have hcardE : Odd (Fintype.card E) := by
    rw [Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hch
  have hcardW : Odd (Fintype.card W) := by
    rw [Module.card_eq_pow_finrank (K := E) (V := W)]
    exact hcardE.pow
  have hcard_sub : Fintype.card {w : W // w ≠ 0} = Fintype.card W - 1 := by
    rw [Fintype.card_subtype_compl (fun w : W => w = 0), Fintype.card_subtype_eq (0 : W)]
  have heven : 2 ∣ (MulAction.stabilizer (SpecialLinearGroup E W)
      (⟨v, h0⟩ : {w : W // w ≠ 0})).index := by
    rw [hstab, hcard_sub]
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd (m := Fintype.card W) (n := 1) hcardW odd_one)
  have hle : T ≤ MulAction.stabilizer (SpecialLinearGroup E W)
      (⟨v, h0⟩ : {w : W // w ≠ 0}) := by
    intro t ht
    rw [MulAction.mem_stabilizer_iff]
    exact Subtype.ext (hv t ht)
  have hdvd := Subgroup.index_dvd_of_le hle
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_trans heven hdvd))

end CFSG.LinearAlgebra

end
