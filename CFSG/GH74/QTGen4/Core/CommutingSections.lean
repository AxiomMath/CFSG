module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.GH74.QTGen4

theorem sq_dvd_card_of_commute {X : Type*} [Group X] [Finite X] {A B : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hZ : Subgroup.center A = ⊥) {p : ℕ} (hp : p.Prime)
    (hA : p ∣ Nat.card A) (hB : p ∣ Nat.card B) : p ^ 2 ∣ Nat.card X := by
  have hinf : ∀ x : X, x ∈ A → x ∈ B → x = 1 := by
    intro x hxA hxB
    have hc : (⟨x, hxA⟩ : A) ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hAB g g.2 x hxB
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  let f : A × B →* X :=
    { toFun := fun x => (x.1 : X) * (x.2 : X)
      map_one' := by simp
      map_mul' := by
        intro x y
        have h := hAB (y.1 : X) y.1.2 (x.2 : X) x.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (x.1 : X) * (y.1 : X) * ((x.2 : X) * (y.2 : X))
            = (x.1 : X) * ((y.1 : X) * (x.2 : X)) * (y.2 : X) := by simp only [mul_assoc]
          _ = (x.1 : X) * ((x.2 : X) * (y.1 : X)) * (y.2 : X) := by rw [h]
          _ = (x.1 : X) * (x.2 : X) * ((y.1 : X) * (y.2 : X)) := by simp only [mul_assoc] }
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    have h' : (a : X) * (b : X) = 1 := h
    have haB : (a : X) ∈ B := by
      have : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left h'
      rw [this]
      exact B.inv_mem b.2
    have ha1 : (a : X) = 1 := hinf _ a.2 haB
    have hb1 : (b : X) = 1 := by
      rw [ha1, one_mul] at h'
      exact h'
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hdvd : Nat.card (A × B) ∣ Nat.card X := by
    rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_prod] at hdvd
  rw [pow_two]
  exact (mul_dvd_mul hA hB).trans hdvd

end CFSG.GH74.QTGen4
