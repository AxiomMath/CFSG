module

public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts
public import CFSG.ClassicalInvolution.Q3.Q3T8M11

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

theorem sq_eq_of_cyclic_four {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    {z : X} (hd : TightDatum R S z) {U : Subgroup X} (hUR : U ≤ R) {s : U}
    (hs : orderOf (s : X) = 4) : (s : X) ^ 2 = z := by
  refine hd.eq_of_orderOf_eq_two (R.pow_mem (hUR s.2) 2) ?_
  have h := orderOf_pow_of_dvd (x := (s : X)) (n := 2) (by norm_num) (by rw [hs]; norm_num)
  rw [h, hs]

theorem orderOf_gen_eq_four {X : Type} [Group X] {U : Subgroup X} {s : U}
    (hs : ∀ x : U, x ∈ Subgroup.zpowers s) (hU4 : Nat.card U = 4) : orderOf (s : X) = 4 := by
  rw [Subgroup.orderOf_coe, ← hU4, orderOf_eq_card_of_forall_mem_zpowers hs]

theorem model164M11_proved : Model164M11 := by
  intro X _ _ R S z hm _ hX U hUR hUc hU4 β γ hγU hβ hβ2
  obtain ⟨e⟩ := hX
  obtain ⟨s, hs⟩ := hUc.exists_generator
  have hs4 : orderOf (s : X) = 4 := orderOf_gen_eq_four hs hU4
  have hsz : (s : X) ^ 2 = z := sq_eq_of_cyclic_four hm.datum hUR hs4
  have hγ4 : γ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, ← hβ, hβ2]
  let ψ : ↥NativeSporadic.M11 →* X := (e.symm : NativeSporadic.Carrier .M11 ≃* X).toMonoidHom
  have hψ : ∀ x, ψ (e x) = x := fun x => e.symm_apply_apply x
  have hsurj : Function.Surjective ψ := fun x => ⟨e x, hψ x⟩
  have hs' : orderOf (ψ (e s)) = 4 := by rw [hψ]; exact hs4
  have hγs : γ (ψ (e s)) = ψ (e s) := by rw [hψ]; exact hγU s s.2
  rcases Q3T8.m11_dich ψ hsurj hs' γ hγs hγ4 with h | h
  · left
    rw [hβ, ← sq, h]
  · right
    rw [hβ, ← sq, h, hψ, hsz]

end CFSG.ClassicalInvolution.Q3.TL4.MF164
