module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
import CFSG.CGT.PushingUpLit.SolKNA.QuatLieOrbit
import CFSG.GH74.KGroups.U33Tables
public import CFSG.GH74.KGroups.U33TablesInputs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.GH74.KGroups.U33 (QP t0 equiv_of_lieModel inv_ok QP_ok)

theorem card_moved_t0 : Nat.card {ω : Fin 28 // t0 ω ≠ ω} = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_moved_conj {Ω : Type*} [Finite Ω] (c t : Equiv.Perm Ω) :
    Nat.card {ω : Ω // (c * t * c⁻¹) ω ≠ ω} = Nat.card {ω : Ω // t ω ≠ ω} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (c⁻¹ : Equiv.Perm Ω) fun ω => ?_)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  constructor
  · intro h h'
    apply h
    rw [h']
    simp
  · intro h h'
    apply h
    have := congrArg (c⁻¹ : Equiv.Perm Ω) h'
    simpa using this

theorem posModel_U3 :
    PosModel .PSU 3 := by
  intro X _ _ h Q hQ
  obtain ⟨e⟩ := equiv_of_lieModel h
  let ψ : X →* Equiv.Perm (Fin 28) := QP.originalSubgroup.subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  refine no_big_quaternion_of_moved ψ hψ 24 (by norm_num) (fun g hg => ?_) hQ
  have hg2 : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    omega
  have h2 : (ψ g) ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
  have h1 : ψ g ≠ 1 := fun h => hg1 (hψ (by rw [h, map_one]))
  obtain ⟨c, -, hc⟩ := CFSG.GH74.KGroups.invConjCheck_sound QP QP_ok inv_ok (ψ g) (e g).2 h2 h1
  rw [← hc, card_moved_conj, card_moved_t0]

end CFSG.CGT.PushingUpLit.SolKNA
