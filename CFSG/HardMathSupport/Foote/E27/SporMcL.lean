module

public import CFSG.HardMathSupport.Foote.E27.SporSylowBound
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import CFSG.Sporadic.Recognition.McLASThreeLocalCert

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup CFSG.Sporadic.Recognition.McLAS

section Certificates


theorem mcl_dvd81_card_sylow_inf_centralizer {K : Type*} [Group K]
    (e : K ≃* CFSG.Blueprint.NativeSporadic.McL) (S₀ : Sylow 3 K) {z : K}
    (hz : z ∈ (S₀ : Subgroup K)) (hz3 : orderOf z = 3) :
    81 ∣ Nat.card ↥((S₀ : Subgroup K) ⊓ centralizer ({z} : Set K)) := by
  obtain ⟨x, R, T, A, hL⟩ := mcl_threeLocal_of_certificate
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11 :=
    card_mcl_eq
  have hfac : (Nat.card CFSG.Blueprint.NativeSporadic.McL).factorization 3 = 6 := by
    have h : 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11 = 3 ^ 6 * (2 ^ 7 * 5 ^ 3 * 7 * 11) := by ring
    rw [hcard, h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hfin : Finite CFSG.Blueprint.NativeSporadic.McL :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine @dvd81_card_sylow_inf_centralizer_of_equiv K CFSG.Blueprint.NativeSporadic.McL _
    inferInstance hfin e T ?_ ?_ S₀ z hz hz3
  · rw [hfac, hL.card_T]; norm_num
  · intro s hs hs3
    have := hL.A_elementaryAbelian.toIsMulCommutative
    exact @dvd81_card_inf_centralizer_of_threeLocal CFSG.Blueprint.NativeSporadic.McL inferInstance
      hfin T R A x hL.order_x hL.R_le_T hL.A_le_T hL.card_R hL.commutator_R hL.center_R hL.card_A
      this hL.order_three s hs hs3

theorem E27Config.false_of_mcl {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.McL) :
    False := by
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  exact h.false_of_sylow_kill hz S₀ fun s hs hs3 =>
    Or.inl (mcl_dvd81_card_sylow_inf_centralizer e S₀ hs hs3)

theorem E27Config.false_of_sporadic_mcl {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .McL ≃*
      (TauCeti.CFSGIndex.sporadic .McL).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) : False :=
  h.false_of_mcl hz (e.trans hbr.some.symm)

end Certificates

end CFSG.HardMathSupport.Foote.E27
