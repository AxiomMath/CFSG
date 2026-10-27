module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Assembly.OrderReductions.FrattiniElementary
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

open scoped IsMulCommutative

namespace CFSG.GroupTheory

open CFSG.OrderReductions.FrattiniAutomorphisms

theorem frattini_elementary_quotient {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) :
    (frattini P).Characteristic ∧ IsMulCommutative (P ⧸ frattini P) ∧
      (∀ x : P ⧸ frattini P, x ^ p = 1) ∧ IsElementaryAbelian p (P ⧸ frattini P) ∧
      ∃ d : ℕ, Nat.card (P ⧸ frattini P) = p ^ d ∧
        Nonempty (Additive (P ⧸ frattini P) ≃+ (Fin d → ZMod p)) := by
  have hcomm : IsMulCommutative (P ⧸ frattini P) :=
    CFSG.OrderReductions.FrattiniElementary.frattini_quotient_isMulCommutative p hP
  have hpow : ∀ x : P ⧸ frattini P, x ^ p = 1 :=
    CFSG.OrderReductions.FrattiniElementary.frattini_quotient_exponent p hP
  have helem : IsElementaryAbelian p (P ⧸ frattini P) :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }
  refine ⟨inferInstance, hcomm, hpow, helem, ?_⟩
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  have : FiniteDimensional (ZMod p) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) (Additive (P ⧸ frattini P))
  refine ⟨Module.finrank (ZMod p) (Additive (P ⧸ frattini P)), ?_, ⟨b.equivFun.toAddEquiv⟩⟩
  rw [show Nat.card (P ⧸ frattini P) = Nat.card (Additive (P ⧸ frattini P)) from rfl,
    Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem frattini_automorphism_kernel {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) :
    (∀ (σ : MulAut P) (x : P), quotientAutomorphism (frattini P) σ (x : P ⧸ frattini P) =
      (σ x : P ⧸ frattini P)) ∧ IsPGroup p (quotientAutomorphism (frattini P)).ker :=
  ⟨fun σ x => quotientEquivalence_apply (frattini P) σ x,
    frattini_automorphism_kernel_isPGroup p hP⟩

end CFSG.GroupTheory
