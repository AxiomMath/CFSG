module

public import CFSG.LieType.Steinberg.CentralExt.GriessTable
public import CFSG.Monster.Existence.TwoPoint.StdE6Model
public import Certificates.Data.ExceptionalSL3

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two

@[expose] def TwistedE6TwoMultiplier : Prop :=
  ∀ (Y : Type) [Group Y], CFSG.Blueprint.LieModel Y .twistedE6 0 2 1 →
    commutator Y = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier Y ≃* Multiplicative (ZMod 3 × ZMod 2 × ZMod 2))

variable {X : Type} [Group X]

theorem row_of_multiplier
    (h : commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* Multiplicative (ZMod 3 × ZMod 2 × ZMod 2))) :
    GriessAll.GriessRow X .twistedE6 0 2 1 := by
  obtain ⟨hX, ⟨e⟩⟩ := h
  exact ⟨hX, ⟨e.trans (((MulEquiv.prodMultiplicative _ _).trans
    (MulEquiv.prodCongr MulEquiv.prodUnique.symm (MulEquiv.prodMultiplicative _ _))).trans
    (GriessClassical.toGenEx (t := .twistedE6) (n := 0) (p := 2) (f := 1) (a₁ := 3) (a₂ := 1)
      (b₁ := 2) (b₂ := 2) rfl rfl))⟩⟩

theorem lieModel_of_tauCeti (hmodel : CFSG.Models.LieModel X .twistedE6 0 2 1) :
    CFSG.Blueprint.LieModel X .twistedE6 0 2 1 := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | twistedE6 q =>
      have hp : q.p = 2 := by have := hd.1; omega
      have hf : q.exponent = 1 := by have := hd.2; omega
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      set K := GaloisField q.p (2 * q.exponent)
      have hK2 : Nat.card K = q.card ^ 2 := by
        rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
          ← pow_mul, mul_comm]
      have hq : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hp, hf, pow_one]
      have hK : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.E6.order := hK2
      let σ : K →+* K := iterateFrobenius K q.p q.exponent
      have hσ : ∀ x, σ x = x ^ q.card := fun x => by
        rw [TauCeti.PrimePower.card_def]
        exact iterateFrobenius_def q.p q.exponent x
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).twistedE6 q hv K hK σ hσ
      exact CFSG.Monster.Existence.lieModel_twistedE6_of_mulEquiv K (by rw [hK, hq, pow_one]) σ
        (fun c => by rw [hσ c, hq, pow_one]) ⟨e.trans b.symm⟩
    | _ => simp [CFSG.Models.NamesTag] at hd


section Table

theorem griess_all_models_of_twistedE6_two (h : TwistedE6TwoMultiplier) (t : StatedLieTag)
    (n p f : ℕ) (hmodel : CFSG.Models.LieModel X t n p f) : GriessAll.GriessRow X t n p f :=
  GriessTable.griess_all_models_of_one
    (fun Y _ hY => row_of_multiplier (h Y (lieModel_of_tauCeti hY))) t n p f hmodel

theorem griess_native_models_of_twistedE6_two (h : TwistedE6TwoMultiplier) (t : StatedLieTag)
    (n p f : ℕ) (hmodel : CFSG.Blueprint.LieModel X t n p f) : GriessAll.GriessRow X t n p f :=
  GriessTable.griess_native_models_of_one (fun Y _ hY => row_of_multiplier (h Y hY)) t n p f
    hmodel

end Table

end CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two
