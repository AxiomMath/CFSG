module

public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.IrreducibleQuadratic
public import CFSG.LieType.Steinberg.Exceptional.Universal
public import CFSG.LieType.Universal.Unitary.Extras

public section

namespace CFSG.LieType.Universal

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Exceptional

structure LieUniversal : Type 1 where
  K : Type
  [instGroup : Group K]
  D : UniversalRootDatum K

attribute [instance] LieUniversal.instGroup

@[expose] def bnRank : StatedLieTag → ℕ → ℕ
  | .PSL, n => n - 1
  | .PSU, n => n / 2
  | .PSp, n => n
  | .POmegaOdd, n => n
  | .POmegaPlus, n => n
  | .POmegaMinus, n => n - 1
  | .F4, _ => 4
  | .twistedE6, _ => 4
  | .E6, _ => 6
  | .E7, _ => 7
  | .E8, _ => 8
  | .G2, _ => 2
  | .trialityD4, _ => 2
  | .twistedF4, _ => 2
  | .Tits, _ => 2
  | .twistedB2, _ => 1
  | .twistedG2, _ => 1

@[expose] noncomputable def trivialUniversal : LieUniversal :=
  ⟨Matrix.SpecialLinearGroup (Fin 1) (ZMod 2), SpecialLinear.rootDatum 0 (ZMod 2)⟩

theorem card_galoisField_two_mul (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
  rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]

@[expose] noncomputable def minusCoeffs (p f : ℕ) [Fact p.Prime] :
    GaloisField p f × GaloisField p f :=
  ((exists_irreducible_quadratic (GaloisField p f)).choose,
    (exists_irreducible_quadratic (GaloisField p f)).choose_spec.choose)

theorem minusCoeffs_irr (p f : ℕ) [Fact p.Prime] :
    ∀ s : GaloisField p f, s ^ 2 + (minusCoeffs p f).1 * s + (minusCoeffs p f).2 ≠ 0 :=
  (exists_irreducible_quadratic (GaloisField p f)).choose_spec.choose_spec

@[expose] noncomputable def lieUniversal (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) :
    LieUniversal :=
  haveI : Fact p.Prime := ⟨hp⟩
  match t, n with
  | .PSL, m + 1 =>
    ⟨Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField p f),
      SpecialLinear.rootDatum m (GaloisField p f)⟩
  | .PSU, n =>
    if hf : 1 ≤ f then ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * f)) p f) n,
      Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ else trivialUniversal
  | .PSp, n => ⟨StatedSp n (GaloisField p f), Symplectic.rootDatum n (GaloisField p f)⟩
  | .POmegaOdd, n => ⟨spinGroup (Spin.quadOdd n (GaloisField p f)),
      Spin.oddDatum n (GaloisField p f)⟩
  | .POmegaMinus, n =>
    ⟨spinGroup (Spin.quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2),
      Spin.Twisted.minusDatum n (minusCoeffs_irr p f)⟩
  | .POmegaPlus, n =>
    if hn : 3 ≤ n then ⟨spinGroup (Spin.quadPlus n (GaloisField p f)),
      Spin.plusDatum n (GaloisField p f) hn⟩ else trivialUniversal
  | .F4, _ => ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField p f)),
      CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField p f)⟩
  | .E8, _ => ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField p f)),
      CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField p f)⟩
  | .E6, _ => ⟨e6UniversalGroup p f, e6UniversalDatum p f⟩
  | .E7, _ => ⟨e7UniversalGroup p f, e7UniversalDatum p f⟩
  | .twistedE6, _ => ⟨twistedE6Group p f, twistedE6Datum p f⟩
  | _, _ => trivialUniversal

end CFSG.LieType.Universal
