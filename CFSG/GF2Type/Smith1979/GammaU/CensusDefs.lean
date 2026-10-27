
module

public import CFSG.GF2Type.Smith1979.GammaU.StepA2Base
public import CFSG.GF2Type.Smith1979.GammaU.StepCInputs
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairBase

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

@[expose] def thetaU : V12 ≃ₗ[ZMod 2] V12 :=
  LinearEquiv.ofLinear theta0 (theta0.comp theta0) (LinearMap.ext theta0_theta0_theta0)
    (LinearMap.ext theta0_theta0_theta0)

@[simp] theorem thetaU_apply (x : V12) : thetaU x = theta0 x := rfl

structure NLMem (i : ℕ) (h : V12 ≃ₗ[ZMod 2] V12) : Prop where
  mem : h ∈ gammaU
  fix : h (vecOf a0) = vecOf a0
  d0 : ∀ y, h y ∈ spanOf d0 ↔ y ∈ spanOf d0
  norm : ∀ l, RowsSet (compOf i) (h * l * h⁻¹) ↔ RowsSet (compOf i) l

@[expose] def candGrp (i : ℕ) (Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)) :
    Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  Subgroup.closure ({l | RowsSet (compOf i) l} ∪ ↑Le ∪ {thetaU})

@[expose] def ResGrp (i : ℕ) (N : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : Prop :=
  ∃ c ∈ ResPair.resConj i, ∃ (h1 : mulR c (Viol.invR c) = idR)
    (h2 : mulR (Viol.invR c) c = idR),
    N = (ResPair.n2 i).map (MulAut.conj (Viol.eqvOf c (Viol.invR c) h1 h2)).toMonoidHom

@[expose] def FrameTr (T : ℕ → V12 ≃ₗ[ZMod 2] V12) (m : ℕ) : Prop :=
  (∀ j < m, T j ∈ gammaU ∧ T j (vecOf a0) = vecOf a0) ∧
    (∃ j < m, (spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12) = spanOf d0) ∧
    ∀ r ∈ saGens, ∀ j < m, ∃ j' < m,
      ((spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12)).map (linOfRows r) =
        (spanOf d0).map (T j' : V12 →ₗ[ZMod 2] V12)

@[expose] def ColTr (te : ℕ → V12 ≃ₗ[ZMod 2] V12) (r0 : Array ℕ) : Prop :=
  ∀ n ∈ colPts r0, te n ∈ gammaU ∧ te n (vecOf a0) = vecOf n

@[expose] def CensusBase (i : ℕ) (r0 : Array ℕ) (T : ℕ → V12 ≃ₗ[ZMod 2] V12) (m : ℕ)
    (te : ℕ → V12 ≃ₗ[ZMod 2] V12) : Prop :=
  r0 ∈ unitaryElts i ∧ FrameTr T m ∧ ColTr te r0

@[expose] def CfgAll (i : ℕ) (r0 : Array ℕ) (T : ℕ → V12 ≃ₗ[ZMod 2] V12) (m : ℕ)
    (te : ℕ → V12 ≃ₗ[ZMod 2] V12) (P : Subgroup (V12 ≃ₗ[ZMod 2] V12) → Prop) : Prop :=
  ∀ n ∈ colPts r0, ∀ j < m, ∀ c < 32, ∀ Le : Subgroup (V12 ≃ₗ[ZMod 2] V12),
    (∀ l, l ∈ Le ↔ ∃ r ∈ compOf c, ∀ x, ((te n * T j)⁻¹ * l * (te n * T j)) x = linOfRows r x) →
    vecOf a0 ∈ (spanOf d0).map ((te n * T j : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) →
    (∃ l ∈ Le, ∀ y, l y = linOfRows r0 y) →
    Nat.card (candGrp i Le) = 1152 → P (candGrp i Le)

@[expose] def RowsConj (h : V12 ≃ₗ[ZMod 2] V12) (r r0 : Array ℕ) : Prop :=
  ∀ y, linOfRows r0 y = h⁻¹ (linOfRows r (h y))

@[expose] def CompFacts : Prop :=
  ∀ c < 32, ∀ g ∈ ResPair.compGens c, ∃ U ∈ gammaU, ∀ y, U y = linOfRows g y

@[expose] def PairFacts (i : ℕ) : Prop :=
  ∃ r0 T m te, CensusBase i r0 T m te ∧ ∀ r₁ ∈ unitaryElts i, ∀ r₂ ∈ unitaryElts i, r₁ ≠ r₂ →
    ∃ U h₁ h₂ : V12 ≃ₗ[ZMod 2] V12, NLMem i U ∧
      (∀ N, ResGrp i N → ResGrp i (N.map (MulAut.conj U).toMonoidHom)) ∧
      NLMem i h₁ ∧ NLMem i h₂ ∧ RowsConj (U * h₁) r₁ r0 ∧ RowsConj (U * h₂) r₂ r0 ∧
      CfgAll i r0 T m te fun R₁ => CfgAll i r0 T m te fun R₂ =>
        Viol.Violation (R₁.map (MulAut.conj h₁).toMonoidHom ⊔ R₂.map (MulAut.conj h₂).toMonoidHom)
          (compOf i) (compOf i) ∨
        ResGrp i (R₁.map (MulAut.conj h₁).toMonoidHom ⊔ R₂.map (MulAut.conj h₂).toMonoidHom)

@[expose] def TripleFacts (i : ℕ) : Prop :=
  ∃ r0 T m te, CensusBase i r0 T m te ∧ ∀ r ∈ unitaryElts i, r ∉ ResPair.hyp10 i →
    ∃ h : V12 ≃ₗ[ZMod 2] V12, NLMem i h ∧ RowsConj h r r0 ∧
      CfgAll i r0 T m te fun R =>
        Viol.Violation (ResPair.n2 i ⊔ R.map (MulAut.conj h).toMonoidHom) (compOf i) (compOf i)

end CFSG.GF2Type.Smith1979.GammaU.StepA
