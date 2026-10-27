module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelTheta

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

def cSideFix (g : SL2 × SL2) : Finset V0 :=
  Finset.univ.filter fun M => actFun g M = M

def cSideE11 : V0 := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

def cSideZeroOn (F : Finset V0) : Prop := ∀ M ∈ F, M = 0

def cSideNondegOn (F : Finset V0) : Prop :=
  ∀ M ∈ F, M ≠ 0 → ∃ N ∈ F, q0Polar M N ≠ 0

def cSidePlaneOn (F : Finset V0) : Prop :=
  ∃ M ∈ F, ∃ N ∈ F, M ≠ 0 ∧ N ≠ 0 ∧ M ≠ N ∧ q0Fun M = 0 ∧ q0Fun N = 0 ∧ q0Polar M N = 0

def cSideNondegAt (g : SL2 × SL2) : Prop := cSideNondegOn (cSideFix g)

def cSidePlaneAt (g : SL2 × SL2) : Prop := cSidePlaneOn (cSideFix g)

def cSideSwapCent (g : SL2 × SL2) : Prop :=
  (∃ x : SL2, x * frobSL g.2 = g.1 * x) ∧ (∃ x : SL2, x * frobSL g.1 = g.2 * x)

def cSideK1 : Prop :=
  ∀ g : SL2 × SL2, (g ^ 3 = 1 ∨ g ^ 5 = 1) → g ≠ 1 → (g.1 = 1 ∨ g.2 = 1) →
    ∀ M ∈ cSideFix g, M = 0

def cSideK2 : Prop :=
  ∀ g : SL2 × SL2, g ^ 3 = 1 → g.1 ≠ 1 → g.2 ≠ 1 →
    (cSideFix g).card = 16 ∧ cSideNondegAt g ∧ cSidePlaneAt g

def cSideK3 : Prop := ∀ g : SL2 × SL2, g ^ 2 = 1 → g ≠ 1 → (cSideFix g).card = 16

def cSideK4a : Prop :=
  ∀ M : V0, (M ≠ 0 ∧ q0Fun M = 0) ↔ ((M ≠ 0 ∧ det0 M = 0) ∨ det0 M = 1)

def cSideK4b : Prop :=
  ∀ N : V0, N ≠ 0 → det0 N = 0 → ∃ g : SL2 × SL2, actFun g cSideE11 = N

def cSideK4c : Prop := ∀ N : V0, det0 N = 1 → ∃ g : SL2 × SL2, actFun g 1 = N

def cSideK4d : Prop :=
  (Finset.univ.filter fun M : V0 => M ≠ 0 ∧ det0 M = 0).card = 75 ∧
  (Finset.univ.filter fun M : V0 => det0 M = 1).card = 60

def cSideK6a : Prop :=
  (∀ M : V0, q0Fun (b0Fun M) = q0Fun M) ∧ (Finset.univ.filter fun M : V0 => b0Fun M = M).card = 16

theorem omegaFun_actFun (g : SL2 × SL2) (M : V0) :
    omegaFun (actFun g M) = actFun g (omegaFun M) := by
  simp only [omegaFun, actFun, Matrix.mul_smul, Matrix.smul_mul]

def cSideK6c : Prop :=
  (∀ M : V0, omegaFun (omegaFun M) + omegaFun M + M = 0) ∧
  (∀ M : V0, b0Fun (omegaFun M) = omegaFun (omegaFun (b0Fun M)))

def cSideGood2 (F : Finset V0) : Prop := F.card = 16 ∧ cSideNondegOn F ∧ cSidePlaneOn F

def cSideGood5 (F : Finset V0) : Prop := F.card = 16 ∧ cSideNondegOn F ∧ ¬ cSidePlaneOn F

def cSideModelProp : Prop :=
  cSideK1 ∧ cSideK2 ∧ cSideK3 ∧ (cSideK4a ∧ cSideK4b ∧ cSideK4c ∧ cSideK4d) ∧
    ((∀ g : SL2 × SL2, g ^ 5 = 1 → g.1 ≠ 1 → g.2 ≠ 1 → cSideSwapCent g → ∀ M ∈ cSideFix g, M =
        0) ∧ (∀ g : SL2 × SL2, g ^ 5 = 1 → g.1 ≠ 1 → g.2 ≠ 1 → ¬ cSideSwapCent g → (cSideFix
        g).card = 16 ∧ cSideNondegAt g ∧ ¬ cSidePlaneAt g)) ∧ (cSideK6a ∧ cSideK6c)

end CFSG.EvenSporadicStandard.HNRecog.CSide
