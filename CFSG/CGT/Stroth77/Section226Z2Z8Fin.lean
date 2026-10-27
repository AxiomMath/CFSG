module

public import CFSG.CGT.Stroth77.TypePredicates
import CFSG.Mathlib.Decide.Bounded
public import Mathlib.Tactic.Linarith

public section

namespace CFSG.CGT.Stroth77

namespace Sec226Z

variable (τ : StrothTypeIndex)

abbrev Pair := Torus τ.k × Torus τ.k

@[expose] def muvt (m : Pair τ) : Torus τ.k := m.1 + τ.action.φuv m.2

@[expose] def tw (m : Pair τ) : Pair τ := (τ.action.φρ (muvt τ m), τ.action.φρ m.1)

@[expose] def uw (m : Pair τ) : Pair τ := (τ.action.φu m.1, τ.action.φu (muvt τ m))

@[expose] def cob (d : Torus τ.k) : Pair τ := (τ.action.φuv d - d, τ.action.φt d - d)

@[expose] def IsCoc (m : Pair τ) : Prop :=
  m.1 + τ.action.φuv m.1 = 0 ∧ m.2 + τ.action.φt m.2 = 0 ∧
    m.1 + τ.action.φuv m.2 = m.2 + τ.action.φt m.1

instance (m : Pair τ) : Decidable (IsCoc τ m) := by unfold IsCoc; infer_instance

@[expose] def InE (v : Torus τ.k) : Prop := v + v = 0 ∧ τ.action.φuv v = v

instance (v : Torus τ.k) : Decidable (InE τ v) := by unfold InE; infer_instance

@[expose] def IsE (m : Pair τ) : Prop := InE τ m.1 ∧ InE τ m.2

instance (m : Pair τ) : Decidable (IsE τ m) := by unfold IsE; infer_instance

@[expose] def βlin (β : Pair τ) (w : Torus τ.k) : Torus τ.k := (w 1).val • β.1 + (w 2).val • β.2

@[expose] def βapp (β : Pair τ) (m : Pair τ) : Pair τ := (βlin τ β m.1, βlin τ β m.2)

@[expose] def act (φ ψ : Torus τ.k →+ Torus τ.k) (β : Pair τ) : Pair τ :=
  (φ (βlin τ β (ψ (gen τ.k 1))), φ (βlin τ β (ψ (gen τ.k 2))))

@[expose] def IsShift (β : Pair τ) : Prop := β.1 + β.1 = 0 ∧ β.2 + β.2 = 0

instance (β : Pair τ) : Decidable (IsShift τ β) := by unfold IsShift; infer_instance

@[expose] def IsShift16 (β : Pair τ) : Prop := IsShift τ β ∧ β.1 0 = 0 ∧ β.2 0 = 0

instance (β : Pair τ) : Decidable (IsShift16 τ β) := by unfold IsShift16; infer_instance

@[expose] def tor (x y z : ℕ) : Torus τ.k := x • gen τ.k 0 + y • gen τ.k 1 + z • gen τ.k 2

@[expose] def w₂ : Pair τ := (tor τ 0 4 0, tor τ 0 0 4)
@[expose] def β₁ : Pair τ := (tor τ 0 0 4, tor τ 0 4 0)
@[expose] def β₂ : Pair τ := (tor τ 0 4 0, tor τ 0 4 4)
@[expose] def β₃ : Pair τ := (tor τ 0 4 4, tor τ 0 0 4)
@[expose] def β₅ : Pair τ := (tor τ 0 0 4, tor τ 0 4 4)
@[expose] def β₆ : Pair τ := (tor τ 0 4 4, tor τ 0 4 0)

@[expose] def W4Hyp (m : Pair τ) : Prop :=
  (∃ du : Torus τ.k, uw τ m = m + cob τ du) ∧
    (∃ d : Torus τ.k, tw τ (tw τ m) = m + βapp τ (β₂ τ) m + tw τ m + cob τ d) ∧
    ∃ d : Torus τ.k, tw τ (tw τ (tw τ m)) = m + cob τ d

instance : DecidablePred (W4Hyp τ) := fun m => by unfold W4Hyp; infer_instance

@[expose] def W4Concl (m : Pair τ) : Prop :=
  (∃ d : Torus τ.k, IsE τ (m + cob τ d)) ∨ (∃ d : Torus τ.k, IsE τ (tw τ m + cob τ d)) ∨
    (∃ d : Torus τ.k, IsE τ (tw τ (tw τ m) + cob τ d)) ∨
    ∃ d : Torus τ.k, tw τ m + cob τ (τ.action.φρ d) = m + cob τ d

instance : DecidablePred (W4Concl τ) := fun m => by unfold W4Concl; infer_instance

@[expose] def U2Hyp (m : Pair τ) : Prop :=
  IsCoc τ m ∧ tw τ m = m ∧ ∃ q : Torus τ.k, τ.action.φρ q = q ∧ βlin τ (β₅ τ) q = 0 ∧
    τ.action.φuv q = q + 2 • m.1 + βlin τ (β₅ τ) m.1 ∧
    τ.action.φt q = q + 2 • m.2 + βlin τ (β₅ τ) m.2

instance : DecidablePred (U2Hyp τ) := fun m => by unfold U2Hyp; infer_instance

@[expose] def U2Concl (m : Pair τ) : Prop :=
  (∃ d : Torus τ.k, IsE τ (m + cob τ d)) ∨ (∃ d : Torus τ.k, IsE τ (uw τ m + cob τ d)) ∨
    ∃ d : Torus τ.k, IsE τ (m + βapp τ (β₆ τ) m + uw τ m + cob τ d)

instance : DecidablePred (U2Concl τ) := fun m => by unfold U2Concl; infer_instance

@[expose] def EFact : Prop :=
  ∀ v : Torus τ.k, v + v = 0 → v ≠ 0 → τ.action.φuv v = v → ∀ w : Torus τ.k, InE τ w →
    w = 0 ∨ w = v ∨ w = τ.action.φρ v ∨ w = v + τ.action.φρ v

instance : Decidable (EFact τ) := by unfold EFact; infer_instance

abbrev τ₀ : StrothTypeIndex := .t200 1
abbrev τ₁ : StrothTypeIndex := .t201 1

@[expose] def reps₀ : List (Pair τ₀) :=
  [(tor _ 0 0 0, tor _ 0 0 0), (tor _ 0 0 0, tor _ 0 0 4), (tor _ 0 0 0, tor _ 1 2 2),
    (tor _ 0 0 0, tor _ 1 2 6), (tor _ 0 1 3, tor _ 0 1 0), (tor _ 0 1 3, tor _ 0 1 4),
    (tor _ 0 1 3, tor _ 1 3 2), (tor _ 0 1 3, tor _ 1 3 6)]

@[expose] def reps₁ : List (Pair τ₁) :=
  [(tor _ 0 0 0, tor _ 0 0 0), (tor _ 0 0 0, tor _ 0 0 4), (tor _ 0 0 0, tor _ 1 2 2),
    (tor _ 0 0 0, tor _ 1 2 6), (tor _ 0 1 1, tor _ 0 3 2), (tor _ 0 1 1, tor _ 0 3 6),
    (tor _ 0 1 1, tor _ 1 1 0), (tor _ 0 1 1, tor _ 1 1 4)]

@[instance_reducible] private def decEqTorus (k : Fin 3 → ℕ) : DecidableEq (Torus k) :=
  fun f g => decidable_of_iff (f 0 = g 0 ∧ f 1 = g 1 ∧ f 2 = g 2) <| by
    refine ⟨fun ⟨h0, h1, h2⟩ => funext fun i => ?_, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩
    fin_cases i <;> assumption

private theorem forall_coc {P : Torus τ.k → Torus τ.k → Prop}
    (h : ∀ x : Torus τ.k, x + τ.action.φuv x = 0 → ∀ y : Torus τ.k, y + τ.action.φt y = 0 →
      x + τ.action.φuv y = y + τ.action.φt x → P x y) :
    ∀ x y : Torus τ.k, IsCoc τ (x, y) → P x y :=
  fun x y hm => h x hm.1 y hm.2.1 hm.2.2

private theorem forall_coc_exists {P : Torus τ.k → Torus τ.k → Torus τ.k → Prop}
    (h : ∀ x : Torus τ.k, x + τ.action.φuv x = 0 → ∀ y : Torus τ.k, y + τ.action.φt y = 0 →
      x + τ.action.φuv y = y + τ.action.φt x → ∃ i < 2, ∃ j < 4, ∃ l < 4, P x y (tor τ i j l)) :
    ∀ x y : Torus τ.k, IsCoc τ (x, y) → ∃ d, P x y d :=
  forall_coc τ fun x hx y hy hxy => let ⟨_, _, _, _, _, _, hP⟩ := h x hx y hy hxy; ⟨_, hP⟩

section

attribute [local instance high] decEqTorus

theorem exists_rep_t200 :
    ∀ x y : Torus τ₀.k, IsCoc τ₀ (x, y) → ∃ d : Torus τ₀.k, (x, y) + cob τ₀ d ∈ reps₀ :=
  forall_coc_exists τ₀ (by decide +kernel)

theorem exists_rep_t201 :
    ∀ x y : Torus τ₁.k, IsCoc τ₁ (x, y) → ∃ d : Torus τ₁.k, (x, y) + cob τ₁ d ∈ reps₁ :=
  forall_coc_exists τ₁ (by decide +kernel)

open scoped CFSG.Decide.Bounded in
private theorem w4_reps_t200 : ∀ m ∈ reps₀, W4Hyp τ₀ m → W4Concl τ₀ m := by decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem w4_reps_t201 : ∀ m ∈ reps₁, W4Hyp τ₁ m → W4Concl τ₁ m := by decide +kernel

theorem w4_finite_t200 :
    ∀ x y : Torus τ₀.k, (x, y) ∈ reps₀ → W4Hyp τ₀ (x, y) → W4Concl τ₀ (x, y) :=
  fun x y => w4_reps_t200 (x, y)

theorem w4_finite_t201 :
    ∀ x y : Torus τ₁.k, (x, y) ∈ reps₁ → W4Hyp τ₁ (x, y) → W4Concl τ₁ (x, y) :=
  fun x y => w4_reps_t201 (x, y)

theorem u2_finite_t200 : ∀ x y : Torus τ₀.k, U2Hyp τ₀ (x, y) → U2Concl τ₀ (x, y) := by
  have key : ∀ x y : Torus τ₀.k, IsCoc τ₀ (x, y) → tw τ₀ (x, y) = (x, y) → U2Hyp τ₀ (x, y) →
      U2Concl τ₀ (x, y) :=
    forall_coc τ₀ (by decide +kernel)
  exact fun x y h => key x y h.1 h.2.1 h

theorem u2_finite_t201 : ∀ x y : Torus τ₁.k, U2Hyp τ₁ (x, y) → U2Concl τ₁ (x, y) := by
  have key : ∀ x y : Torus τ₁.k, IsCoc τ₁ (x, y) → tw τ₁ (x, y) = (x, y) → U2Hyp τ₁ (x, y) →
      U2Concl τ₁ (x, y) :=
    forall_coc τ₁ (by decide +kernel)
  exact fun x y h => key x y h.1 h.2.1 h

end

@[expose] def actUv (β : Pair τ) : Pair τ := act τ τ.action.φuv τ.action.φuv β
@[expose] def actT (β : Pair τ) : Pair τ := act τ τ.action.φt τ.action.φt β
@[expose] def actU (β : Pair τ) : Pair τ := act τ τ.action.φu τ.action.φu β
@[expose] def actRho (β : Pair τ) : Pair τ := act τ τ.action.φρ (τ.action.φρ.comp τ.action.φρ) β

@[expose] def CommFact : Prop :=
  ∀ x y : Torus τ.k, IsShift τ (x, y) →
    IsShift16 τ (actUv τ (x, y) + (x, y)) ∧ IsShift16 τ (actT τ (x, y) + (x, y))

instance : Decidable (CommFact τ) := by unfold CommFact; infer_instance

@[expose] def FixFact : Prop :=
  ∀ x y : Torus τ.k, IsShift τ (x, y) →
    (actUv τ (x, y) + (x, y) = 0 ∨ actUv τ (x, y) + (x, y) = w₂ τ) →
    (actT τ (x, y) + (x, y) = 0 ∨ actT τ (x, y) + (x, y) = w₂ τ) → IsShift16 τ (x, y)

instance : Decidable (FixFact τ) := by unfold FixFact; infer_instance

@[expose] def SocleFact : Prop :=
  ∀ x y : Torus τ.k, IsShift16 τ (x, y) → (x, y) ≠ 0 → (x, y) ≠ w₂ τ →
    (actRho τ (x, y) + actRho τ (actRho τ (x, y)) = β₁ τ ∨
      actRho τ (x, y) + actRho τ (actRho τ (x, y)) = β₂ τ ∨
      actRho τ (x, y) + actRho τ (actRho τ (x, y)) = β₃ τ) ∨
    (actRho τ (x, y) + actRho τ (actRho τ (x, y)) = 0 ∧ ((x, y) = β₅ τ ∨ (x, y) = β₆ τ))

instance : Decidable (SocleFact τ) := by unfold SocleFact; infer_instance

@[expose] def OrbitFact₁ : Prop :=
  actRho τ (β₁ τ) = β₂ τ ∧ actRho τ (β₂ τ) = β₃ τ ∧ actRho τ (β₃ τ) = β₁ τ ∧
  actUv τ (β₁ τ) = β₁ τ ∧ actT τ (β₁ τ) = β₁ τ ∧ actU τ (β₁ τ) = β₁ τ

instance : Decidable (OrbitFact₁ τ) := by unfold OrbitFact₁; infer_instance

@[expose] def OrbitFact₅ : Prop :=
  actUv τ (β₅ τ) = β₅ τ ∧ actT τ (β₅ τ) = β₅ τ ∧ actRho τ (β₅ τ) = β₅ τ ∧
  actU τ (β₅ τ) = β₆ τ ∧ actU τ (β₆ τ) = β₅ τ

instance : Decidable (OrbitFact₅ τ) := by unfold OrbitFact₅; infer_instance

@[expose] def SumFact : Prop :=
  β₁ τ + β₂ τ = β₃ τ ∧ β₅ τ + β₆ τ = w₂ τ ∧ β₁ τ ≠ β₂ τ ∧
  β₁ τ ≠ 0 ∧ β₂ τ ≠ 0 ∧ β₃ τ ≠ 0 ∧ β₅ τ ≠ 0 ∧ β₆ τ ≠ 0 ∧ w₂ τ ≠ 0

instance : Decidable (SumFact τ) := by unfold SumFact; infer_instance

private def invs : List (Torus τ.k) :=
  [tor τ 0 0 0, tor τ 0 0 4, tor τ 0 4 0, tor τ 0 4 4, tor τ 1 0 0, tor τ 1 0 4, tor τ 1 4 0,
    tor τ 1 4 4]

private theorem mem_invs_t200 : ∀ x : Torus τ₀.k, x + x = 0 → x ∈ invs τ₀ := by decide +kernel
private theorem mem_invs_t201 : ∀ x : Torus τ₁.k, x + x = 0 → x ∈ invs τ₁ := by decide +kernel

private theorem forall_shift {l : List (Torus τ.k)} (hl : ∀ x : Torus τ.k, x + x = 0 → x ∈ l)
    {P : Torus τ.k → Torus τ.k → Prop} (h : ∀ x ∈ l, ∀ y ∈ l, P x y) :
    ∀ x y : Torus τ.k, IsShift τ (x, y) → P x y :=
  fun x y hβ => h x (hl x hβ.1) y (hl y hβ.2)

private theorem forall_shift16 {l : List (Torus τ.k)} (hl : ∀ x : Torus τ.k, x + x = 0 → x ∈ l)
    {P : Torus τ.k → Torus τ.k → Prop} (h : ∀ x ∈ l, ∀ y ∈ l, IsShift16 τ (x, y) → P x y) :
    ∀ x y : Torus τ.k, IsShift16 τ (x, y) → P x y :=
  fun x y hβ => h x (hl x hβ.1.1) y (hl y hβ.1.2) hβ

theorem eFact_t200 : EFact τ₀ := by decide +kernel
open scoped CFSG.Decide.Bounded in
theorem commFact_t200 : CommFact τ₀ := forall_shift τ₀ mem_invs_t200 (by decide +kernel)
open scoped CFSG.Decide.Bounded in
theorem fixFact_t200 : FixFact τ₀ := forall_shift τ₀ mem_invs_t200 (by decide +kernel)
open scoped CFSG.Decide.Bounded in
theorem socleFact_t200 : SocleFact τ₀ := forall_shift16 τ₀ mem_invs_t200 (by decide +kernel)
theorem orbitFact₁_t200 : OrbitFact₁ τ₀ := by decide +kernel
theorem orbitFact₅_t200 : OrbitFact₅ τ₀ := by decide +kernel
theorem sumFact_t200 : SumFact τ₀ := by decide +kernel

theorem eFact_t201 : EFact τ₁ := by decide +kernel
open scoped CFSG.Decide.Bounded in
theorem commFact_t201 : CommFact τ₁ := forall_shift τ₁ mem_invs_t201 (by decide +kernel)
open scoped CFSG.Decide.Bounded in
theorem fixFact_t201 : FixFact τ₁ := forall_shift τ₁ mem_invs_t201 (by decide +kernel)
open scoped CFSG.Decide.Bounded in
theorem socleFact_t201 : SocleFact τ₁ := forall_shift16 τ₁ mem_invs_t201 (by decide +kernel)
theorem orbitFact₁_t201 : OrbitFact₁ τ₁ := by decide +kernel
theorem orbitFact₅_t201 : OrbitFact₅ τ₁ := by decide +kernel
theorem sumFact_t201 : SumFact τ₁ := by decide +kernel

end Sec226Z

end CFSG.CGT.Stroth77
