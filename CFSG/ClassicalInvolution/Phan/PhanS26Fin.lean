module

public import CFSG.ClassicalInvolution.Phan.PhanS25PairB
public import CFSG.ClassicalInvolution.Phan.PhanS20Model

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

@[expose] def zs7 : List (ZMod 7) := [0, 1, 2, 3, 4, 5, 6]

@[expose] def all49 : List GF49 := zs7.flatMap (fun x => zs7.map (fun y => (⟨x, y⟩ : GF49)))

theorem mem_zs7 (x : ZMod 7) : x ∈ zs7 := by revert x; decide

theorem mem_all49 (z : GF49) : z ∈ all49 := by
  obtain ⟨x, y⟩ := z
  simp only [all49, List.mem_flatMap, List.mem_map]
  exact ⟨x, mem_zs7 x, y, mem_zs7 y, rfl⟩

@[expose] def Fstar : List GF49 := [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨5, 0⟩, ⟨6, 0⟩]

@[expose] def canonSet : List GF49 :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨2, 2⟩, ⟨3, 2⟩,
    ⟨4, 2⟩, ⟨3, 3⟩]

@[expose] def zeta0 : GF49 := ⟨2, 2⟩

theorem fixed_mem_Fstar (x : GF49) (hx : star x = x) (h0 : x ≠ 0) : x ∈ Fstar := by
  obtain ⟨a, b⟩ := x
  revert a b
  decide

theorem norm_surj_aux : ∀ x ∈ Fstar, ∃ s ∈ all49, s * star s * x = 1 := by decide

theorem rot_exists_aux : ∀ η ∈ all49, ∃ ℓ ∈ all49, ℓ * star ℓ = 1 ∧ ℓ * ℓ * η ∈ canonSet := by
  decide

theorem ratio_exists_aux : ∀ ν ∈ all49, ν * star ν = 1 → ∃ ℓ ∈ all49, ℓ * star ℓ = 1 ∧
    (star ℓ * star ℓ * ν = 1 ∨ star ℓ * star ℓ * ν = zeta0) := by decide

@[expose] def addC (x y : V7) : V7 :=
  ⟨x.x0 + y.x0, x.x1 + y.x1, x.x2 + y.x2, x.x3 + y.x3, x.x4 + y.x4, x.x5 + y.x5, x.x6 + y.x6⟩

@[expose] def subC (x y : V7) : V7 :=
  ⟨x.x0 - y.x0, x.x1 - y.x1, x.x2 - y.x2, x.x3 - y.x3, x.x4 - y.x4, x.x5 - y.x5, x.x6 - y.x6⟩

@[expose] def zeroC : V7 := ⟨0, 0, 0, 0, 0, 0, 0⟩

theorem toVec_addC (x y : V7) : toVec (addC x y) = toVec x + toVec y := by
  funext i
  rcases i with i | i | i
  · fin_cases i <;> rfl
  · rcases i with i
    fin_cases i <;> rfl
  · rfl

theorem toVec_subC (x y : V7) : toVec (subC x y) = toVec x - toVec y := by
  funext i
  rcases i with i | i | i
  · fin_cases i <;> rfl
  · rcases i with i
    fin_cases i <;> rfl
  · rfl

theorem toVec_zeroC : toVec zeroC = 0 := by
  funext i
  rcases i with i | i | i
  · fin_cases i <;> rfl
  · rcases i with i
    fin_cases i <;> rfl
  · rfl

theorem toVec_eq_zero_iff (x : V7) : toVec x = 0 ↔ x = zeroC := by
  rw [← toVec_zeroC]
  exact ⟨fun h => toVec_injective h, fun h => by rw [h]⟩

@[expose] def eqC (x y : V7) : Bool :=
  x.x0 == y.x0 && x.x1 == y.x1 && x.x2 == y.x2 && x.x3 == y.x3 && x.x4 == y.x4 && x.x5 == y.x5 &&
    x.x6 == y.x6

theorem eqC_iff (x y : V7) : eqC x y = true ↔ x = y := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := y
  simp [eqC, V7.mk.injEq, and_assoc]

theorem eqC_eq_false_iff (x y : V7) : eqC x y = false ↔ x ≠ y := by
  rw [Bool.eq_false_iff]
  exact not_congr (eqC_iff x y)

theorem m0_tau (x : GF49) : m0.τ x = star x := rfl

@[expose] def NvecC (γ η : GF49) (c : V7) : V7 :=
  addC (addC (addC (smulC (-(star η * (γ - 1 - η * star η + 2))) e0C)
    (smulC (γ - 1 - η * star η) c))
    (smulC (-(γ - 1 - η * star η + 2 * (η * star η))) (tauC e0C)))
    (smulC (2 * star η) (tauC c))

theorem toVec_NvecC (γ η : GF49) (c : V7) :
    toVec (NvecC γ η c) = Nvec m0 γ η (toVec e0C) (toVec c) := by
  simp only [NvecC, Nvec, toVec_addC, toVec_smulC, toVec_tauC, m0_tau]

@[expose] def pvecC (c : V7) : V7 := subC e0C (tauC c)

theorem toVec_pvecC (c : V7) : toVec (pvecC c) = pvec m0 (toVec e0C) (toVec c) := by
  simp only [pvecC, pvec, toVec_subC, toVec_tauC]

structure ClassRep where
  γ : GF49
  η : GF49
  br : ℕ
  c : V7

structure TableOK (reps : List ClassRep) : Prop where
  valid : ∀ r ∈ reps, r.c.x3 = 1 ∧ isFFC r.c = true ∧ herC e0C r.c = r.η ∧
    herC r.c r.c = r.γ
  regular : ∀ γ ∈ Fstar, ∀ η ∈ canonSet, (η ≠ 0 ∨ γ ≠ 1) →
    ∃ r ∈ reps, r.γ = γ ∧ r.η = η ∧ r.br = 1
  deg0 : ∀ γ ∈ Fstar, ∀ η ∈ canonSet, η ≠ 0 → pairDisc γ η (star η) = 0 →
    ∃ r ∈ reps, r.γ = γ ∧ r.η = η ∧ r.br = 0
  nvec0 : ∀ r ∈ reps, r.br = 0 → eqC (NvecC r.γ r.η r.c) zeroC = true
  nvec1 : ∀ r ∈ reps, r.br = 1 → r.η ≠ 0 → eqC (NvecC r.γ r.η r.c) zeroC = false
  sp : ∀ b ∈ [102, 131, 146, 104], ∃ r ∈ reps, r.γ = 1 ∧ r.η = 0 ∧ r.br = b
  p102 : ∀ r ∈ reps, r.br = 102 → eqC (pvecC r.c) zeroC = true
  p131 : ∀ r ∈ reps, r.br = 131 → eqC (pvecC r.c) zeroC = false ∧
    eqC (tauC (pvecC r.c)) (smulC 1 (pvecC r.c)) = true
  p146 : ∀ r ∈ reps, r.br = 146 → eqC (pvecC r.c) zeroC = false ∧
    eqC (tauC (pvecC r.c)) (smulC zeta0 (pvecC r.c)) = true
  p104 : ∀ r ∈ reps, r.br = 104 → ∀ s ∈ all49, ∀ t ∈ all49,
    eqC (subC (smulC s (pvecC r.c)) (smulC t (tauC (pvecC r.c)))) zeroC = true →
      s = 0 ∧ t = 0

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
