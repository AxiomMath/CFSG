module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux1
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAuxAlg

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section Bridge

open T7

variable {L : Type} [Field L] [CharP L 2]

@[expose] def crd (v : V L) : T7 L := ⟨v rS, v rA1, v rA2, v rA3, v rB12, v rB13, v rB23⟩

theorem crd_add (v v' : V L) : crd (v + v') = crd v + crd v' := rfl

theorem crd_smul (c : L) (v : V L) : crd (c • v) = c • crd v := rfl

theorem crd_zero : crd (0 : V L) = 0 := rfl

variable (AD : ActData L)

theorem crd_act_g5 {v : V L} (hv : Supp v) (t : L) :
    crd (actFun AD.a1 AD.a2 g5 t v) = opG5 t (crd v) := by
  ext <;> simp [crd, actc_g5_rS AD hv, actc_g5_rA1 AD hv, actc_g5_rA2 AD hv, actc_g5_rA3 AD hv,
    actc_g5_rB12 AD hv, actc_g5_rB13 AD hv, actc_g5_rB23 AD hv]

theorem crd_act_g5n {v : V L} (hv : Supp v) (t : L) :
    crd (actFun AD.a1 AD.a2 g5n t v) = opG5n t (crd v) := by
  ext <;> simp [crd, actc_g5n_rS AD hv, actc_g5n_rA1 AD hv, actc_g5n_rA2 AD hv, actc_g5n_rA3 AD hv,
    actc_g5n_rB12 AD hv, actc_g5n_rB13 AD hv, actc_g5n_rB23 AD hv]

theorem crd_act_a3 {v : V L} (hv : Supp v) (t : L) :
    crd (actFun AD.a1 AD.a2 a3 t v) = opA3 t (crd v) := by
  ext <;> simp [crd, actc_a3_rS AD hv, actc_a3_rA1 AD hv, actc_a3_rA2 AD hv, actc_a3_rA3 AD hv,
    actc_a3_rB12 AD hv, actc_a3_rB13 AD hv, actc_a3_rB23 AD hv]

theorem crd_act_a4 {v : V L} (hv : Supp v) (t : L) :
    crd (actFun AD.a1 AD.a2 a4 t v) = opA4 t (crd v) := by
  ext <;> simp [crd, actc_a4_rS AD hv, actc_a4_rA1 AD hv, actc_a4_rA2 AD hv, actc_a4_rA3 AD hv,
    actc_a4_rB12 AD hv, actc_a4_rB13 AD hv, actc_a4_rB23 AD hv]

end Bridge

section WTable

@[expose] def pS : Fin Tag.F4.rank → ℤ := ![1, 3, 4, 2]
@[expose] def pA1 : Fin Tag.F4.rank → ℤ := ![1, 2, 2, 0]
@[expose] def pA2 : Fin Tag.F4.rank → ℤ := ![1, 2, 2, 2]
@[expose] def pA3 : Fin Tag.F4.rank → ℤ := ![1, 2, 4, 2]
@[expose] def pB12 : Fin Tag.F4.rank → ℤ := ![1, 2, 2, 1]
@[expose] def pB13 : Fin Tag.F4.rank → ℤ := ![1, 2, 3, 1]
@[expose] def pB23 : Fin Tag.F4.rank → ℤ := ![1, 2, 3, 2]

theorem w_smul_eq (μ : Fin Tag.F4.rank → ℤ) :
    wF4 • μ = TwClass.wordF4.foldr (reflect Tag.F4) μ :=
  wordProd_smul_eq_foldr Tag.F4 TwClass.wordF4 μ

theorem w_rS : wF4 • rS = pS := by rw [w_smul_eq]; decide +kernel
theorem w_rA1 : wF4 • rA1 = pA1 := by rw [w_smul_eq]; decide +kernel
theorem w_rA2 : wF4 • rA2 = pA2 := by rw [w_smul_eq]; decide +kernel
theorem w_rA3 : wF4 • rA3 = pA3 := by rw [w_smul_eq]; decide +kernel
theorem w_rB12 : wF4 • rB12 = pB12 := by rw [w_smul_eq]; decide +kernel
theorem w_rB13 : wF4 • rB13 = pB13 := by rw [w_smul_eq]; decide +kernel
theorem w_rB23 : wF4 • rB23 = pB23 := by rw [w_smul_eq]; decide +kernel
theorem w_pS : wF4 • pS = rS := by rw [w_smul_eq]; decide +kernel
theorem w_pA1 : wF4 • pA1 = rA1 := by rw [w_smul_eq]; decide +kernel
theorem w_pA2 : wF4 • pA2 = rA2 := by rw [w_smul_eq]; decide +kernel
theorem w_pA3 : wF4 • pA3 = rA3 := by rw [w_smul_eq]; decide +kernel
theorem w_pB12 : wF4 • pB12 = rB12 := by rw [w_smul_eq]; decide +kernel
theorem w_pB13 : wF4 • pB13 = rB13 := by rw [w_smul_eq]; decide +kernel
theorem w_pB23 : wF4 • pB23 = rB23 := by rw [w_smul_eq]; decide +kernel
theorem w_g5 : wF4 • g5 = g5 := by rw [w_smul_eq]; decide +kernel
theorem w_g5n : wF4 • g5n = g5n := by rw [w_smul_eq]; decide +kernel
theorem w_a3 : wF4 • a3 = a4 := by rw [w_smul_eq]; decide +kernel
theorem w_a4 : wF4 • a4 = a3 := by rw [w_smul_eq]; decide +kernel

theorem deg1_cases : ∀ ν ∈ rootFinset Tag.F4, ν 0 = 1 →
    (ν = rS ∨ ν = rA1 ∨ ν = rA2 ∨ ν = rA3 ∨ ν = rB12 ∨ ν = rB13 ∨ ν = rB23) ∨
    (ν = pS ∨ ν = pA1 ∨ ν = pA2 ∨ ν = pA3 ∨ ν = pB12 ∨ ν = pB13 ∨ ν = pB23) := by
  decide +kernel

end WTable

section Determined

open T7

variable {L : Type} [Field L] [CharP L 2] {Fr : L →+* L}

@[expose] def fv (Fr : L →+* L) (μ : Fin Tag.F4.rank → ℤ) (l : L) : V L :=
  Pi.single μ l + Pi.single (wF4 • μ) (Fr l)

theorem eq_of_crd {u u' : V L} (hs : Supp u) (hs' : Supp u')
    (hf : ∀ ν, u ν = Fr (u (wF4⁻¹ • ν))) (hf' : ∀ ν, u' ν = Fr (u' (wF4⁻¹ • ν)))
    (h : crd u = crd u') : u = u' := by
  funext ν
  by_cases hν : ν ∈ Deg1 Tag.F4
  · have hr := mem_rootFinset.2 hν.1
    have h1 : ν 0 = 1 := hν.2
    have eS : u rS = u' rS := congrArg T7.s h
    have eA1 : u rA1 = u' rA1 := congrArg T7.a1 h
    have eA2 : u rA2 = u' rA2 := congrArg T7.a2 h
    have eA3 : u rA3 = u' rA3 := congrArg T7.a3 h
    have eB12 : u rB12 = u' rB12 := congrArg T7.b12 h
    have eB13 : u rB13 = u' rB13 := congrArg T7.b13 h
    have eB23 : u rB23 = u' rB23 := congrArg T7.b23 h
    have inv : ∀ {ρ p : Fin Tag.F4.rank → ℤ}, wF4 • ρ = p → wF4⁻¹ • p = ρ := by
      intro ρ p hρ
      rw [inv_smul_eq_iff]
      exact hρ.symm
    rcases deg1_cases ν hr h1 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact eS
    · exact eA1
    · exact eA2
    · exact eA3
    · exact eB12
    · exact eB13
    · exact eB23
    · rw [hf, hf', inv w_rS, eS]
    · rw [hf, hf', inv w_rA1, eA1]
    · rw [hf, hf', inv w_rA2, eA2]
    · rw [hf, hf', inv w_rA3, eA3]
    · rw [hf, hf', inv w_rB12, eB12]
    · rw [hf, hf', inv w_rB13, eB13]
    · rw [hf, hf', inv w_rB23, eB23]
  · rw [hs ν hν, hs' ν hν]

theorem rep_E {u : V L} (hf : ∀ ν, u ν = Fr (u (wF4⁻¹ • ν))) {ρ p : Fin Tag.F4.rank → ℤ}
    (h1 : wF4 • ρ = p) (h2 : wF4 • p = ρ) : InE Fr (u ρ) := by
  have e1 : wF4⁻¹ • ρ = p := by rw [inv_smul_eq_iff]; exact h2.symm
  have e2 : wF4⁻¹ • p = ρ := by rw [inv_smul_eq_iff]; exact h1.symm
  have a := hf ρ
  rw [e1] at a
  have b := hf p
  rw [e2] at b
  unfold InE
  rw [← b, ← a]

theorem crd_E {u : V L} (hf : ∀ ν, u ν = Fr (u (wF4⁻¹ • ν))) :
    InE Fr (crd u).s ∧ InE Fr (crd u).a1 ∧ InE Fr (crd u).a2 ∧ InE Fr (crd u).a3 ∧
      InE Fr (crd u).b12 ∧ InE Fr (crd u).b13 ∧ InE Fr (crd u).b23 :=
  ⟨rep_E hf w_rS w_pS, rep_E hf w_rA1 w_pA1, rep_E hf w_rA2 w_pA2, rep_E hf w_rA3 w_pA3,
    rep_E hf w_rB12 w_pB12, rep_E hf w_rB13 w_pB13, rep_E hf w_rB23 w_pB23⟩

theorem fv_apply_ne {ρ μ : Fin Tag.F4.rank → ℤ} (l : L) (h1 : ρ ≠ μ) (h2 : ρ ≠ wF4 • μ) :
    fv Fr μ l ρ = 0 := by
  simp [fv, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]

theorem fv_apply_self (μ : Fin Tag.F4.rank → ℤ) (l : L) (h2 : μ ≠ wF4 • μ) :
    fv Fr μ l μ = l := by
  simp [fv, Pi.single_eq_of_ne h2]

end Determined

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

