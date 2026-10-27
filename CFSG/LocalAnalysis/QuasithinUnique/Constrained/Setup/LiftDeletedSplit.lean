module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftRetraction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.SL2Modules

section Dot

variable {Ω : Type*} [Fintype Ω]

@[expose] def dotForm (Ω : Type*) [Fintype Ω] :
    ↥(SL2Modules.evenWeight Ω) →ₗ[ZMod 2] ↥(SL2Modules.evenWeight Ω) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ∑ ω, (x : Ω → ZMod 2) ω * (y : Ω → ZMod 2) ω)
    (fun x x' y => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun x y y' => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      ring)

theorem dotForm_apply (x y : ↥(SL2Modules.evenWeight Ω)) :
    dotForm Ω x y = ∑ ω, (x : Ω → ZMod 2) ω * (y : Ω → ZMod 2) ω := rfl

theorem dotForm_comm (x y : ↥(SL2Modules.evenWeight Ω)) : dotForm Ω x y = dotForm Ω y x := by
  simp only [dotForm_apply, mul_comm]

theorem dotForm_perm (σ : Equiv.Perm Ω) (x y : ↥(SL2Modules.evenWeight Ω))
    (hx : permAct σ (x : Ω → ZMod 2) ∈ SL2Modules.evenWeight Ω) (hy : permAct σ (y : Ω → ZMod 2) ∈ SL2Modules.evenWeight Ω) :
    dotForm Ω ⟨permAct σ (x : Ω → ZMod 2), hx⟩ ⟨permAct σ (y : Ω → ZMod 2), hy⟩ = dotForm Ω x y := by
  simp only [dotForm_apply, permAct]
  exact Equiv.sum_comp σ.symm (fun ω => (x : Ω → ZMod 2) ω * (y : Ω → ZMod 2) ω)

variable [DecidableEq Ω] in
theorem dotForm_nondeg (h5 : Fintype.card Ω = 5) (x : ↥(SL2Modules.evenWeight Ω))
    (h : ∀ y, dotForm Ω x y = 0) : x = 0 := by
  by_contra hx0
  have : ∃ a, (x : Ω → ZMod 2) a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (Subtype.ext (funext hcon))
  obtain ⟨a, ha⟩ := this
  have ha1 : (x : Ω → ZMod 2) a = 1 := by
    rcases zmod2_cases ((x : Ω → ZMod 2) a) with h0 | h1
    · exact absurd h0 ha
    · exact h1
  have : ∃ b, (x : Ω → ZMod 2) b = 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ ω, (x : Ω → ZMod 2) ω = 1 := fun ω => by
      rcases zmod2_cases ((x : Ω → ZMod 2) ω) with h0 | h1
      · exact absurd h0 (hcon ω)
      · exact h1
    have hsum : ∑ ω, (x : Ω → ZMod 2) ω = 0 := x.2
    simp only [hall, Finset.sum_const, Finset.card_univ, h5] at hsum
    revert hsum
    decide
  obtain ⟨b, hb⟩ := this
  have hy := h ⟨delta a + delta b, delta_add_delta_mem a b⟩
  have hsum : ∀ c : Ω, ∑ ω, (x : Ω → ZMod 2) ω * delta c ω = (x : Ω → ZMod 2) c := by
    intro c
    simp [delta, Pi.single_apply]
  rw [dotForm_apply] at hy
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hsum] at hy
  rw [ha1, hb] at hy
  simp at hy

variable [DecidableEq Ω] in
theorem deleted_retraction (h5 : Fintype.card Ω = 5) {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρV : Representation (ZMod 2) ↥(alternatingGroup Ω) V)
    (ι : ↥(SL2Modules.evenWeight Ω) →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (hιeq : ∀ s x, ι (deletedRep (alternatingGroup Ω) Ω s x) = ρV s (ι x)) :
    ∃ P : V →ₗ[ZMod 2] ↥(SL2Modules.evenWeight Ω), (∀ x, P (ι x) = x) ∧
      ∀ s v, P (ρV s v) = deletedRep (alternatingGroup Ω) Ω s (P v) := by
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  have hnd := dotForm_nondeg (Ω := Ω) h5
  have hcomm := dotForm_comm (Ω := Ω)
  have hinv : ∀ (g : ↥(alternatingGroup Ω)) (x y : ↥(SL2Modules.evenWeight Ω)),
      dotForm Ω (deletedRep (alternatingGroup Ω) Ω g x) (deletedRep (alternatingGroup Ω) Ω g y) =
        dotForm Ω x y := fun g x y => dotForm_perm (MulAction.toPerm g) x y _ _
  have hsplit : ∀ π : Module.Dual (ZMod 2) V →ₗ[ZMod 2] ↥(SL2Modules.evenWeight Ω),
      Function.Surjective π →
      (∀ g f, π (ρV.dual g f) = deletedRep (alternatingGroup Ω) Ω g (π f)) →
      ∃ j : ↥(SL2Modules.evenWeight Ω) →ₗ[ZMod 2] Module.Dual (ZMod 2) V, (∀ x, π (j x) = x) ∧
        ∀ g x, j (deletedRep (alternatingGroup Ω) Ω g x) = ρV.dual g (j x) :=
    fun π hπs hπ =>
      deleted_five_quotient_equivariant_section h5 (E := Module.Dual (ZMod 2) V) ρV.dual π hπs hπ
  exact retraction_of_selfdual_splitting (K := ZMod 2) _ ρV (dotForm Ω) hnd hcomm hinv hsplit ι
    hι hιeq

end Dot

end CFSG.QuasithinUnique.Setup.Lift
