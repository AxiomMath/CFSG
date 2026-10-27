module

public import CFSG.GF2Type.Smith1979.IdxFourModelBase
public import CFSG.GF2Type.Smith1979.GammaU.Transport
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.RankThree.OrthogonalInvolutions

theorem fix_le_comm_of_anti {l : V12 ≃ₗ[ZMod 2] V12}
    (h : ∀ x, l (theta0 x) = theta0 (theta0 (l x))) : fixSpace l ≤ commSpace l := by
  intro v hv
  rw [mem_fixSpace] at hv
  refine mem_commSpace.2 ⟨theta0 v, ?_⟩
  rw [h, hv, theta0_theta0_eq, vec_sub_eq_add]
  funext j
  simp only [Pi.add_apply]
  generalize v j = a
  generalize (theta0 v) j = b
  revert a b
  decide

theorem outer_fix_le
    {l : V12 ≃ₗ[ZMod 2] V12} (hl : l ∈ Lbar0) (hE : l ∉ E0) :
    fixSpace l ≤ commSpace l := by
  refine fix_le_comm_of_anti fun x => ?_
  rcases conj_theta (M0_le_gammaU (mem_stabIn.1 (Lbar0_le_stab hl)).1) with h | h
  · refine absurd ((mem_E0_iff_unitary hl).2 ?_) hE
    calc l * omegaE = (l * omegaE * l⁻¹) * l := by group
      _ = omegaE * l := by rw [h]
  · have e := congrArg (fun e : V12 ≃ₗ[ZMod 2] V12 => e (l x)) h
    simp only [LinearEquiv.mul_apply, inv_apply_apply, omegaE_apply] at e
    exact e

@[expose] def Vt0 : Submodule (ZMod 2) V12 := spanOf vtBasis

theorem theta0_a0V : theta0 a0V = vecOf 960 := by
  have := vecOf_theta0N (n := 15) (by norm_num)
  rw [show theta0N 15 = 960 by decide] at this
  exact this.symm

theorem vtBasis_lt : ∀ v ∈ vtBasis, v < 4096 := by decide

theorem Vt0_le : Vt0 ≤ Submodule.span (ZMod 2) {y | ∃ l ∈ Lbar0,
    ∃ x : V12, f0 x a0V = 0 ∧ f0 x (theta0 a0V) = 0 ∧ y = l x - x} := by
  rw [theta0_a0V]
  exact Certificates.certificate17608.2.2.2.2.2.2.2

theorem finrank_spanOf_of_indep : ∀ vs : List ℕ, (∀ v ∈ vs, v < 4096) →
    (∀ i < vs.length, vs[i]! ∉ spanList (vs.drop (i + 1))) →
    Module.finrank (ZMod 2) (spanOf vs) = vs.length := by
  intro vs
  induction vs with
  | nil =>
    intro _ _
    simp [spanOf_nil]
  | cons v vs ih =>
    intro hlt hind
    have hv : v ∉ spanList vs := by simpa using hind 0 (by simp)
    have hvs : ∀ w ∈ vs, w < 4096 := fun w hw => hlt w (List.mem_cons_of_mem v hw)
    have := finrank_spanOf_cons (v := v) (vs := vs) (fun hmem => hv
      ((mem_spanList_iff hvs (hlt v List.mem_cons_self)).2 hmem))
    rw [this, ih hvs (fun i hi => by simpa using hind (i + 1) (by simpa using hi))]
    simp

theorem finrank_Vt0 : Module.finrank (ZMod 2) Vt0 = 6 :=
  finrank_spanOf_of_indep vtBasis vtBasis_lt (by decide +kernel)

end CFSG.GF2Type.Smith1979.IdxFour
