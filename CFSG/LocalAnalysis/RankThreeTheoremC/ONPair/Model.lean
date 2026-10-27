module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.Words
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelFacts
public import Certificates.Certificate753505

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open scoped MatrixGroups
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Phan.Q3G CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Checks

theorem qP_rels : ∀ r ∈ sl3Rels7, wordVal qP r = 1 := Certificates.certificate753505.1

theorem qP_omega : wordVal qP (decodeWord 4 sl3OmegaCodes7) = 1 :=
  Certificates.certificate753505.2.1

theorem qP_zero_ne_one : qP 0 ≠ 1 := Certificates.certificate753505.2.2.1

theorem qP_fix_zero (i : Fin 4) : (qP i : Equiv.Perm (Fin N)) 0 = 0 :=
  Certificates.certificate753505.2.2.2 i

end Checks

section Theta

theorem exists_theta : ∃ θ : SL(3, ZMod 7) →* Pv, ∀ i, θ (sl3Gen (ZMod 7) i) = qP i :=
  sl3_lift7 qP qP_rels

@[expose] noncomputable def theta : SL(3, ZMod 7) →* Pv := exists_theta.choose

theorem theta_sl3Gen (i : Fin 4) : theta (sl3Gen (ZMod 7) i) = qP i := exists_theta.choose_spec i

theorem theta_omega : theta sl3Omega7 = 1 := by
  rw [← wordVal_sl3Omega7, ← wordVal_map theta, show (fun i => theta (sl3Gen (ZMod 7) i)) = qP from
    funext theta_sl3Gen]
  exact qP_omega

theorem theta_ne_one : theta (sl3Gen (ZMod 7) 0) ≠ 1 := by
  rw [theta_sl3Gen]
  exact qP_zero_ne_one

@[expose] noncomputable def Q0 : Subgroup Pv := theta.range

noncomputable def Q0_equiv : projectiveSL 3 (ZMod 7) ≃* Q0 :=
  projectiveSL_mulEquiv_range theta theta_ne_one theta_omega

theorem card_Q0 : Nat.card Q0 = 1876896 := card_range_of_lift theta theta_ne_one theta_omega

theorem Q0_eq_closure : Q0 = Subgroup.closure (Set.range qP) := by
  rw [Q0, range_eq_closure_of_lift, show (fun i => theta (sl3Gen (ZMod 7) i)) = qP from
    funext theta_sl3Gen]

theorem Q0_le_stab : ∀ g ∈ Q0, (g : Equiv.Perm (Fin N)) 0 = 0 := by
  intro g hg
  rw [Q0_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact qP_fix_zero i
  | one => rfl
  | mul x y _ _ hx hy =>
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx =>
    rw [Subgroup.coe_inv, Equiv.Perm.inv_def]
    nth_rw 1 [← hx]
    exact Equiv.symm_apply_apply _ _

end Theta

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
