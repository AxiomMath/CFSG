module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartCoord

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private instance instDecidableIsEvenVec6 (v : Fin 6 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private instance instDecidableIsEvenVec8' (v : Fin 8 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

@[expose] def sec5oPt (i : Fin 6) : Fin 8 :=
  Fin.castLE (by norm_num) i

@[expose] def sec5oGamma (e f : Fin 6) : Equiv.Perm (Fin 8) :=
  Equiv.swap (sec5oPt e) 6 * Equiv.swap (sec5oPt f) 7

@[expose] def sec5oTau (a b e f : Fin 6) : Equiv.Perm (Fin 6) :=
  Equiv.swap a b * Equiv.swap e f

@[expose] def sec5oSigma (a b e f : Fin 6) : Equiv.Perm (Fin 8) :=
  (sec5oGamma e f)⁻¹ * extPerm (sec5oTau a b e f) * sec5oGamma e f

theorem sec5o_gamma_mem_alt {e f : Fin 6} (hef : e ≠ f) :
    sec5oGamma e f ∈ alternatingGroup (Fin 8) := by
  have h1 : sec5oPt e ≠ 6 := fun h => by
    have := congrArg Fin.val h
    simp [sec5oPt] at this
    omega
  have h2 : sec5oPt f ≠ 7 := fun h => by
    have := congrArg Fin.val h
    simp [sec5oPt] at this
    omega
  unfold sec5oGamma
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h1,
    Equiv.Perm.sign_swap h2]
  decide

theorem sec5o_tau_mem_alt {a b e f : Fin 6} (hab : a ≠ b) (hef : e ≠ f) :
    sec5oTau a b e f ∈ alternatingGroup (Fin 6) := by
  unfold sec5oTau
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hef]
  decide

theorem sec5o_gamma_inv {e f : Fin 6} (hef : e ≠ f) :
    (sec5oGamma e f)⁻¹ = sec5oGamma e f := by
  have key : ∀ e f : Fin 6, e ≠ f → (sec5oGamma e f)⁻¹ = sec5oGamma e f := by
    unfold sec5oGamma sec5oPt
    decide +kernel
  exact key e f hef

theorem sec5o_isEvenVec_pair : IsEvenVec (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1 :
    Fin 8 → ZMod 2) := by
  unfold IsEvenVec
  decide +kernel

theorem sec5o_isEvenVec_unit (i : Fin 6) :
    IsEvenVec (Pi.single (sec5oPt i) (1 : ZMod 2) + Pi.single 6 1 : Fin 8 → ZMod 2) := by
  revert i
  unfold sec5oPt
  decide +kernel

theorem sec5o_heartCoord_unit (i : Fin 6) :
    heartCoord (Pi.single (sec5oPt i) (1 : ZMod 2) + Pi.single 6 1) = Pi.single i 1 := by
  revert i
  unfold sec5oPt
  decide +kernel

theorem sec5o_gamma_pair {e f : Fin 6} (hef : e ≠ f) :
    heartCoord (permVec (sec5oGamma e f) (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1)) =
      Pi.single e 1 + Pi.single f 1 := by
  have key : ∀ e f : Fin 6, e ≠ f →
      heartCoord (permVec (sec5oGamma e f) (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1)) =
        Pi.single e 1 + Pi.single f 1 := by
    unfold sec5oGamma sec5oPt
    decide +kernel
  exact key e f hef

theorem sec5o_gamma_ra {e f a : Fin 6} (hef : e ≠ f) (hae : a ≠ e) (haf : a ≠ f) :
    IsEvenVec (heartCoord (permVec (sec5oGamma e f)
      (Pi.single (sec5oPt a) (1 : ZMod 2) + Pi.single 6 1))) := by
  have key : ∀ e f a : Fin 6, e ≠ f → a ≠ e → a ≠ f →
      IsEvenVec (heartCoord (permVec (sec5oGamma e f)
        (Pi.single (sec5oPt a) (1 : ZMod 2) + Pi.single 6 1))) := by
    unfold sec5oGamma sec5oPt
    decide +kernel
  exact key e f a hef hae haf

set_option synthInstance.maxSize 2048 in
theorem sec5o_sigma_t {a b e f : Fin 6} (hab : a ≠ b) (hef : e ≠ f) (hae : a ≠ e) (haf : a ≠ f)
    (hbe : b ≠ e) (hbf : b ≠ f) :
    permVec (sec5oSigma a b e f) (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1) =
      Pi.single 6 1 + Pi.single 7 1 := by
  have key : ∀ a b e f : Fin 6, a ≠ b → e ≠ f → a ≠ e → a ≠ f → b ≠ e → b ≠ f →
      permVec (sec5oSigma a b e f) (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1) =
        Pi.single 6 1 + Pi.single 7 1 := by
    unfold sec5oSigma sec5oGamma sec5oTau sec5oPt
    decide +kernel
  exact key a b e f hab hef hae haf hbe hbf

set_option synthInstance.maxSize 2048 in
theorem sec5o_sigma_frame {a b e f : Fin 6} (hab : a ≠ b) (hef : e ≠ f) (hae : a ≠ e)
    (haf : a ≠ f) (hbe : b ≠ e) (hbf : b ≠ f) (i : Fin 6) :
    heartCoord (permVec (sec5oSigma a b e f)
      (Pi.single (sec5oPt i) (1 : ZMod 2) + Pi.single 6 1)) =
      1 + Pi.single (Equiv.swap a b i) 1 := by
  have key : ∀ a b e f i : Fin 6, a ≠ b → e ≠ f → a ≠ e → a ≠ f → b ≠ e → b ≠ f →
      heartCoord (permVec (sec5oSigma a b e f)
        (Pi.single (sec5oPt i) (1 : ZMod 2) + Pi.single 6 1)) =
        1 + Pi.single (Equiv.swap a b i) 1 := by
    unfold sec5oSigma sec5oGamma sec5oTau sec5oPt
    decide +kernel
  exact key a b e f i hab hef hae haf hbe hbf

theorem sec5o_exists_efab {v : Fin 6 → ZMod 2} (hv : vecWeight v = 4) :
    ∃ e f a b : Fin 6, e ≠ f ∧ a ≠ b ∧ a ≠ e ∧ a ≠ f ∧ b ≠ e ∧ b ≠ f ∧
      1 + v = Pi.single e 1 + Pi.single f 1 := by
  revert v
  unfold vecWeight
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
