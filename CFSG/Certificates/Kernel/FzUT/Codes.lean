module

public import Certificates.Data.Kernel.FzUT.Codes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Ev

public section

namespace CFSG.KC.FzUT

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.FritzII
open scoped commutatorElement

@[expose] def enc4 (a : F4c) : Nat := a.a.val + 2 * a.b.val

@[expose] def enc (x : FzUT) : Nat := enc4 x.a + 4 * enc4 x.b + 16 * enc4 x.c

@[expose] def dec4 (n : Nat) : F4c := ⟨((n &&& 1 : Nat) : ZMod 2), (((n >>> 1) &&& 1 : Nat) : ZMod 2)⟩

@[expose] def dec (n : Nat) : FzUT := ⟨dec4 (n &&& 3), dec4 ((n >>> 2) &&& 3), dec4 ((n >>> 4) &&& 3)⟩

theorem enc_lt : ∀ x : FzUT, enc x < 64 := by decide +kernel

theorem dec_enc : ∀ x : FzUT, dec (enc x) = x := by decide +kernel

theorem enc_dec : ∀ n : Fin 64, enc (dec n) = n := by decide +kernel

theorem enc_injective : Function.Injective enc := fun x y h => by
  rw [← dec_enc x, h, dec_enc]

theorem enc_one : enc 1 = 0 := by decide +kernel

theorem f4mulP_eq : ∀ a b : F4c, f4mulP (enc4 a) (enc4 b) = enc4 (a * b) := by decide +kernel

theorem pmulP_eq : ∀ x y : FzUT, pmulP (enc x) (enc y) = enc (x * y) := by decide +kernel

theorem pwP_eq : ∀ (e : ZMod 2) (g : FzUT), pwP e.val (enc g) = enc (fzPw e g) := by
  decide +kernel

theorem commP_eq : ∀ g h : FzUT, commP (enc g) (enc h) = enc ⁅g, h⁆ := by decide +kernel

theorem evN_bits : ∀ x : FzUT, (enc x &&& 1) = x.a.a.val ∧ ((enc x >>> 1) &&& 1) = x.a.b.val ∧
    ((enc x >>> 2) &&& 1) = x.b.a.val ∧ ((enc x >>> 3) &&& 1) = x.b.b.val ∧
    (((enc x >>> 4) ^^^ f4mulP (enc x &&& 3) ((enc x >>> 2) &&& 3)) &&& 1) =
      (x.c + x.a * x.b).a.val ∧
    ((((enc x >>> 4) ^^^ f4mulP (enc x &&& 3) ((enc x >>> 2) &&& 3)) >>> 1) &&& 1) =
      (x.c + x.a * x.b).b.val := by
  decide +kernel

theorem evN_eq (d : FzAutD) (x : FzUT) :
    evN (enc d.g1) (enc d.g2) (enc d.g3) (enc d.g4) (enc x) = enc (fzEv d x) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := evN_bits x
  simp only [evN, fzEv, h1, h2, h3, h4, h5, h6, pwP_eq, commP_eq, pmulP_eq]

theorem hom_evN (σ : FzUT →* FzUT) (x : FzUT) :
    enc (σ x) = evN (enc (σ fzE1)) (enc (σ fzEW)) (enc (σ fzF1)) (enc (σ fzFW)) (enc x) := by
  rw [fzUT_hom_apply σ x]
  exact (evN_eq ⟨σ fzE1, σ fzEW, σ fzF1, σ fzFW⟩ x).symm

end CFSG.KC.FzUT
