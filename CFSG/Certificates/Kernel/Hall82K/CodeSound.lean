module

public import CFSG.Certificates.Kernel.Hall82K.EnumSound
public import Certificates.Data.Kernel.Hall82K.Rm

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.KC.Misc.Clos CFSG.KC.LQT

theorem code_inj {g h : Equiv.Perm (Fin 64)} (hg : g ∈ addSub) (hh : h ∈ addSub)
    (he : codeL g = codeL h) : g = h :=
  congrArg Subtype.val (closEnc.inj (a₁ := ⟨g, hg⟩) (a₂ := ⟨h, hh⟩) he)

theorem codeL_mul {g h : Equiv.Perm (Fin 64)} (hg : g ∈ addSub) (hh : h ∈ addSub) :
    codeL ⇑(g * h) = compL (codeL g) (codeL h) :=
  closEnc.enc_mul ⟨g, hg⟩ ⟨h, hh⟩

theorem codeL_one : codeL ⇑(1 : Equiv.Perm (Fin 64)) = idK := rfl

theorem codeL_pow {g : Equiv.Perm (Fin 64)} (hg : g ∈ addSub) :
    ∀ n, codeL ⇑(g ^ n) = powL (codeL g) n
  | 0 => by
    rw [pow_zero, codeL_one]
    rfl
  | n + 1 => by
    rw [pow_succ, codeL_mul (addSub.pow_mem hg n) hg, codeL_pow hg n]
    rfl

theorem apL_code {g : Equiv.Perm (Fin 64)} (hg : g ∈ addSub) (v : Fin 64) :
    (g v).val = apL (codeL g) v.val :=
  (apL_codeL (mem_addSub.1 hg) v).symm

theorem orB_eq_true82 {a b : Bool} (h : CFSG.KC.Ord.orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem negK_eq_true {b : Bool} (h : negK b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

end CFSG.KC.Hall82K
