module

public import Certificates.Data.Kernel.Misc.Perm23340
public import Mathlib.GroupTheory.Perm.Sign
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.C23340

open Equiv CFSG.KC.LQT

theorem chk23340_sound (h : chk23340 = true) :
    ∀ σ u : Perm (Fin 6), σ * σ = 1 → Perm.sign u = 1 → u ≠ 1 →
      u * σ = σ * u → u ^ 45 = 1 → ∃ c : Perm (Fin 6), Perm.sign c = 1 ∧
        c * σ = σ * c ∧ (u⁻¹ * c * u * c⁻¹) ^ 45 ≠ 1 := by
  intro σ u hσ hu h1 hc h45
  have hn : (6 : ℕ) ≤ 32 := by norm_num
  have hs := (P.allP_iff (n := 6) _).1 h σ
  simp only [wit, p45, P.allC_iff hn, P.anyC_iff hn, P.impB_iff, P.notB_iff, P.andB_iff,
    P.even_code hn, P.code_one, P.code_pow hn, P.code_inv hn, P.code_mul hn, P.beq_iff,
    P.code_eq_iff hn] at hs
  obtain ⟨c, hcσ, hc1, hc2⟩ := hs hσ u hc hu h1 h45
  exact ⟨c, hc1, hcσ, hc2⟩

end CFSG.KC.Misc.C23340

end
