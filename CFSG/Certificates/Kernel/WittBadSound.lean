module

public import Certificates.Data.Kernel.WittBad
public import CFSG.Certificates.Kernel.WittCntSound

public section

namespace CFSG.KC.WCnt

open CFSG.KS.PCnt

theorem badT_pkw_iff (τ : Equiv.Perm (Fin 22)) (e v₀ v₁ : Fin 22 → Fin 22) {k : Nat}
    (p : Fin k → Fin 22 → Fin 22) (E V₀ V₁ : Nat) (Vs : List Nat) (hlen : Vs.length = k)
    (hE : ∀ i : Fin 22, pt E i.val = (e i).val) (h₀ : ∀ i : Fin 22, pt V₀ i.val = (v₀ i).val)
    (h₁ : ∀ i : Fin 22, pt V₁ i.val = (v₁ i).val)
    (hP : ∀ j : Fin k, ∀ i : Fin 22, pt (Vs.getD j.val 0) i.val = (p j i).val) :
    badT E V₀ V₁ Vs (pkw 5 τ) = true ↔ (∀ x, τ (e x) = e (τ x)) ∧
      ¬((∃ j : Fin k, ∀ x, τ (v₀ x) = p j (τ x)) ∧ ∃ j : Fin k, ∀ x, τ (v₁ x) = p j (τ x)) := by
  have e1 := relT_pkw τ e e E E hE hE
  have e2 := relAny_pkw_iff τ v₀ V₀ h₀ p Vs hlen hP
  have e3 := relAny_pkw_iff τ v₁ V₁ h₁ p Vs hlen hP
  rw [badT, e1]
  cases h2 : relAny V₀ Vs (pkw 5 τ) <;> cases h3 : relAny V₁ Vs (pkw 5 τ) <;>
    rw [h2] at e2 <;> rw [h3] at e3 <;> by_cases hc : ∀ x, τ (e x) = e (τ x) <;> simp_all

end CFSG.KC.WCnt

end
