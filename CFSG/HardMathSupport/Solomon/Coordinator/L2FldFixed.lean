module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixedIso
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (StatedProj StatedSL)
open CFSG.RankThree.PartTwo.Sec4
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

theorem l2FieldFixed_holds : L2FieldFixed := by
  intro F _ _ β hβ3 hβ1 σ φ γ hφ hβ
  have hφ3 : φ ^ 3 = 1 := by
    have h : γ⁻¹ * β ^ 3 * γ = φ ^ 3 := by rw [hβ, conj_pow]; group
    rw [← h, hβ3]; group
  have hφ1 : φ ≠ 1 := by
    intro h
    apply hβ1
    rw [hβ, h]; group
  have hσ3 := l2fld_sigma_pow_three hφ hφ3
  have hσ1 := l2fld_sigma_ne_one hφ hφ1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨p, f, hK⟩ := exists_piField_true F
  obtain ⟨d⟩ := exists_frobData hK hσ
  obtain ⟨ψ⟩ := l2fld_fixSub_entrywise_iso hσ3 d.K₀ d.hKσ hφ
  have hcard : Nat.card F = Nat.card ↥d.K₀ ^ 3 := by
    have h1 := hK.card
    have h2 := d.hP.card
    rw [piCard, Bool.cond_true] at h1 h2
    rw [h1, h2]
    exact d.pow_eq
  have hfix : fixSub β = (fixSub φ).map γ.toMonoidHom := by
    have := fixSub_congr γ φ
    rw [hβ]
    exact this
  let ψ'' : ↥(fixSub φ) ≃* ↥(fixSub β) :=
    ((fixSub φ).equivMapOfInjective γ.toMonoidHom γ.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  let ψ' : ↥(fixSub β) ≃* ↥(fixSub φ) := ψ''.symm
  exact ⟨↥d.K₀, inferInstance, inferInstance, hcard, ⟨ψ'.trans ψ.symm⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator
