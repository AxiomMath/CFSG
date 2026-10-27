module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2Crit
public import CFSG.LocalAnalysis.GLTheoremB.AltAut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.S7 CFSG.Open
  Equiv Equiv.Perm

set_option maxRecDepth 100000 in
theorem A7_centralizer_T_pow_nine :
    ∀ σ : Perm (Fin 7), σ * a = a * σ → σ * b = b * σ → σ ^ 9 = 1 := by
  decide +kernel

theorem A7_central_trivial (D : Subgroup (MulAut ↥Alt7)) (hD : Nat.card D = 9)
    (y : MulAut ↥Alt7) (hy : y ∈ Subgroup.centralizer (D : Set (MulAut ↥Alt7)))
    (hcop : Nat.Coprime 3 (orderOf y)) : y = 1 := by
  set φ : MulAut ↥Alt7 →* S := conjEquiv.symm.toMonoidHom with hφ
  have hφi : Function.Injective φ := conjEquiv.symm.injective
  have hR : Nat.card (D.map φ) = 9 := by
    rw [← hD]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective D φ hφi).toEquiv).symm
  obtain ⟨g, hg⟩ := exists_conj_eq_T hR
  set σ : S := φ y with hσ
  have hcomm : ∀ r ∈ D.map φ, σ * r = r * σ := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_centralizer_iff.1 hy d hd).symm
  have hcT : ∀ t ∈ T, (g⁻¹ * σ * g) * t = t * (g⁻¹ * σ * g) := by
    intro t ht
    have hr : g * t * g⁻¹ ∈ D.map φ := (hg _).2 (by simpa [mul_assoc] using ht)
    have := hcomm _ hr
    calc g⁻¹ * σ * g * t = g⁻¹ * (σ * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * σ) * g := by rw [this]
      _ = t * (g⁻¹ * σ * g) := by group
  have h9 : (g⁻¹ * σ * g) ^ 9 = 1 :=
    A7_centralizer_T_pow_nine _ (hcT a a_mem_T) (hcT b b_mem_T)
  have h9' : σ ^ 9 = 1 := by
    have e : g⁻¹ * σ ^ 9 * g = 1 := by
      have := conj_pow (a := g⁻¹) (b := σ) (i := 9)
      simp only [inv_inv] at this
      rw [← this]
      exact h9
    calc σ ^ 9 = g * (g⁻¹ * σ ^ 9 * g) * g⁻¹ := by group
      _ = 1 := by rw [e]; group
  have hy9 : y ^ 9 = 1 := hφi (by rw [map_pow, map_one]; exact h9')
  have hdvd : orderOf y ∣ 9 := orderOf_dvd_of_pow_eq_one hy9
  have h1 : orderOf y = 1 := by
    have h3 : Nat.Coprime (orderOf y) 3 := hcop.symm
    have : orderOf y ∣ 3 ^ 2 := by simpa using hdvd
    exact (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 h3) this)
  exact orderOf_eq_one_iff.1 h1

theorem isLocallyBalancedAbs_A7 :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs 3 2 (alternatingGroup (Fin 7)) :=
  isLocallyBalancedAbs_three_two_of_central fun D _ hD y hy hcop =>
    A7_central_trivial D hD y hy hcop

end CFSG.HardMathSupport.Solomon.Coordinator
