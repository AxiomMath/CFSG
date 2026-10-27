module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4S9
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSplitCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOddClosure

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cat81

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup AutL2Facts

theorem cent2Nilp_body : ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p (2 * f) → ∀ y₀ : Y, orderOf y₀ = 2 →
      HasNormalPComplement 2 ↥(centralizer ({MulAut.conj y₀} : Set (MulAut Y))) := by
  intro Y _ _ p f hp hp2 hf hY y₀ hy₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hodd := isOddPrimePower_of hp hp2 (by omega : 1 ≤ 2 * f) hF
  have hsq := isSquare_neg_one_of_card_sq hp hp2 hF
  obtain ⟨φ⟩ := nonempty_stabilizer_equiv e hodd hsq y₀ hy₀
  have h2 := two_ne_zero_of_isOddPrimePower hodd
  have hneg : (-1 : Fˣ) ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun u : Fˣ => (u : F)) h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  set C := centralizer ({MulAut.conj y₀} : Set (MulAut Y)) with hC
  have heq : C = MulAction.stabilizer (MulAut Y) y₀ := by
    ext α
    rw [hC, mem_centralizer_conj_iff e, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  have hodd_mul : ∀ x ∈ C, ∀ y ∈ C, Odd (orderOf x) → Odd (orderOf y) →
      Odd (orderOf (x * y)) := by
    intro x hx y hy hxo hyo
    rw [heq] at hx hy
    set x' := φ ⟨x, hx⟩ with hx'
    set y' := φ ⟨y, hy⟩ with hy'
    have hcx := mem_centralizer_singleton_iff.mp x'.2
    have hcy := mem_centralizer_singleton_iff.mp y'.2
    have hx'o : Odd (orderOf (x' : PGammaL2 F)) := by
      rw [Subgroup.orderOf_coe, hx', MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hxo
    have hy'o : Odd (orderOf (y' : PGammaL2 F)) := by
      rw [Subgroup.orderOf_coe, hy', MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hyo
    have h3 := odd_mul_of_commute_z hneg hcx hcy hx'o hy'o
    have e3 : (x' : PGammaL2 F) * y' = (φ (⟨x, hx⟩ * ⟨y, hy⟩) : PGammaL2 F) := by
      rw [map_mul, Subgroup.coe_mul]
    rw [e3, Subgroup.orderOf_coe, MulEquiv.orderOf_eq] at h3
    have e4 : orderOf (⟨x, hx⟩ * ⟨y, hy⟩ : MulAction.stabilizer (MulAut Y) y₀) =
        orderOf (x * y) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rwa [e4] at h3
  exact ⟨pPrimeCore 2 ↥C, inferInstance, pPrimeCore_coprime_card,
    isPGroup_quotient_pPrimeCore_of_odd_mul C hodd_mul⟩

end Cat81

end CFSG.ComponentClassification.CatFactsL4U4
