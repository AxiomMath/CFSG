module

public import CFSG.ClassicalInvolution.Asc77.AscBSD2

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.RouteD (ModelFund psu_model_equiv)
open scoped MatrixGroups

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem map_mem_center (φ : X ≃* Y) {c : X} (hc : c ∈ Subgroup.center X) :
    φ c ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  have h := hc (φ.symm y)
  have h' := congrArg φ h
  simpa using h'

theorem CentralSqOne.of_mulEquiv (φ : X ≃* Y) (h : CentralSqOne Y) : CentralSqOne X := by
  intro c hc hc2
  have h1 : φ c = 1 := h (φ c) (map_mem_center φ hc) (by rw [← map_mul, hc2, map_one])
  exact φ.injective (by rw [h1, map_one])

theorem CentralSqCard.of_mulEquiv (φ : X ≃* Y) (h : CentralSqCard Y) : CentralSqCard X := by
  intro c₁ c₂ h₁ h₂ e₁ e₂
  rcases h (φ c₁) (φ c₂) (map_mem_center φ h₁) (map_mem_center φ h₂)
      (by rw [← map_mul, e₁, map_one]) (by rw [← map_mul, e₂, map_one]) with h | h | h
  · exact Or.inl (φ.injective (by rw [h, map_one]))
  · exact Or.inr (Or.inl (φ.injective (by rw [h, map_one])))
  · exact Or.inr (Or.inr (φ.injective h))

end Transport

section SU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem su_three_centralSqOne (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) :
    CentralSqOne (Su K p f 3) := by
  intro z hz hz2
  rcases eq_one_or_suMat_eq_neg_one hK hq (by norm_num) hz hz2 with h | h
  · exact h
  · exfalso
    have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
    have hdet := det_suMat z
    rw [h] at hdet
    simp [Matrix.det_neg] at hdet
    exact h2 (by linear_combination (-1 : K) * hdet)

theorem su_four_centralSqCard (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    CentralSqCard (Su K p f 4) := by
  intro z₁ z₂ h₁ h₂ e₁ e₂
  rcases eq_one_or_suMat_eq_neg_one hK hq (by norm_num) h₁ e₁ with h | h
  · exact Or.inl h
  rcases eq_one_or_suMat_eq_neg_one hK hq (by norm_num) h₂ e₂ with h' | h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (suMat_injective (h.trans h'.symm)))

theorem longRootSU_eq_of_mem_inv (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    {L L' : Subgroup (Su K p f n)} (hL : L ∈ longRootSetU (K := K) (p := p) (f := f) hn)
    (hL' : L' ∈ longRootSetU (K := K) (p := p) (f := f) hn) {t : Su K p f n} (htL : t ∈ L)
    (htL' : t ∈ L') (ht : orderOf t = 2) : L = L' := by
  obtain ⟨i, hi⟩ := hL
  obtain ⟨i', hi'⟩ := hL'
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have e : t = i := hi.eq_of_orderOf_eq_two hK hp htL ht
  have e' : t = i' := hi'.eq_of_orderOf_eq_two hK hp htL' ht
  rw [hi.eq_longRootGroupSU h2, hi'.eq_longRootGroupSU h2, ← e, ← e']

end SU

section Model

variable {p : ℕ} [Fact p.Prime]


theorem fund_eq_of_mem_inv_psu {n e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p e)
    {R R' : Subgroup (modelUniv .PSU n p e Fact.out).K} (hR : R ∈ ModelFund p .PSU n e)
    (hR' : R' ∈ ModelFund p .PSU n e) {r : (modelUniv .PSU n p e Fact.out).K}
    (hr : IsInvIn R r) (hr' : IsInvIn R' r) : R = R' := by
  have hf : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hord : orderOf (φ r) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by simpa [pow_two] using hr.2.1) hr.2.2
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  exact longRootSU_eq_of_mem_inv hK hp2 ((hφ R).mp hR) ((hφ R').mp hR')
    (Subgroup.mem_map_of_mem _ hr.1) (Subgroup.mem_map_of_mem _ hr'.1) hord

theorem fund_eq_of_central_ratio_psu_three {e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU 3 p e)
    {R R' : Subgroup (modelUniv .PSU 3 p e Fact.out).K} (hR : R ∈ ModelFund p .PSU 3 e)
    (hR' : R' ∈ ModelFund p .PSU 3 e) {r r' : (modelUniv .PSU 3 p e Fact.out).K}
    (hr : IsInvIn R r) (hr' : IsInvIn R' r')
    (hc : r * r'⁻¹ ∈ Subgroup.center (modelUniv .PSU 3 p e Fact.out).K) : R = R' := by
  have hf : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, -⟩ := psu_model_equiv hp2 hadm
  have hZ := CentralSqOne.of_mulEquiv φ (su_three_centralSqOne hK hp2 hq)
  have hrr : r = r' := eq_of_ratio hZ hr.2.1 hr'.2.1 hc
  subst hrr
  exact fund_eq_of_mem_inv_psu hp2 hadm hR hR' hr hr'

theorem fund_two_bound_psu_four {e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU 4 p e)
    {R₁ R₂ R₃ : Subgroup (modelUniv .PSU 4 p e Fact.out).K} (h₁ : R₁ ∈ ModelFund p .PSU 4 e)
    (h₂ : R₂ ∈ ModelFund p .PSU 4 e) (h₃ : R₃ ∈ ModelFund p .PSU 4 e)
    {r₁ r₂ r₃ : (modelUniv .PSU 4 p e Fact.out).K} (hr₁ : IsInvIn R₁ r₁) (hr₂ : IsInvIn R₂ r₂)
    (hr₃ : IsInvIn R₃ r₃)
    (h12 : r₁ * r₂⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    (h23 : r₂ * r₃⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K) :
    R₁ = R₂ ∨ R₂ = R₃ ∨ R₁ = R₃ := by
  have hf : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, -⟩ := psu_model_equiv hp2 hadm
  have hZ := CentralSqCard.of_mulEquiv φ (su_four_centralSqCard hK hq)
  rcases eq_of_three_ratios hZ hr₁.2.1 hr₂.2.1 hr₃.2.1 h12 h23 with h | h | h
  · subst h
    exact Or.inl (fund_eq_of_mem_inv_psu hp2 hadm h₁ h₂ hr₁ hr₂)
  · subst h
    exact Or.inr (Or.inl (fund_eq_of_mem_inv_psu hp2 hadm h₂ h₃ hr₂ hr₃))
  · subst h
    exact Or.inr (Or.inr (fund_eq_of_mem_inv_psu hp2 hadm h₁ h₃ hr₁ hr₃))

end Model

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
