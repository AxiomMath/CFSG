module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11True
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11GlueConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIITrue

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def pY0 : ↥P1408 := ⟨elemW y0Word, elemW_mem _⟩

@[expose] noncomputable def pN1 : ↥P1408 := ⟨elemW n1Word, elemW_mem _⟩

@[expose] noncomputable def pRho0 : ↥P1408 := ⟨elemW rho0Word, elemW_mem _⟩

@[expose] noncomputable def m11M : Subgroup ↥P1408 := m11K.subgroupOf P1408

theorem coe_pY0 : (pY0 : Equiv.Perm (Fin 1408)) = elemW y0Word := rfl

theorem coe_pN1 : (pN1 : Equiv.Perm (Fin 1408)) = elemW n1Word := rfl

theorem coe_pRho0 : (pRho0 : Equiv.Perm (Fin 1408)) = elemW rho0Word := rfl

theorem pY0_mem : pY0 ∈ m11M := Subgroup.mem_subgroupOf.2 elemW_y0_mem

theorem factorization_card_P1408_eleven : (177408000 : ℕ).factorization 11 = 1 := by
  rw [show (177408000 : ℕ) = 11 * 16128000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_eleven,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Cert


theorem isM11Like_m11M : TwoHSData.IsM11Like ↥m11M :=
  isM11Like_m11K.of_mulEquiv (Subgroup.subgroupOfEquivOfLe m11K_le_P1408).symm

theorem orderOf_pY0 : orderOf pY0 = 11 := by
  change orderOf (⟨elemW y0Word, elemW_mem _⟩ : ↥P1408) = 11
  rw [Subgroup.orderOf_mk]
  exact orderOf_y0


theorem exists_conj_eq_m11M (hP : Nat.card ↥P1408 = 177408000) {E_P : Subgroup ↥P1408}
    (hEn : E_P.Normal) (hEi : E_P.index = 2)
    (hE : ∀ x : ↥P1408, x ∈ E_P ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408)
    (M : Subgroup ↥P1408) (hM : TwoHSData.IsM11Like ↥M) :
    ∃ g : ↥P1408, M = m11M.map (MulAut.conj g).toMonoidHom := by
  haveI := hEn
  obtain ⟨-, -, -, -, -, -, -, -, hBn, hZ₁n⟩ := twoHSBasic_spec
  obtain ⟨hconj, hz, haz⟩ := m11_classes hP
  have hn1 : pN1 * pY0 * pN1⁻¹ ∈ zpowers pY0 := by
    have : pN1 * pY0 * pN1⁻¹ = pY0 ^ 7 := Subtype.ext (by simpa [coe_pN1, coe_pY0] using hconj)
    rw [this]
    exact pow_mem (mem_zpowers pY0) 7
  have hsyl : ∀ t : ↥P1408, orderOf t = 11 → ∃ x : ↥P1408, x⁻¹ * t * x ∈ zpowers pY0 := by
    intro t ht
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    haveI : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
    have hS : Nat.card (zpowers pY0) = 11 ^ (Nat.card (⊤ : Subgroup ↥P1408)).factorization 11 := by
      rw [Nat.card_zpowers, orderOf_pY0, Subgroup.card_top, hP, factorization_card_P1408_eleven,
        pow_one]
    obtain ⟨x, -, hx⟩ := TwoHSData.exists_conj_mem_of_orderOf_eq_prime (M := ↥P1408) (p := 11)
      (R := ⊤) (S := zpowers pY0) le_top hS trivial ht
    exact ⟨x, hx⟩
  have hj : ∀ j : ↥P1408, (IsConj pZ j ∨ IsConj (pA * pZ) j) →
      j ∈ m11M ∨ pN1 * j * pN1⁻¹ ∈ m11M ∨
        ∃ w ∈ closure ({pY0, j} : Set ↥P1408), ¬ TwoHSData.M11Order (orderOf w) := by
    intro j hj
    have hprop : m11Prop (j : Equiv.Perm (Fin 1408)) := by
      rcases hj with hj | hj
      · exact hz _ ((isConj_subtype_iff P1408 elemZ_mem j.2).1 hj)
      · exact haz _ ((isConj_subtype_iff P1408 (P1408.mul_mem elemA_mem elemZ_mem) j.2).1 hj)
    rcases hprop with ⟨p, -, hord⟩ | hmem | hmem
    · refine Or.inr (Or.inr ⟨probeG pY0 j p, probeG_mem_closure _ _ _, ?_⟩)
      have := Subgroup.orderOf_coe (probeG pY0 j p)
      rw [← this, coe_probeG]
      exact hord
    · exact Or.inl (Subgroup.mem_subgroupOf.2 hmem)
    · exact Or.inr (Or.inl (Subgroup.mem_subgroupOf.2 hmem))
  exact TwoHSData.exists_conj_eq_of_isM11Like hEn isM11Like_m11M orderOf_pY0 pY0_mem hn1 hsyl
    (fun t ht => mem_of_orderOf_eleven hEi ht)
    (fun h => hBn ((hE pB).1 h)) (fun h => hZ₁n ((hE pZ₁).1 h))
    (fun g => Subtype.ext (elemA_comm g.2)) (involution_cover_inv hP) hj M hM

theorem m11_unique_class_P (hP : Nat.card ↥P1408 = 177408000)
    {E_P : Subgroup ↥P1408} (hEn : E_P.Normal) (hEi : E_P.index = 2)
    (hE : ∀ x : ↥P1408, x ∈ E_P ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) :
    (∃ M : Subgroup ↥P1408, IsSporadic ↥M .M11) ∧
      ∀ M M' : Subgroup ↥P1408, IsSporadic ↥M .M11 → IsSporadic ↥M' .M11 →
        ∃ g : ↥P1408, M' = M.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨e⟩ := nonempty_mulEquiv_m11K
  have hNat : TwoHSData.IsM11Like (Carrier .M11) := isM11Like_m11K.of_mulEquiv e
  have hlike : ∀ M : Subgroup ↥P1408, IsSporadic ↥M .M11 → TwoHSData.IsM11Like ↥M := by
    intro M hM
    obtain ⟨f⟩ := hM
    exact hNat.of_mulEquiv f.symm
  refine ⟨⟨m11M, ⟨(Subgroup.subgroupOfEquivOfLe m11K_le_P1408).trans e⟩⟩, ?_⟩
  intro M M' hM hM'
  exact TwoHSData.exists_conj_of_conj (exists_conj_eq_m11M hP hEn hEi hE M (hlike M hM))
    (exists_conj_eq_m11M hP hEn hEi hE M' (hlike M' hM'))


theorem m11_centralizer_five_P (hP : Nat.card ↥P1408 = 177408000)
    {E_P : Subgroup ↥P1408} (hEn : E_P.Normal) (hEi : E_P.index = 2)
    (hE : ∀ x : ↥P1408, x ∈ E_P ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408)
    (M : Subgroup ↥P1408) (hM : IsSporadic ↥M .M11) (ρ : ↥P1408) (hρM : ρ ∈ M)
    (hρ : orderOf ρ = 5) : IsShapeCentralizerFiveB ↥(centralizer ({ρ} : Set ↥P1408)) := by
  haveI : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  obtain ⟨e⟩ := nonempty_mulEquiv_m11K
  have hNat : TwoHSData.IsM11Like (Carrier .M11) := isM11Like_m11K.of_mulEquiv e
  obtain ⟨f⟩ := hM
  obtain ⟨g, rfl⟩ := exists_conj_eq_m11M hP hEn hEi hE M (hNat.of_mulEquiv f.symm)
  obtain ⟨ρ₁, hρ₁, rfl⟩ := Subgroup.mem_map.1 hρM
  have hρ₁5 : orderOf ρ₁ = 5 := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj g) ρ₁]
    exact hρ
  obtain ⟨h5, hρ0K, hck, hcB⟩ := m11_five
  have hρ0 : orderOf pRho0 = 5 := by
    change orderOf (⟨elemW rho0Word, elemW_mem _⟩ : ↥P1408) = 5
    rw [Subgroup.orderOf_mk]
    exact h5
  have hρ0M : pRho0 ∈ m11M := Subgroup.mem_subgroupOf.2 hρ0K
  have hck' : ∀ k : ℕ, 0 < k → k < 5 → ∃ c ∈ m11M, c * pRho0 * c⁻¹ = pRho0 ^ k := by
    intro k hk0 hk5
    obtain ⟨c, hcK, hc⟩ := hck k hk0 hk5
    refine ⟨⟨c, m11K_le_P1408 hcK⟩, Subgroup.mem_subgroupOf.2 hcK, Subtype.ext ?_⟩
    simpa [coe_pRho0] using hc
  have h01 : IsConj pRho0 ρ₁ :=
    TwoHSData.isConj_of_orderOf_five isM11Like_m11M hρ0M hρ0 hck' hρ₁ hρ₁5
  have h0B : IsConj pRho0 (repP fix5B) :=
    isConj_iff.2 ⟨⟨elemW cBWord, elemW_mem _⟩, Subtype.ext hcB⟩
  have h1ρ : IsConj ρ₁ ((MulAut.conj g).toMonoidHom ρ₁) :=
    isConj_iff.2 ⟨g, by simp [MulAut.conj_apply]⟩
  obtain ⟨eC⟩ := nonempty_centralizer_mulEquiv_of_isConj (h0B.symm.trans (h01.trans h1ρ))
  exact IsShapeCentralizerFiveB.of_mulEquiv eC (isShape_repP_five_B hP)

end Cert

end CFSG.EvenSporadicStandard.HNRecog
