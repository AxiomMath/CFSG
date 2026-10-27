module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCHeFus
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCEndFacts

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {X : Type} [Group X] [Finite X]

theorem Config.diagonal_fusion
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    {b y : X} {M : Subgroup X} (hb : orderOf b = 2) (hbK : b ∈ coreActionKernel J)
    (hab : a * b = b * a) (hUM : GSUnbalancingTriple b y M) (hMa : conjugate M a ≠ M)
    (hTM : gsFixedLayer J b ≤ M ⊔ conjugate M a)
    (h7 : Nonempty (M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin 7))) {z : X}
    (hzJ : z ∈ J) (hz2 : orderOf z = 2) (hzb : z * b = b * z) :
    ∃ g : X, g * a * g⁻¹ = a * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hMb, hMc, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  have ha := h.orderOf_eq
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hza : z * a = a * z := mem_centralizer_singleton_iff.mp (h.le_centralizer hzJ)
  have ht2 : a * z * (a * z) = 1 := by
    calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [hza]
      _ = a * a * (z * z) := by group
      _ = 1 := by rw [haa, hzz, one_mul]
  set C := centralizer ({b} : Set X) with hC
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr hab
  set M' := conjugate M a with hM'
  have hmemM' : ∀ x, x ∈ M' ↔ a * x * a ∈ M := fun x => by rw [hM', mem_conjugate_iff, hainv]
  have hM'C : M' ≤ C := fun x hx => by
    have h2 := mul_mem (mul_mem haC (hMb ((hmemM' x).mp hx))) haC
    rwa [show a * (a * x * a) * a = (a * a) * x * (a * a) by group, haa, one_mul,
      mul_one] at h2
  have hM'c : IsPComponent 2 (M'.subgroupOf C) := by
    have h1 := isPComponent_conjugate hMc (⟨a, haC⟩ : ↥C)
    rwa [conjugate_subgroupOf_eq] at h1
  have hne : M ≠ M' := fun he => hMa he.symm
  have hM'K : M' ≤ coreActionKernel M :=
    le_coreActionKernel_of_component_ne hMb hM'C hMc hM'c hne
  have hMK : M ≤ coreActionKernel M' :=
    le_coreActionKernel_of_component_ne hM'C hMb hM'c hMc hne.symm
  have hMN' : M ≤ normalizer (M' : Set X) := fun x hx => (mem_coreActionKernel.mp (hMK hx)).1
  have hM'N : M' ≤ normalizer (M : Set X) := fun x hx => (mem_coreActionKernel.mp (hM'K hx)).1
  obtain ⟨e7⟩ := alternating_equiv_of_unbalancing hTB hSA hnonab hK hz hU hUM h7
  have hZM : center (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ :=
    center_eq_bot_of_equiv e7 (alternatingGroup.center_eq_bot (by simp))
  have hZM' : center (↥M' ⧸ pPrimeCore 2 ↥M') = ⊥ := by
    let φ : X ≃* X := MulAut.conj a⁻¹
    have hφ : M.map φ.toMonoidHom = M' := rfl
    let eM : ↥M ≃* ↥M' := (M.equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hφ)
    exact center_eq_bot_of_equiv
      ((QuotientGroup.congr _ _ eM.symm (pPrimeCore_map_iso 2 eM.symm)).trans e7)
      (alternatingGroup.center_eq_bot (by simp))
  have hzMM : z ∈ M ⊔ M' := hTM (h.mem_gsFixedLayer hb hbK hzJ hz2 hzb)
  have hzMM' : z ∈ ((M ⊔ M' : Subgroup X) : Set X) := hzMM
  rw [coe_mul_of_left_le_normalizer_right M M' hMN'] at hzMM'
  obtain ⟨m₁, hm₁, m₂, hm₂, hz12⟩ := hzMM'
  replace hz12 : m₁ * m₂ = z := hz12
  have hKM : M ⊔ M' ≤ normalizer (M : Set X) := sup_le Subgroup.le_normalizer hM'N
  have hKM' : M ⊔ M' ≤ normalizer (M' : Set X) := sup_le hMN' Subgroup.le_normalizer
  set ρ₁ := (oddQuotConj M).comp (inclusion hKM) with hρ₁
  set ρ₂ := (oddQuotConj M').comp (inclusion hKM') with hρ₂
  have hρ₁M' : ∀ x (hx : x ∈ M'), ρ₁ ⟨x, mem_sup_right hx⟩ = 1 := fun x hx =>
    (oddQuotConj_eq_one_iff (inclusion hKM ⟨x, mem_sup_right hx⟩)).mpr (hM'K hx)
  have hρ₂M : ∀ x (hx : x ∈ M), ρ₂ ⟨x, mem_sup_left hx⟩ = 1 := fun x hx =>
    (oddQuotConj_eq_one_iff (inclusion hKM' ⟨x, mem_sup_left hx⟩)).mpr (hMK hx)
  have hu₁ : a * m₁ * a ∈ M' := (hmemM' _).mpr (by
    rw [show a * (a * m₁ * a) * a = (a * a) * m₁ * (a * a) by group, haa, one_mul, mul_one]
    exact hm₁)
  have hu₂ : a * m₂ * a ∈ M := (hmemM' m₂).mp hm₂
  have hzu : z = a * m₁ * a * (a * m₂ * a) := by
    calc z = a * (z * a) := by rw [← mul_assoc, ← hza, mul_assoc, haa, mul_one]
      _ = a * (m₁ * m₂) * a := by rw [hz12]; group
      _ = a * m₁ * (a * a) * m₂ * a := by rw [haa]; group
      _ = a * m₁ * a * (a * m₂ * a) := by group
  have hx₁ : a * m₁⁻¹ * a ∈ M' := by
    have h1 := inv_mem hu₁
    rwa [show (a * m₁ * a)⁻¹ = a⁻¹ * m₁⁻¹ * a⁻¹ by group, hainv] at h1
  set zK : ↥(M ⊔ M') := ⟨z, hzMM⟩ with hzK
  set m₁K : ↥(M ⊔ M') := ⟨m₁, mem_sup_left hm₁⟩ with hm₁K
  set m₂K : ↥(M ⊔ M') := ⟨m₂, mem_sup_right hm₂⟩ with hm₂K
  set u₁K : ↥(M ⊔ M') := ⟨a * m₁ * a, mem_sup_right hu₁⟩ with hu₁K
  set u₂K : ↥(M ⊔ M') := ⟨a * m₂ * a, mem_sup_left hu₂⟩ with hu₂K
  set x₁K : ↥(M ⊔ M') := ⟨a * m₁⁻¹ * a, mem_sup_right hx₁⟩ with hx₁K
  have hz12K : zK = m₁K * m₂K := Subtype.ext hz12.symm
  have hzuK : zK = u₁K * u₂K := Subtype.ext hzu
  have hx₁u : x₁K = u₁K⁻¹ := Subtype.ext (by
    show a * m₁⁻¹ * a = (a * m₁ * a)⁻¹
    rw [show (a * m₁ * a)⁻¹ = a⁻¹ * m₁⁻¹ * a⁻¹ by group, hainv])
  have hzzK : zK * zK = 1 := Subtype.ext hzz
  set wK := m₁K * x₁K * zK with hwK
  have hw : ((wK : ↥(M ⊔ M')) : X) = m₁ * a * m₁⁻¹ * (a * z)⁻¹ := by
    show m₁ * (a * m₁⁻¹ * a) * z = m₁ * a * m₁⁻¹ * (a * z)⁻¹
    rw [inv_eq_of_mul_eq_one_right ht2]
    group
  have hρ₁w : ρ₁ wK = 1 := by
    have h1 : ρ₁ zK = ρ₁ m₁K := by rw [hz12K, map_mul, hρ₁M' m₂ hm₂, mul_one]
    rw [hwK, map_mul, map_mul, hρ₁M' _ hx₁, mul_one, ← h1, ← map_mul, hzzK, map_one]
  have hρ₂w : ρ₂ wK = 1 := by
    have h1 : ρ₂ zK = ρ₂ u₁K := by rw [hzuK, map_mul, hρ₂M _ hu₂, mul_one]
    rw [hwK, map_mul, map_mul, hρ₂M m₁ hm₁, one_mul, h1, hx₁u, map_inv, inv_mul_cancel]
  have hwS : ((wK : ↥(M ⊔ M')) : X) ∈ ((M ⊔ M' : Subgroup X) : Set X) := wK.2
  rw [coe_mul_of_left_le_normalizer_right M M' hMN'] at hwS
  obtain ⟨x, hx, y', hy', hxy⟩ := hwS
  replace hxy : x * y' = ((wK : ↥(M ⊔ M')) : X) := hxy
  have hxyK : wK = ⟨x, mem_sup_left hx⟩ * ⟨y', mem_sup_right hy'⟩ := Subtype.ext hxy.symm
  have hxO : x ∈ (pPrimeCore 2 ↥M).map M.subtype := by
    refine mem_oddIn_of_oddQuotConj_eq_one hZM hx ?_
    have h1 := hρ₁w
    rw [hxyK, map_mul, hρ₁M' y' hy', mul_one] at h1
    exact h1
  have hyO : y' ∈ (pPrimeCore 2 ↥M').map M'.subtype := by
    refine mem_oddIn_of_oddQuotConj_eq_one hZM' hy' ?_
    have h1 := hρ₂w
    rw [hxyK, map_mul, hρ₂M x hx, one_mul] at h1
    exact h1
  have hOM := UnbalancedCorr.map_pPrimeCore_eq_inf_of_subgroupOf hMb hMc.choose_spec.2.1
  have hOM' := UnbalancedCorr.map_pPrimeCore_eq_inf_of_subgroupOf hM'C hM'c.choose_spec.2.1
  rw [hOM] at hxO
  rw [hOM'] at hyO
  have hwO : ((wK : ↥(M ⊔ M')) : X) ∈ (pPrimeCore 2 ↥C).map C.subtype := by
    rw [← hxy]
    exact mul_mem (mem_inf.mp hxO).2 (mem_inf.mp hyO).2
  have hwodd : Odd (orderOf ((wK : ↥(M ⊔ M')) : X)) := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hwO
    rw [card_map_of_injective C.subtype_injective] at h1
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
  exact exists_conj_of_odd_mul (g := m₁) haa ht2 (by rw [hw]; group) hwodd

end CFSG.ComponentClassification.GSThmB.CorC
