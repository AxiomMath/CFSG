module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812A
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.RankThree.PartOne.K133.Count
import CFSG.RankThree.PartTwo.Sec10.Item10Std
import CFSG.RankThree.PartTwo.Sec18.Transport

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

private theorem isPComponent_conjugate_rank_one {X : Type} [Group X] [Finite X] {p : ℕ}
    {K : Subgroup X} (hK : CFSG.IsPComponent p K) (hrank : CFSG.Open.pRank 3 K = 1)
    (g : X) :
    CFSG.IsPComponent p (CFSG.conjugate K g) ∧
      CFSG.Open.pRank 3 (CFSG.conjugate K g) = 1 := by
  refine ⟨CFSG.ComponentClassification.UnbalancedLayer.isPComponent_conjugate hK g, ?_⟩
  rw [show CFSG.conjugate K g = K.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
    CFSG.RankThreeEvenClassification.Helpers.pRank_map_equiv 3 Nat.prime_three
      (MulAut.conj g⁻¹) K]
  exact hrank

private theorem four_conjugates_pairwise_distinct {X : Type} [Group X]
    {K₁ K₂ : Subgroup X} (hK₁n : K₁.Normal) (hne : K₁ ≠ K₂) {g : X}
    (hgN : g ∉ Subgroup.normalizer (K₂ : Set X)) (hodd : Odd (orderOf g)) :
    K₁ ≠ CFSG.conjugate K₂ g ∧ K₁ ≠ CFSG.conjugate K₂ (g ^ 2) ∧
      K₂ ≠ CFSG.conjugate K₂ g ∧ K₂ ≠ CFSG.conjugate K₂ (g ^ 2) ∧
      CFSG.conjugate K₂ g ≠ CFSG.conjugate K₂ (g ^ 2) := by
  have hconj_one : ∀ H : Subgroup X, CFSG.conjugate H 1 = H := by
    intro H
    ext x
    simp [CFSG.conjugate]
  have hK₁conj (h : X) : CFSG.conjugate K₁ h⁻¹ = K₁ := by
    simpa [CFSG.conjugate] using Subgroup.Normal.map_conj_eq K₁ h
  have hne₂₃ : K₂ ≠ CFSG.conjugate K₂ g := by
    intro h
    apply hgN
    have hinv : g⁻¹ ∈ Subgroup.normalizer (K₂ : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h.symm
    simpa using Subgroup.inv_mem _ hinv
  have hne₂₄ : K₂ ≠ CFSG.conjugate K₂ (g ^ 2) := by
    intro h
    apply hgN
    have hinv : (g ^ 2)⁻¹ ∈ Subgroup.normalizer (K₂ : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h.symm
    have h2N : g ^ 2 ∈ Subgroup.normalizer (K₂ : Set X) := by
      simpa using Subgroup.inv_mem _ hinv
    have hmem : g ∈ Subgroup.zpowers (g ^ 2) := by
      obtain ⟨n, hn⟩ := hodd
      refine Subgroup.mem_zpowers_iff.mpr ⟨((n + 1 : ℕ) : ℤ), ?_⟩
      rw [zpow_natCast]
      have h2 : (g ^ 2) ^ (n + 1) = g ^ (orderOf g + 1) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
    exact Subgroup.zpowers_le.mpr h2N hmem
  have hne₁₃ : K₁ ≠ CFSG.conjugate K₂ g := by
    intro h
    apply hne
    have h' := congrArg (fun H : Subgroup X => CFSG.conjugate H g⁻¹) h
    rwa [hK₁conj g, CFSG.LocalCores.conjugate_conjugate, mul_inv_cancel,
      hconj_one] at h'
  have hne₁₄ : K₁ ≠ CFSG.conjugate K₂ (g ^ 2) := by
    intro h
    apply hne
    have h' := congrArg (fun H : Subgroup X => CFSG.conjugate H ((g ^ 2)⁻¹)) h
    rwa [hK₁conj (g ^ 2), CFSG.LocalCores.conjugate_conjugate, mul_inv_cancel,
      hconj_one] at h'
  have hne₃₄ : CFSG.conjugate K₂ g ≠ CFSG.conjugate K₂ (g ^ 2) := by
    intro h
    apply hne₂₃
    have h' := congrArg (fun H : Subgroup X => CFSG.conjugate H g⁻¹) h
    rw [CFSG.LocalCores.conjugate_conjugate, CFSG.LocalCores.conjugate_conjugate,
      mul_inv_cancel, hconj_one, show g ^ 2 * g⁻¹ = g by group] at h'
    exact h'
  exact ⟨hne₁₃, hne₁₄, hne₂₃, hne₂₄, hne₃₄⟩

private theorem exists_order_three_mem_inf_of_isSylowOf {X : Type} [Group X] [Finite X]
    {K S : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤)
    (hKsub : K.IsSubnormal) (h3K : 3 ∣ Nat.card K) :
    ∃ a ∈ S ⊓ K, orderOf a = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSK : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ K) K :=
    CFSG.RankThree.PartTwo.Sec10.IsSylowOf.inf_of_isSubnormal hS hKsub
  have hcard : Nat.card ↥(S ⊓ K) = 3 ^ (Nat.card K).factorization 3 := hSK.card_eq
  have hpos : 0 < (Nat.card K).factorization 3 :=
    Nat.prime_three.factorization_pos_of_dvd Nat.card_pos.ne' h3K
  have h3 : 3 ∣ Nat.card ↥(S ⊓ K) := by
    rw [hcard]
    exact dvd_pow_self 3 hpos.ne'
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S ⊓ K)) 3 h3
  exact ⟨(a : X), a.2, (Subgroup.orderOf_coe a).trans ha⟩

private theorem le_centModSubgroup_of_isPComponent_ne {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {K L : Subgroup X} (hK : CFSG.IsPComponent p K)
    (hL : CFSG.IsPComponent p L) (hne : K ≠ L) :
    L ≤ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K := by
  have hcore :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p hp K L hK hL).2 hne
  have hLn : L ≤ Subgroup.normalizer (K : Set X) := hcore.1
  have hcomm : ⁅K, L⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype := hcore.2.2.1.trans inf_le_left
  intro l hl
  rw [CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup]
  refine ⟨hLn hl, fun k hk => ?_⟩
  change ⁅k, l⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype
  exact hcomm (Subgroup.commutator_mem_commutator hk hl)

private theorem not_mem_centModSubgroup_of_order_three {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections X) {K : Subgroup X}
    (hK : CFSG.IsPComponent p K) (hrank : CFSG.Open.pRank 3 K = 1)
    {a : X} (ha : a ∈ K) (ha3 : orderOf a = 3) :
    a ∉ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K := by
  have hcore : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K) :=
    not_three_dvd_card_pPrimeCore_of_isPComponent hp hSch hK hrank
  intro hcent
  apply not_forall_commutator_mem_pPrimeCore Nat.prime_three (by norm_num)
    hK hcore hrank ha ha3
  intro b hb
  have h := (CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.mp hcent).2 b hb
  have h' : ⁅b, a⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype := h
  change ⁅a, b⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype
  simpa only [commutatorElement_inv] using Subgroup.inv_mem _ h'

private theorem exists_four_order_three_commuting {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections X)
    {K₁ K₂ K₃ K₄ : Subgroup X}
    (hK₁ : CFSG.IsPComponent p K₁) (hK₂ : CFSG.IsPComponent p K₂)
    (hK₃ : CFSG.IsPComponent p K₃) (hK₄ : CFSG.IsPComponent p K₄)
    (hrank₁ : CFSG.Open.pRank 3 K₁ = 1) (hrank₂ : CFSG.Open.pRank 3 K₂ = 1)
    (hrank₃ : CFSG.Open.pRank 3 K₃ = 1) (hrank₄ : CFSG.Open.pRank 3 K₄ = 1)
    (hne₁₂ : K₁ ≠ K₂) (hne₁₃ : K₁ ≠ K₃) (hne₁₄ : K₁ ≠ K₄)
    (hne₂₃ : K₂ ≠ K₃) (hne₂₄ : K₂ ≠ K₄) (hne₃₄ : K₃ ≠ K₄)
    {S : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤) :
    ∃ a₁ a₂ a₃ a₄ : X,
      a₁ ∈ S ⊓ K₁ ∧ a₂ ∈ S ⊓ K₂ ∧ a₃ ∈ S ⊓ K₃ ∧ a₄ ∈ S ⊓ K₄ ∧
      orderOf a₁ = 3 ∧ orderOf a₂ = 3 ∧ orderOf a₃ = 3 ∧ orderOf a₄ = 3 ∧
      a₁ * a₂ = a₂ * a₁ ∧ a₁ * a₃ = a₃ * a₁ ∧ a₁ * a₄ = a₄ * a₁ ∧
      a₂ * a₃ = a₃ * a₂ ∧ a₂ * a₄ = a₄ * a₂ ∧ a₃ * a₄ = a₄ * a₃ := by
  have hK₁sub : K₁.IsSubnormal := hK₁.choose_spec.2.1
  have hK₂sub : K₂.IsSubnormal := hK₂.choose_spec.2.1
  have hK₃sub : K₃.IsSubnormal := hK₃.choose_spec.2.1
  have hK₄sub : K₄.IsSubnormal := hK₄.choose_spec.2.1
  have hcore₁ : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K₁) :=
    not_three_dvd_card_pPrimeCore_of_isPComponent hp hSch hK₁ hrank₁
  have hcore₂ : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K₂) :=
    not_three_dvd_card_pPrimeCore_of_isPComponent hp hSch hK₂ hrank₂
  have hcore₃ : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K₃) :=
    not_three_dvd_card_pPrimeCore_of_isPComponent hp hSch hK₃ hrank₃
  have h3K₁ : 3 ∣ Nat.card K₁ := by
    refine CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three ?_
    rw [hrank₁]
  have h3K₂ : 3 ∣ Nat.card K₂ := by
    refine CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three ?_
    rw [hrank₂]
  have h3K₃ : 3 ∣ Nat.card K₃ := by
    refine CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three ?_
    rw [hrank₃]
  have h3K₄ : 3 ∣ Nat.card K₄ := by
    refine CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three ?_
    rw [hrank₄]
  obtain ⟨a₁, ha₁, ho₁⟩ := exists_order_three_mem_inf_of_isSylowOf hS hK₁sub h3K₁
  obtain ⟨a₂, ha₂, ho₂⟩ := exists_order_three_mem_inf_of_isSylowOf hS hK₂sub h3K₂
  obtain ⟨a₃, ha₃, ho₃⟩ := exists_order_three_mem_inf_of_isSylowOf hS hK₃sub h3K₃
  obtain ⟨a₄, ha₄, ho₄⟩ := exists_order_three_mem_inf_of_isSylowOf hS hK₄sub h3K₄
  have hc₁₂ : a₁ * a₂ = a₂ * a₁ :=
    commute_of_isPComponent hp Nat.prime_three hK₁ hK₂ hne₁₂ hcore₁ hS.isPGroup ha₁ ha₂
  have hc₁₃ : a₁ * a₃ = a₃ * a₁ :=
    commute_of_isPComponent hp Nat.prime_three hK₁ hK₃ hne₁₃ hcore₁ hS.isPGroup ha₁ ha₃
  have hc₁₄ : a₁ * a₄ = a₄ * a₁ :=
    commute_of_isPComponent hp Nat.prime_three hK₁ hK₄ hne₁₄ hcore₁ hS.isPGroup ha₁ ha₄
  have hc₂₃ : a₂ * a₃ = a₃ * a₂ :=
    commute_of_isPComponent hp Nat.prime_three hK₂ hK₃ hne₂₃ hcore₂ hS.isPGroup ha₂ ha₃
  have hc₂₄ : a₂ * a₄ = a₄ * a₂ :=
    commute_of_isPComponent hp Nat.prime_three hK₂ hK₄ hne₂₄ hcore₂ hS.isPGroup ha₂ ha₄
  have hc₃₄ : a₃ * a₄ = a₄ * a₃ :=
    commute_of_isPComponent hp Nat.prime_three hK₃ hK₄ hne₃₄ hcore₃ hS.isPGroup ha₃ ha₄
  exact ⟨a₁, a₂, a₃, a₄, ha₁, ha₂, ha₃, ha₄, ho₁, ho₂, ho₃, ho₄,
    hc₁₂, hc₁₃, hc₁₄, hc₂₃, hc₂₄, hc₃₄⟩

private theorem four_order_three_independent {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections X)
    {K₁ K₂ K₃ K₄ : Subgroup X}
    (hK₁ : CFSG.IsPComponent p K₁) (hK₂ : CFSG.IsPComponent p K₂)
    (hK₃ : CFSG.IsPComponent p K₃) (hK₄ : CFSG.IsPComponent p K₄)
    (hrank₁ : CFSG.Open.pRank 3 K₁ = 1) (hrank₂ : CFSG.Open.pRank 3 K₂ = 1)
    (hrank₃ : CFSG.Open.pRank 3 K₃ = 1) (hrank₄ : CFSG.Open.pRank 3 K₄ = 1)
    (hne₁₂ : K₁ ≠ K₂) (hne₁₃ : K₁ ≠ K₃) (hne₁₄ : K₁ ≠ K₄)
    (hne₂₃ : K₂ ≠ K₃) (hne₂₄ : K₂ ≠ K₄) (hne₃₄ : K₃ ≠ K₄)
    {a₁ a₂ a₃ a₄ : X} (ha₁ : a₁ ∈ K₁) (ha₂ : a₂ ∈ K₂) (ha₃ : a₃ ∈ K₃) (ha₄ : a₄ ∈ K₄)
    (ho₁ : orderOf a₁ = 3) (ho₂ : orderOf a₂ = 3) (ho₃ : orderOf a₃ = 3)
    (ho₄ : orderOf a₄ = 3) :
    a₂ ∉ Subgroup.zpowers a₁ ∧
      a₃ ∉ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ∧
      a₄ ∉ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ⊔ Subgroup.zpowers a₃ := by
  have ha₁cent₂ : a₁ ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₂ :=
    le_centModSubgroup_of_isPComponent_ne hp hK₂ hK₁ hne₁₂.symm ha₁
  have ha₁cent₃ : a₁ ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₃ :=
    le_centModSubgroup_of_isPComponent_ne hp hK₃ hK₁ hne₁₃.symm ha₁
  have ha₁cent₄ : a₁ ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₄ :=
    le_centModSubgroup_of_isPComponent_ne hp hK₄ hK₁ hne₁₄.symm ha₁
  have ha₂cent₃ : a₂ ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₃ :=
    le_centModSubgroup_of_isPComponent_ne hp hK₃ hK₂ hne₂₃.symm ha₂
  have ha₂cent₄ : a₂ ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₄ :=
    le_centModSubgroup_of_isPComponent_ne hp hK₄ hK₂ hne₂₄.symm ha₂
  have ha₃cent₄ : a₃ ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₄ :=
    le_centModSubgroup_of_isPComponent_ne hp hK₄ hK₃ hne₃₄.symm ha₃
  have ha₂not : a₂ ∉ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₂ :=
    not_mem_centModSubgroup_of_order_three hp hSch hK₂ hrank₂ ha₂ ho₂
  have ha₃not : a₃ ∉ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₃ :=
    not_mem_centModSubgroup_of_order_three hp hSch hK₃ hrank₃ ha₃ ho₃
  have ha₄not : a₄ ∉ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₄ :=
    not_mem_centModSubgroup_of_order_three hp hSch hK₄ hrank₄ ha₄ ho₄
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    exact ha₂not (Subgroup.zpowers_le.mpr ha₁cent₂ hmem)
  · intro hmem
    exact ha₃not (sup_le
      (Subgroup.zpowers_le.mpr ha₁cent₃) (Subgroup.zpowers_le.mpr ha₂cent₃) hmem)
  · intro hmem
    have hE₂ : Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ≤
        CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K₄ :=
      sup_le (Subgroup.zpowers_le.mpr ha₁cent₄) (Subgroup.zpowers_le.mpr ha₂cent₄)
    exact ha₄not (sup_le hE₂ (Subgroup.zpowers_le.mpr ha₃cent₄) hmem)

private theorem isElemAbelian_sup_zpowers_of_commute {X : Type} [Group X]
    {E : Subgroup X} {a : X} (hE : CFSG.Open.IsElemAbelian 3 E)
    (ha : orderOf a = 3) (hcomm : ∀ x ∈ E, x * a = a * x) (haE : a ∉ E) :
    CFSG.Open.IsElemAbelian 3 (E ⊔ Subgroup.zpowers a) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers a) = Nat.card E * 3 := by
  have hpow : a ^ 3 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  have hcomm' : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxa : Commute x a := hcomm x hx
    exact (hxa.zpow_right k).eq
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hE
    (CFSG.Open.isElemAbelian_zpowers hpow) hcomm', ?_⟩
  rw [CFSG.RankThree.PartOne.K133.card_sup_zpowers (Y := E) (b := a) Nat.prime_three ha
    hcomm haE]

private theorem exists_elemAbelian_card_three_pow_four {X : Type} [Group X]
    {a₁ a₂ a₃ a₄ : X} (h₁ : orderOf a₁ = 3) (h₂ : orderOf a₂ = 3)
    (h₃ : orderOf a₃ = 3) (h₄ : orderOf a₄ = 3)
    (hc₁₂ : a₁ * a₂ = a₂ * a₁) (hc₁₃ : a₁ * a₃ = a₃ * a₁)
    (hc₁₄ : a₁ * a₄ = a₄ * a₁) (hc₂₃ : a₂ * a₃ = a₃ * a₂)
    (hc₂₄ : a₂ * a₄ = a₄ * a₂) (hc₃₄ : a₃ * a₄ = a₄ * a₃)
    (hn₂ : a₂ ∉ Subgroup.zpowers a₁)
    (hn₃ : a₃ ∉ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂)
    (hn₄ : a₄ ∉ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ⊔ Subgroup.zpowers a₃) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  let E₁ : Subgroup X := Subgroup.zpowers a₁
  let E₂ : Subgroup X := E₁ ⊔ Subgroup.zpowers a₂
  let E₃ : Subgroup X := E₂ ⊔ Subgroup.zpowers a₃
  let E₄ : Subgroup X := E₃ ⊔ Subgroup.zpowers a₄
  have hcard₁ : Nat.card E₁ = 3 := by
    rw [show E₁ = Subgroup.zpowers a₁ from rfl, Nat.card_zpowers, h₁]
  have hE₁ : CFSG.Open.IsElemAbelian 3 E₁ := by
    rw [show E₁ = Subgroup.zpowers a₁ from rfl]
    exact CFSG.Open.isElemAbelian_zpowers (by simpa [h₁] using pow_orderOf_eq_one a₁)
  have hcomm₁₂ : ∀ x ∈ E₁, x * a₂ = a₂ * x := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute a₁ a₂ from hc₁₂) m).eq
  obtain ⟨hE₂, hcard₂⟩ := isElemAbelian_sup_zpowers_of_commute hE₁ h₂ hcomm₁₂ hn₂
  have hcard₂' : Nat.card E₂ = 3 ^ 2 := by
    rw [hcard₂, hcard₁]
    norm_num
  have hcent₂₃ : E₂ ≤ Subgroup.centralizer ({a₃} : Set X) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hc₁₃
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hc₂₃
  have hcomm₂₃ : ∀ x ∈ E₂, x * a₃ = a₃ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hcent₂₃ hx)
  obtain ⟨hE₃, hcard₃⟩ := isElemAbelian_sup_zpowers_of_commute hE₂ h₃ hcomm₂₃ hn₃
  have hcard₃' : Nat.card E₃ = 3 ^ 3 := by
    rw [hcard₃, hcard₂']
    norm_num
  have hcent₃₄ : E₃ ≤ Subgroup.centralizer ({a₄} : Set X) := by
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hc₁₄
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hc₂₄
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hc₃₄
  have hcomm₃₄ : ∀ x ∈ E₃, x * a₄ = a₄ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hcent₃₄ hx)
  obtain ⟨hE₄, hcard₄⟩ := isElemAbelian_sup_zpowers_of_commute hE₃ h₄ hcomm₃₄ hn₄
  have hcard₄' : Nat.card E₄ = 3 ^ 4 := by
    rw [hcard₄, hcard₃']
    norm_num
  exact ⟨E₄, hE₄, hcard₄'⟩

namespace P812Hyp

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem mem_normalizer_two_of_odd (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {x : G} (hx : x ∈ M)
    (hodd : Odd (orderOf x)) : x ∈ Subgroup.normalizer (L₂ : Set G) := by
  classical
  let K₁ : Subgroup ↥M := L₁.subgroupOf M
  let K₂ : Subgroup ↥M := L₂.subgroupOf M
  let x' : ↥M := ⟨x, hx⟩
  have hne : K₁ ≠ K₂ := by simpa [K₁, K₂] using h.subgroupOf_ne
  have hrankK₁ : CFSG.Open.pRank 3 K₁ = 1 := by
    simpa [K₁] using h.pRank_three_subgroupOf₁
  have hrankK₂ : CFSG.Open.pRank 3 K₂ = 1 := by
    simpa [K₂] using h.pRank_three_subgroupOf₂
  have hodd' : Odd (orderOf x') := by simpa [x'] using hodd
  have hx'N : x' ∈ Subgroup.normalizer (K₂ : Set ↥M) := by
    by_contra hxN
    let K₃ : Subgroup ↥M := CFSG.conjugate K₂ x'
    let K₄ : Subgroup ↥M := CFSG.conjugate K₂ (x' ^ 2)
    obtain ⟨hK₃, hrankK₃⟩ := isPComponent_conjugate_rank_one h.comp₂ hrankK₂ x'
    obtain ⟨hK₄, hrankK₄⟩ := isPComponent_conjugate_rank_one h.comp₂ hrankK₂ (x' ^ 2)
    obtain ⟨hne₁₃, hne₁₄, hne₂₃, hne₂₄, hne₃₄⟩ :=
      four_conjugates_pairwise_distinct h.normal₁ hne hxN hodd'
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥M))
    let Ssub : Subgroup ↥M := S
    have hSsyl : CFSG.ABGLocalTools.IsSylowOf 3 Ssub ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
      exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
    obtain ⟨a₁, a₂, a₃, a₄, ha₁, ha₂, ha₃, ha₄, ho₁, ho₂, ho₃, ho₄,
      hc₁₂, hc₁₃, hc₁₄, hc₂₃, hc₂₄, hc₃₄⟩ :=
      exists_four_order_three_commuting h.prime hSch h.comp₁ h.comp₂ hK₃ hK₄
        hrankK₁ hrankK₂ hrankK₃ hrankK₄ hne hne₁₃ hne₁₄ hne₂₃ hne₂₄ hne₃₄ hSsyl
    have ha₁K₁ : a₁ ∈ K₁ := (Subgroup.mem_inf.mp ha₁).2
    have ha₂K₂ : a₂ ∈ K₂ := (Subgroup.mem_inf.mp ha₂).2
    have ha₃K₃ : a₃ ∈ K₃ := (Subgroup.mem_inf.mp ha₃).2
    have ha₄K₄ : a₄ ∈ K₄ := (Subgroup.mem_inf.mp ha₄).2
    obtain ⟨hn₂, hn₃, hn₄⟩ :=
      four_order_three_independent h.prime hSch h.comp₁ h.comp₂ hK₃ hK₄
        hrankK₁ hrankK₂ hrankK₃ hrankK₄ hne hne₁₃ hne₁₄ hne₂₃ hne₂₄ hne₃₄
        ha₁K₁ ha₂K₂ ha₃K₃ ha₄K₄ ho₁ ho₂ ho₃ ho₄
    obtain ⟨E, hEea, hEcard⟩ :=
      exists_elemAbelian_card_three_pow_four ho₁ ho₂ ho₃ ho₄
        hc₁₂ hc₁₃ hc₁₄ hc₂₃ hc₂₄ hc₃₄ hn₂ hn₃ hn₄
    have h4top : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) :=
      CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hEea hEcard
    have hle := CFSG.RankThree.PartTwo.Sec18.pRank_subgroupOf_le 3 Nat.prime_three
      (⊤ : Subgroup ↥M)
    rw [Subgroup.map_top, Subgroup.range_subtype] at hle
    exact absurd (h4top.trans hle)
      (not_le.mpr (h.rank_three.trans_lt (by norm_num)))
  have hmem : x' ∈ (Subgroup.normalizer (L₂ : Set G)).subgroupOf M := by
    rw [Subgroup.subgroupOf_normalizer_eq h.le₂]
    exact hx'N
  exact Subgroup.mem_subgroupOf.mp hmem

end P812Hyp

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
