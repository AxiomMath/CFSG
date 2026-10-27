module

public import CFSG.HardMathSupport.Seitz.G2Noninner.Interface

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.SEITZ2

section Pair

@[expose] def SubfieldPairG2At (K : Type) [Field K] [Finite K] : Prop :=
  ∀ (σ : K ≃+* K) (p : ℕ), p.Prime → 5 ≤ p → orderOf σ = p → ∀ g : adjointGroup .G2 K,
    (g2Fixed σ).map (MulAut.conj g).toMonoidHom ≠ g2Fixed σ →
    Subgroup.closure ((g2Fixed σ : Set (adjointGroup .G2 K)) ∪
      ((g2Fixed σ).map (MulAut.conj g).toMonoidHom : Set (adjointGroup .G2 K))) = ⊤ ∨
      ¬ p ∣ Nat.card (g2Fixed σ)

theorem SubfieldPairG2Odd.at (h : SubfieldPairG2Odd) {K : Type} [Field K] [Finite K]
    (h2 : ringChar K ≠ 2) : SubfieldPairG2At K :=
  fun σ p hp hp5 hσ g hg => h K h2 σ p hp hp5 hσ g hg

theorem ringChar_eq_of_card_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) : ringChar K = ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  exact ringChar.eq K ℓ

end Pair

section Rank

theorem exists_conj_mem_of_plane_of_hom {P Q : Type} [Group P] [Group Q] [Finite Q] [IsCyclic Q]
    {p : ℕ} (hp : p.Prime) (Θ : MulAut P →* Q)
    (hker : Θ.ker = (MulAut.conj : P →* MulAut P).range)
    (E : Subgroup (MulAut P)) [hE : IsElementaryAbelian p E] (hEc : Nat.card E = p ^ 2) :
    ∃ g : P, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  classical
  have := Fintype.ofFinite Q
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero 2 hp.ne_zero)
  let φ : E → {σ : Q // σ ^ p = 1} := fun e =>
    ⟨Θ e, by
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (A := E) (e : MulAut _) e.2, map_one]⟩
  have hcard : Nat.card {σ : Q // σ ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  have hlt : Nat.card {σ : Q // σ ^ p = 1} < Nat.card E := by
    rw [hEc]
    have := hp.two_le
    nlinarith
  have : Fintype E := Fintype.ofFinite E
  have hlt': Fintype.card {σ : Q // σ ^ p = 1} < Fintype.card E := by
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  obtain ⟨a, b, hab, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hlt'
  have hΘ : Θ ((a : MulAut _)⁻¹ * (b : MulAut _)) = 1 := by
    have h1 : Θ (a : MulAut _) = Θ (b : MulAut _) := congrArg Subtype.val hφ
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have hmem : (a : MulAut _)⁻¹ * (b : MulAut _) ∈ Θ.ker := hΘ
  rw [hker] at hmem
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_one] at hg
    apply hab
    have h1 : a.1 = b.1 := by
      have := congrArg (fun z => a.1 * z) hg
      simpa using this
    exact Subtype.ext h1
  · rw [hg]
    exact E.mul_mem (E.inv_mem a.2) b.2

end Rank

section Main

theorem fieldAutData_G2_of_descent {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hpair : SubfieldPairG2At K)
    (hp5 : 5 ≤ p)
    (hrank : ∀ E : Subgroup (MulAut (adjointGroup .G2 K)), IsElementaryAbelian p E →
      Nat.card E = p ^ 2 → ∃ g : adjointGroup .G2 K, g ≠ 1 ∧ MulAut.conj g ∈ E)
    (hdesc : ∀ α : MulAut (adjointGroup .G2 K), IsOuterOfOrder p α →
      ∃ (h : adjointGroup .G2 K) (σ : K ≃+* K), orderOf σ = p ∧
        MulAut.conj h * α * (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 σ) :
    FieldAutData (adjointGroup .G2 K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine fieldAutData_of_standard (MulAut.conj : adjointGroup .G2 K →* MulAut _).range
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut .G2 σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact hrank E hE hEc
  · intro α hα
    obtain ⟨h0, σ, hσ, h⟩ := hdesc α hα
    refine ⟨(MulAut.conj h0)⁻¹, ?_, entrywiseAdjointAut .G2 σ, ⟨σ, hσ, rfl⟩, ?_⟩
    · exact (MulAut.conj : adjointGroup .G2 K →* MulAut _).range.inv_mem ⟨h0, rfl⟩
    · rw [← h]
      group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [fixedSubgroup_entrywise_eq, fixedSubgroup_entrywise_eq]
    exact g2Fixed_congr (fixedField_eq_of_orderOf hℓ hf hK hσ hτ)
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    rw [fixedSubgroup_entrywise_eq] at hx hc
    exact eq_one_of_central_g2Fixed σ hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d ⟨g, rfl⟩ hne
    rw [fixedSubgroup_entrywise_eq] at hne ⊢
    exact hpair σ p hp hp5 hσ g hne

end Main

end CFSG.HardMathSupport.Seitz.G2Noninner
