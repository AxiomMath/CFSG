module

public import CFSG.ClassicalInvolution.Asc77.AscR10E9
public import CFSG.ClassicalInvolution.Asc77.AscR10E21
public import CFSG.ClassicalInvolution.Asc77.AscR10E5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Asc77.T3CII (GenSq genSq_top_sl2 eq_of_map_eq_of_genSq
  commute_of_map_commute_of_genSq eq_three_of_pow_eq_three ne_two_of_pow_eq_three)
open scoped commutatorElement MatrixGroups



section Lift

variable {K G : Type*} [Group K] [Group G]

theorem genSq_of_injOn_map {π : K →* G} {R : Subgroup K}
    (hinj : ∀ r ∈ R, π r = 1 → r = 1) (h : GenSq (R.map π)) : GenSq R := by
  set S := Subgroup.closure {x | ∃ a ∈ R, x = a * a} with hS
  have hSR : S ≤ R := (Subgroup.closure_le R).2 (by
    rintro _ ⟨a, ha, rfl⟩
    exact R.mul_mem ha ha)
  intro x hx
  have h1 : π x ∈ S.map π := by
    have h2 := h (Subgroup.mem_map_of_mem π hx)
    refine ((Subgroup.closure_le _).2 ?_) h2
    rintro _ ⟨_, ⟨a', ha', rfl⟩, rfl⟩
    exact ⟨a' * a', Subgroup.subset_closure ⟨a', ha', rfl⟩, by simp⟩
  obtain ⟨y, hy, hyx⟩ := h1
  have hxy : x * y⁻¹ = 1 := hinj _ (R.mul_mem hx (R.inv_mem (hSR hy))) (by
    rw [map_mul, map_inv, hyx]
    group)
  have : x = y := mul_inv_eq_one.1 hxy
  rw [this]
  exact hy

end Lift

section Abstract

variable {p e : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p e) V]
  [FiniteDimensional (GaloisField p e) V] {Q : QuadraticForm (GaloisField p e) V}

structure SpinCtx3 (p e : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (GaloisField p e) V] [FiniteDimensional (GaloisField p e) V]
    (Q : QuadraticForm (GaloisField p e) V) (𝔉 : Set (Subgroup (spinGroup Q))) : Prop where
  h3 : p ^ e = 3
  hQ : (polarBilin Q).Nondegenerate
  fin : Finite (spinGroup Q)
  hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1
  hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup Q))
  inj : ∀ R ∈ 𝔉, ∀ r ∈ R, spinAction Q r = 1 → r = 1
  map : ∀ R ∈ 𝔉, ∃ i, IsFundamental Q (R.map (spinAction Q)) i

namespace SpinCtx3

variable {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx3 p e Q 𝔉)

include S

theorem hp2 : p ≠ 2 := ne_two_of_pow_eq_three S.h3

theorem odd_card : Odd (Nat.card (GaloisField p e)) :=
  odd_natCard_galoisField_of_pow_eq_three S.h3

theorem one_le : 1 ≤ e := by
  rcases Nat.eq_zero_or_pos e with rfl | h
  · have := S.h3
    simp at this
  · exact h

theorem card_eq : Nat.card (GaloisField p e) = p ^ e :=
  GaloisField.card p e (by have := S.one_le; omega)

theorem card_eq' : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
  card_galoisField_two_mul p e S.one_le

theorem genSq {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝔉) : GenSq R := by
  obtain ⟨i, F, hF, -⟩ := S.map R hR
  have hp3 := (eq_three_of_pow_eq_three S.h3).1
  have : CharP (GaloisField p e) 3 := hp3 ▸ inferInstance
  have h1 : GenSq (R.map (spinAction Q)) := by
    rw [hF, MonoidHom.range_eq_map]
    exact genSq_top_sl2.map _
  exact genSq_of_injOn_map (S.inj R hR) h1

theorem eq_of_map_eq {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉)
    (h : R₁.map (spinAction Q) = R₂.map (spinAction Q)) : R₁ = R₂ :=
  eq_of_map_eq_of_genSq (spinAction Q) (ker_spinAction_le_center Q) S.hker2 (S.genSq h₁)
    (S.genSq h₂) h

theorem commutes_of_map {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉)
    (h : Commutes (R₁.map (spinAction Q)) (R₂.map (spinAction Q))) : Commutes R₁ R₂ :=
  fun a ha b hb => commute_of_map_commute_of_genSq (spinAction Q) (ker_spinAction_le_center Q)
    S.hker2 (S.genSq h₁) (b := b)
    (fun _ ha' => h _ (Subgroup.mem_map_of_mem _ ha') _ (Subgroup.mem_map_of_mem _ hb)) a ha

theorem linear_of_map {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉)
    (h : ∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map (spinAction Q))
      (R₂.map (spinAction Q))) : ∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂ := by
  have := S.fin
  exact RouteD.Gaps.exists_lin_of_map3 (eq_three_of_pow_eq_three S.h3).1 S.hC (spinAction Q)
    (ker_spinAction_le_center Q) S.hker2 (S.genSq h₁) (S.genSq h₂) h

theorem unitary_of_map {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉)
    (h : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₁.map (spinAction Q))
      (R₂.map (spinAction Q))) :
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have := S.fin
  exact exists_uni_of_map_three S.h3 S.card_eq' (spinAction Q) (ker_spinAction_le_center Q)
    S.hker2 (S.genSq h₁) (S.genSq h₂) h

theorem map_eq_of_orderOf {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝔉) {c : spinGroup Q}
    (hcR : c ∈ R) (ho : orderOf c = 2) {i : _ ≃ₗ[GaloisField p e] _}
    (hI : IsFundamental Q (R.map (spinAction Q)) i) : spinAction Q c = i := by
  have h2' : spinAction Q c ^ 2 = 1 := by
    rw [← map_pow, ← ho, pow_orderOf_eq_one, map_one]
  have h1 : spinAction Q c ≠ 1 := fun h1 => by
    have := S.inj R hR c hcR h1
    rw [this, orderOf_one] at ho
    omega
  exact hI.eq_of_orderOf_eq_two S.odd_card ⟨c, hcR, rfl⟩ (orderOf_eq_prime h2' h1)

theorem mem_normalizer {R₁ R₂ : Subgroup (spinGroup Q)} {c₁ c₂ : spinGroup Q}
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : c₁ * c₂ = c₂ * c₁)
    {i₁ i₂ : _ ≃ₗ[GaloisField p e] _}
    (hI₁ : IsFundamental Q (R₁.map (spinAction Q)) i₁)
    (hI₂ : IsFundamental Q (R₂.map (spinAction Q)) i₂) (e₁ : spinAction Q c₁ = i₁)
    (e₂ : spinAction Q c₂ = i₂) (hcπ : i₁ * i₂ = i₂ * i₁) :
    i₂ ∈ Subgroup.normalizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := IsFundamental.two_ne_zero_of_odd S.odd_card
  have : Invertible (2 : GaloisField p e) := invertibleOfNonzero h2
  have hsq : ∀ c : spinGroup Q, orderOf c = 2 → c * c = 1 := fun c hc => by
    rw [← pow_two]
    exact hc ▸ pow_orderOf_eq_one c
  have hfin : ∀ {L : Subgroup (V ≃ₗ[GaloisField p e] V)} {i : V ≃ₗ[GaloisField p e] V},
      IsFundamental Q L i → Module.finrank (GaloisField p e) (minusSp i) = 4 := by
    rintro L i ⟨Fr, -, rfl⟩
    exact (congrArg (fun W : Submodule (GaloisField p e) V => Module.finrank (GaloisField p e) W)
      (negSpace_La_neg_one h2 Fr)).trans (Frame.finrank_span Fr)
  have hii₁ : spinAction Q c₁ * spinAction Q c₁ = 1 := by
    rw [← map_mul, hsq c₁ ho₁, map_one]
  have hii₂ : spinAction Q c₂ * spinAction Q c₂ = 1 := by
    rw [← map_mul, hsq c₂ ho₂, map_one]
  have he₁ : Even (Module.finrank (GaloisField p e) (minusSp (spinAction Q c₁))) := by
    rw [e₁, hfin hI₁]
    exact ⟨2, rfl⟩
  have he₂ : Even (Module.finrank (GaloisField p e) (minusSp (spinAction Q c₂))) := by
    rw [e₂, hfin hI₂]
    exact ⟨2, rfl⟩
  have hpar := even_finrank_inf_minusSp_of_spin_commute S.hQ hc hii₁ hii₂ he₁ he₂
  rw [e₁, e₂] at hpar
  exact (mem_normalizer_iff_even S.odd_card hI₁ hI₂ hcπ).mpr hpar

end SpinCtx3

theorem SpinCtx3.dichotomy {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx3 p e Q 𝔉)
    {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) {c₁ c₂ : spinGroup Q}
    (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂) (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2)
    (hc : c₁ * c₂ = c₂ * c₁) :
    R₁ = R₂ ∨ Commutes R₁ R₂ ∨ (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have hodd := S.odd_card
  obtain ⟨i₁, hI₁⟩ := S.map R₁ h₁
  obtain ⟨i₂, hI₂⟩ := S.map R₂ h₂
  have e₁ := S.map_eq_of_orderOf h₁ hc₁ ho₁ hI₁
  have e₂ := S.map_eq_of_orderOf h₂ hc₂ ho₂ hI₂
  have hcπ : i₁ * i₂ = i₂ * i₁ := by
    rw [← e₁, ← e₂, ← map_mul, ← map_mul, hc]
  by_cases hL : R₁.map (spinAction Q) = R₂.map (spinAction Q)
  · exact Or.inl (S.eq_of_map_eq h₁ h₂ hL)
  · right
    by_cases hii : i₁ = i₂
    · left
      obtain ⟨L', hL', hne', hcomm', huniq⟩ := hI₁.exists_twin hodd
      have hL₂ : R₂.map (spinAction Q) = L' := by
        rcases huniq (R₂.map (spinAction Q)) (by rw [hii]; exact hI₂) with h | h
        · exact absurd h.symm hL
        · exact h
      exact S.commutes_of_map h₁ (by rw [hL₂]; exact hcomm')
    · have hcc := IsFundamental.commute_iff hodd hI₁ hI₂ hcπ hL
      by_cases hcent : i₂ ∈ Subgroup.centralizer ((R₁.map (spinAction Q) : Subgroup _) : Set _)
      · left
        exact S.commutes_of_map h₁ (hcc.mpr hcent)
      · right
        have hN := S.mem_normalizer ho₁ ho₂ hc hI₁ hI₂ e₁ e₂ hcπ
        rcases (lemma_6_10_dichotomy S.card_eq S.card_eq' hodd hI₁ hI₂ hcπ hN hcent).2 with
          ⟨-, hlin⟩ | ⟨-, huni⟩
        · exact Or.inl (S.linear_of_map h₁ h₂ ⟨_, hlin⟩)
        · exact Or.inr (S.unitary_of_map h₁ h₂ ⟨_, huni⟩)

end Abstract

end CFSG.ClassicalInvolution.ModelFacts
