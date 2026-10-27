module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSLBasic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (innerDiagonalAction)
open CFSG.ComponentClassification.CatalogueBLinearSemilinear (semilinearAction)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.CatalogueBGraphField (graphFieldAction)
open CFSG.ComponentClassification.SolMax.FiveCat.C5PSL
open scoped commutatorElement

theorem LitLayer.three_thousand_six_hundred_dvd {G : Type} [Group G] [Finite G]
    {L₁ L₂ : Subgroup G} (h₁ : LitLayer L₁) (h₂ : LitLayer L₂) (hne : L₁ ≠ L₂) :
    3600 ∣ Nat.card G := by
  have hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
    rcases CFSG.LocalCores.distinct_components_commute h₁.1 h₂.1 with h | h
    · exact absurd h hne
    · intro x hx y hy
      have h1 : ⁅x, y⁆ ∈ ⁅L₁, L₂⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
  let φ : ↥L₁ × ↥L₂ →* G :=
    MonoidHom.noncommCoprod L₁.subtype L₂.subtype (fun a b => hcomm a a.2 b b.2)
  let κ : φ.ker →* center L₁ :=
    { toFun := fun x => ⟨x.1.1, by
        rw [Subgroup.mem_center_iff]
        intro y
        have hx : (x.1.1 : G) * (x.1.2 : G) = 1 := MonoidHom.mem_ker.mp x.2
        have hx2 : (x.1.1 : G) = ((x.1.2 : G))⁻¹ := eq_inv_of_mul_eq_one_left hx
        apply Subtype.ext
        have := hcomm (y : G) y.2 ((x.1.2 : G)⁻¹) (L₂.inv_mem x.1.2.2)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hx2]
        exact this⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hκ : Function.Injective κ := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := congrArg (fun t : center L₁ => t.1) hab
    have ha : (a.1.1 : G) * (a.1.2 : G) = 1 := MonoidHom.mem_ker.mp a.2
    have hb : (b.1.1 : G) * (b.1.2 : G) = 1 := MonoidHom.mem_ker.mp b.2
    have h2 : (a.1.2 : G) = (b.1.2 : G) := by
      have e1 : (a.1.2 : G) = ((a.1.1 : G))⁻¹ := eq_inv_of_mul_eq_one_right ha
      have e2 : (b.1.2 : G) = ((b.1.1 : G))⁻¹ := eq_inv_of_mul_eq_one_right hb
      rw [e1, e2, h1]
    apply Subtype.ext
    apply Prod.ext
    · exact h1
    · exact Subtype.ext h2
  have hkdvd : Nat.card φ.ker ∣ Nat.card (center L₁) := Subgroup.card_dvd_of_injective κ hκ
  obtain ⟨hc₁, -⟩ := h₁.card_eq
  obtain ⟨hc₂, -⟩ := h₂.card_eq
  obtain ⟨m, hm⟩ := hkdvd
  have hk0 : 0 < Nat.card φ.ker := Nat.card_pos
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [Nat.card_prod, hc₁, hc₂, hm] at hcard
  have hr : Nat.card φ.range = 3600 * (m * Nat.card (center L₂)) := by
    apply Nat.eq_of_mul_eq_mul_left hk0
    rw [hcard]
    ring
  exact (Dvd.intro _ hr.symm).trans (Subgroup.card_subgroup_dvd_card φ.range)

namespace PSL2

@[expose] def LayerShape (n f : ℕ) (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, LitLayer L → (n = 2 ∧ f = 2) ∨ (n = 3 ∧ f = 1) ∨ (n = 4 ∧ f = 1)

theorem LayerShape.of_mulEquiv {n f : ℕ} {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : LayerShape n f H) : LayerShape n f G := fun L hL => h _ (hL.map e)

theorem layerShape_inner {n f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5 ^ f)
    (hadm : StatedLieAdmissible .PSL n 5 f) (A : GL (Fin n) K)
    (hA : orderOf (innerDiagonalAction n K A) = 2) :
    LayerShape n f (fixedSubgroup (innerDiagonalAction n K A)) := by
  rintro L ⟨hL, hA5, hz⟩
  exfalso
  rcases inner_psl_component_cases Nat.prime_five (by norm_num : (5 : ℕ) ≠ 2) hK hadm A hA hL with
    ⟨z, hzL, hzc, hzz, hz1⟩ | ⟨t, m, e, hT, hadm', hm'⟩
  · exact hz1 (hz z hzL hzc hzz)
  · obtain ⟨rfl, rfl, rfl⟩ := eq_psl_two_one_of_a5 (Or.inl (tag_of_mem_linInnerTuples hT)) hadm'
      hm' hA5
    exact not_mem_linInnerTuples hT

theorem layerShape_field {n f : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ f) (hf : 1 ≤ f) (A : GL (Fin n) K) (τ : K ≃+* K) (hτ : τ ≠ 1)
    (hsq : semilinearAction n K A τ ^ 2 = 1) :
    LayerShape n f (fixedSubgroup (semilinearAction n K A τ)) := by
  rintro L ⟨hL, hA5, -⟩
  obtain ⟨j, hj, hadm', hm'⟩ := field_psl_component_model hn Nat.prime_five
    (by norm_num : (5 : ℕ) ≠ 2) hf hK A τ hτ hsq (MulEquiv.refl _) hL
  obtain ⟨-, rfl, rfl⟩ := eq_psl_two_one_of_a5 (Or.inl rfl) hadm' hm' hA5
  exact Or.inl ⟨rfl, by omega⟩

theorem layerShape_graph {n f : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ f) (A : GL (Fin n) K)
    (hord : orderOf (pureGraphAction n K A) = 2) :
    LayerShape n f (fixedSubgroup (pureGraphAction n K A)) := by
  rintro L ⟨hL, hA5, -⟩
  obtain ⟨t, m, e, hT, hadm', hm'⟩ := graph_psl_component_models Nat.prime_five
    (by norm_num : (5 : ℕ) ≠ 2) hK hn A hord hL
  obtain ⟨rfl, rfl, rfl⟩ := eq_psl_two_one_of_a5 (isClassicalTag_of_mem_graphTuples hT) hadm'
    hm' hA5
  rcases mem_graphTuples_psl_two_one hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem layerShape_graphField {n f : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ f) (hf : 1 ≤ f) (A : GL (Fin n) K) (τ : K ≃+* K) (hτ : τ ≠ 1)
    (hord : orderOf (graphFieldAction n K A τ) = 2) :
    LayerShape n f (fixedSubgroup (graphFieldAction n K A τ)) := by
  rintro L ⟨hL, hA5, -⟩
  exfalso
  obtain ⟨j, hj, hadm', hm'⟩ := graphField_psl_component_model hn Nat.prime_five
    (by norm_num : (5 : ℕ) ≠ 2) hf hK A τ hτ hord (MulEquiv.refl _) hL
  obtain ⟨h, -⟩ := eq_psl_two_one_of_a5 (Or.inr (Or.inl rfl)) hadm' hm' hA5
  exact absurd h (by decide)

theorem layerShape_psl {J : Type} [Group J] {n f : ℕ} (hadm : StatedLieAdmissible .PSL n 5 f)
    (hm : Blueprint.LieModel J .PSL n 5 f) {α : MulAut J} (hα : orderOf α = 2) :
    LayerShape n f (fixedSubgroup α) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have key : ∀ γ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr e α = γ →
      (orderOf γ = 2 → LayerShape n f (fixedSubgroup γ)) → LayerShape n f (fixedSubgroup α) := by
    intro γ hγ h
    exact LayerShape.of_mulEquiv ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) (h (hγ ▸ hβ))
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e α = semilinearAction n K A σ → LayerShape n f (fixedSubgroup α) := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact key _ hAσ fun hord => layerShape_inner hK hadm A hord
    · exact key _ hAσ fun _ => layerShape_field hn hK hf A σ hσ (hAσ ▸ hβ2)
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := psl_two_normal_form (MulAut.congr e α)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr e α))
    have hβ' : MulAut.congr e α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact hsemi A σ hβ'
    · rw [pow_one] at hβ'
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        exact key _ hβ' fun hord => layerShape_graph hn3 hK A hord
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' fun hord => layerShape_graphField hn3 hK hf A σ hσ hord

end PSL2

theorem not_dvd_3600_psl {S : Type} [Group S] {n f : ℕ} (hm : Blueprint.LieModel S .PSL n 5 f)
    (h : (n = 2 ∧ f = 2) ∨ (n = 3 ∧ f = 1)) : ¬ 3600 ∣ Nat.card S := by
  have hadm : StatedLieAdmissible .PSL n 5 f := hm.admissible
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨hmul, -⟩ := lieOrder_of_lieModel_classical (Or.inl rfl) (by norm_num : (5 : ℕ) ≠ 2)
    (by omega : n ≠ 0) hm
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h7800 : Nat.card S = 7800 := by
      simp [lieOrderDivisor, lieOrderNumerator] at hmul
      omega
    rw [h7800]
    norm_num
  · have h372 : Nat.card S = 372000 := by
      simp [lieOrderDivisor, lieOrderNumerator, Finset.prod_Icc_succ_top] at hmul
      omega
    rw [h372]
    norm_num

theorem fiveTwoLayer_char5_PSL : FiveTwoLayerCharFiveClause .PSL := by
  intro S _ _ hs hna ⟨n, f, hm⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  haveI := hs
  have hadm : StatedLieAdmissible .PSL n 5 f := hm.admissible
  have hσ1 : σ ≠ 1 := h₁.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h₁.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hq : ∀ α : MulAut S, α * α = 1 → α ≠ 1 →
      ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_lin (by norm_num : (5 : ℕ) ≠ 2) (Or.inl rfl) hadm hm
  obtain ⟨L₁, L₂, hl₁, hl₂, hne', -⟩ :=
    twoLayers_of_clause hq h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  have hshape := PSL2.layerShape_psl hadm hm hσ2 L₁ hl₁
  have h3600 : 3600 ∣ Nat.card S :=
    (LitLayer.three_thousand_six_hundred_dvd hl₁ hl₂ hne').trans (Subgroup.card_subgroup_dvd_card _)
  rcases hshape with h | h | ⟨rfl, rfl⟩
  · exact absurd h3600 (not_dvd_3600_psl hm (Or.inl h))
  · exact absurd h3600 (not_dvd_3600_psl hm (Or.inr h))
  · exact Or.inl hm

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5
