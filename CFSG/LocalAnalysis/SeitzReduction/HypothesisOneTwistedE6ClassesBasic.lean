module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoBasic
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairs

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {K : Type} [Field K]

theorem diagramOrbit_eq_pair_twistedE6Classes (α : Fin TwistTag.E6.tag.rank → ℤ) :
    TwistTag.E6.diagramOrbit α = {α, permLattice TwistTag.E6.perm α} := by
  have h2 : Finset.range TwistTag.E6.order = {0, 1} := by decide
  rw [TwistTag.diagramOrbit, h2, Finset.image_insert, Finset.image_singleton, pow_zero, pow_one]
  rfl

theorem permLattice_add_twistedE6Classes (v w : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (v + w) =
      permLattice TwistTag.E6.perm v + permLattice TwistTag.E6.perm w := rfl


theorem commute_pinnedX_of_not_isRoot_of_ne_zero_E6 {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β)
    (h : ¬IsRoot TwistTag.E6.tag (α + β)) (h0 : α + β ≠ 0) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) := by
  by_cases hab : α = β
  · subst hab
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · exact commute_pinnedX_of_not_isRoot_add_E6 hα hβ hab
      (fun e => h0 (by rw [e, neg_add_cancel])) h c d

theorem commute_of_mem_rootSpan_twistedE6Classes {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    {g : ModGL TwistTag.E6.tag K}
    (hg : ∀ β ∈ S, ∀ d : K, Commute (pinnedX TwistTag.E6.tag K β d) g)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ rootSpan TwistTag.E6.tag K S) : Commute x g := by
  have hle : rootSpan TwistTag.E6.tag K S ≤ Subgroup.centralizer {g} := by
    refine iSup₂_le fun β hβ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨d, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hg β hβ d).eq.symm
  have := Subgroup.mem_centralizer_iff.1 (hle hx) g rfl
  exact this.symm

theorem commutator_twistedE6PairX_pairSum [CharP K 2] (σ : K →+* K)
    {δ ε : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (hε : IsRoot TwistTag.E6.tag ε) (hγ : IsRoot TwistTag.E6.tag (δ + ε)) (hne : δ ≠ ε)
    (h1 : ¬IsRoot TwistTag.E6.tag (δ + permLattice TwistTag.E6.perm ε))
    (h1' : δ + permLattice TwistTag.E6.perm ε ≠ 0)
    (h2 : ¬IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm (δ + ε) + δ))
    (h2' : permLattice TwistTag.E6.perm (δ + ε) + δ ≠ 0)
    (h3 : ¬IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm (δ + ε) + ε))
    (h3' : permLattice TwistTag.E6.perm (δ + ε) + ε ≠ 0) (s u : K) :
    ⁅twistedE6PairX σ δ s, twistedE6PairX σ ε u⁆ = twistedE6PairX σ (δ + ε) (s * u) := by
  have hρδ := hδ.permLattice TwistTag.E6.cartan_perm
  have hρε := hε.permLattice TwistTag.E6.cartan_perm
  have hργ := hγ.permLattice TwistTag.E6.cartan_perm
  have e1 := commutator_pinnedX_of_isRoot_add_E6 (K := K) hδ hε hne hγ s u
  have e2 : ⁅pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s),
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm ε) (σ u)⁆ =
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm (δ + ε)) (σ (s * u)) := by
    rw [permLattice_add_twistedE6Classes] at hργ ⊢
    rw [commutator_pinnedX_of_isRoot_add_E6 hρδ hρε
      (fun e => hne (permLattice_injective _ e)) hργ, map_mul]
  have c1 := commute_pinnedX_of_not_isRoot_of_ne_zero_E6 (K := K) hδ hρε h1 h1' s (σ u)
  have e : permLattice TwistTag.E6.perm δ + ε =
      permLattice TwistTag.E6.perm (δ + permLattice TwistTag.E6.perm ε) := by
    rw [permLattice_add_twistedE6Classes, permLattice_twistedE6_perm_perm]
  have c2 : Commute (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s))
      (pinnedX TwistTag.E6.tag K ε u) := by
    refine commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hρδ hε
      (by rw [e, isRoot_permLattice_twistedE6_iff]; exact h1) (fun h => h1' ?_) _ _
    apply permLattice_injective TwistTag.E6.perm
    rw [← e, h]
    rfl
  have c5 := commute_pinnedX_of_not_isRoot_of_ne_zero_E6 (K := K) hργ hδ h2 h2' (σ (s * u)) s
  have c6 := commute_pinnedX_of_not_isRoot_of_ne_zero_E6 (K := K) hργ hε h3 h3' (σ (s * u)) u
  unfold twistedE6PairX
  rw [commutatorElement_mul_mul_of_commute_of_commute c1 c2 (by rw [e2]; exact c5)
    (by rw [e2]; exact c6), e1, e2]
  exact (commute_pinnedX_permLattice_twistedE6 hγ (s * u) (σ (s * u))).eq.symm

theorem commutator_pinnedX_twistedE6PairX_of_fixed [CharP K 2] (σ : K →+* K)
    {α β : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hαρ : permLattice TwistTag.E6.perm α = α) (hβ : IsRoot TwistTag.E6.tag β)
    (hγ : IsRoot TwistTag.E6.tag (α + β))
    (he : IsRoot TwistTag.E6.tag (β + (α + permLattice TwistTag.E6.perm β))) (h1 : α ≠ β)
    (h2 : α ≠ permLattice TwistTag.E6.perm β) (h3 : β ≠ α + permLattice TwistTag.E6.perm β)
    (h4 : ¬IsRoot TwistTag.E6.tag (β + (α + permLattice TwistTag.E6.perm β) +
      (α + permLattice TwistTag.E6.perm β)))
    (h4' : β + (α + permLattice TwistTag.E6.perm β) + (α + permLattice TwistTag.E6.perm β) ≠ 0)
    {c : K} (hc : σ c = c) (s : K) :
    ⁅pinnedX TwistTag.E6.tag K α c, twistedE6PairX σ β s⁆ =
      twistedE6PairX σ (α + β) (c * s) *
        pinnedX TwistTag.E6.tag K (β + (α + permLattice TwistTag.E6.perm β)) (s * (c * σ s)) := by
  have hρβ := hβ.permLattice TwistTag.E6.cartan_perm
  have hργ : permLattice TwistTag.E6.perm (α + β) = α + permLattice TwistTag.E6.perm β := by
    rw [permLattice_add_twistedE6Classes, hαρ]
  have hγ' : IsRoot TwistTag.E6.tag (α + permLattice TwistTag.E6.perm β) := by
    rw [← hργ]
    exact hγ.permLattice TwistTag.E6.cartan_perm
  have hid : ∀ a b b' : ModGL TwistTag.E6.tag K, ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
    intro a b b'
    simp only [commutatorElement_def]
    group
  have hbx : ∀ b x : ModGL TwistTag.E6.tag K, b * x * b⁻¹ = ⁅b, x⁆ * x := by
    intro b x
    simp only [commutatorElement_def]
    group
  have e1 := commutator_pinnedX_of_isRoot_add_E6 (K := K) hα hβ h1 hγ c s
  have e2 := commutator_pinnedX_of_isRoot_add_E6 (K := K) hα hρβ h2 hγ' c (σ s)
  have e3 := commutator_pinnedX_of_isRoot_add_E6 (K := K) hβ hγ' h3 he s (c * σ s)
  have hcomm := commute_pinnedX_of_not_isRoot_of_ne_zero_E6 (K := K) he hγ' h4 h4'
    (s * (c * σ s)) (c * σ s)
  unfold twistedE6PairX
  rw [hid, e1, e2, hbx, e3, hργ, map_mul, hc, mul_assoc, hcomm.eq, ← mul_assoc]

theorem exists_eq_pinnedX_of_mem_fixedOrbitGroup [CharP K 2] {σ : K →+* K}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hργ : permLattice TwistTag.E6.perm γ = γ) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit γ : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K σ) :
    ∃ c : K, σ c = c ∧ x = pinnedX TwistTag.E6.tag K γ c := by
  obtain ⟨hxr, hxΓ⟩ := Subgroup.mem_inf.1 hx
  rw [diagramOrbit_eq_singleton_of_fixed hργ, Finset.coe_singleton,
    CFSG.LieType.Chevalley.rootSpan_singleton] at hxr
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hxr
  have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hxΓ).2
  rw [twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) _ hγ, hργ] at hF
  exact ⟨c, pinnedX_injective _ _ _ hF, rfl⟩

theorem exists_eq_twistedE6PairX_of_mem_orbitGroup [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (hδp : 0 < height δ) (hρδ : permLattice TwistTag.E6.perm δ ≠ δ) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit δ : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K σ) :
    ∃ s : K, x = twistedE6PairX σ δ s := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨hxr, hxΓ⟩ := Subgroup.mem_inf.1 hx
  set δ' := permLattice TwistTag.E6.perm δ with hδ'
  have hδ'r : IsRoot TwistTag.E6.tag δ' := hδ.permLattice TwistTag.E6.cartan_perm
  have hδ'p : 0 < height δ' := by rw [hδ', height_permLattice]; exact hδp
  have hO : ((TwistTag.E6.diagramOrbit δ : Finset _) : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
      Set.range ![δ, δ'] := by
    rw [diagramOrbit_eq_pair_twistedE6Classes, Finset.coe_insert, Finset.coe_singleton,
      Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  have hS : ∀ β ∈ Set.range ![δ, δ'], IsRoot TwistTag.E6.tag β ∧ 0 < height β := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨hδ, hδp⟩
    · exact ⟨hδ'r, hδ'p⟩
  have hcl : ∀ α ∈ Set.range ![δ, δ'], ∀ β ∈ Set.range ![δ, δ'], ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ Set.range ![δ, δ'] := by
    intro α hα β hβ a b ha hb hr
    rw [← hO] at hα hβ
    exact absurd hr (TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hδ hα hβ ha hb)
  have hinj : Function.Injective ![δ, δ'] := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij.symm hρδ
    · exact absurd hij hρδ
    · rfl
  have hbij := bijOn_prod_pinnedX K hS hcl ![δ, δ'] hinj rfl
  rw [hO] at hxr
  obtain ⟨c, -, hc⟩ := hbij.surjOn hxr
  have hc' : pinnedX TwistTag.E6.tag K δ (c 0) * pinnedX TwistTag.E6.tag K δ' (c 1) = x := by
    rw [← hc]
    simp [List.ofFn_succ]
  have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hxΓ).2
  rw [← hc', map_mul, twistHom_pinnedX_eq_of_charTwo h2 _ hδ,
    twistHom_pinnedX_eq_of_charTwo h2 _ hδ'r, hδ', permLattice_twistedE6_perm_perm,
    ← (commute_pinnedX_permLattice_twistedE6 hδ (σ (c 1)) (σ (c 0))).eq] at hF
  rw [← hδ'] at hF
  have heq : (![σ (c 1), σ (c 0)] : Fin 2 → K) = c := by
    refine hbij.injOn (Set.mem_univ _) (Set.mem_univ _) ?_
    simpa [List.ofFn_succ] using hF
  have h0 : σ (c 1) = c 0 := congrFun heq 0
  refine ⟨c 0, ?_⟩
  rw [← hc', twistedE6PairX, ← hδ']
  congr 2
  rw [← h0, hσσ]

theorem commutator_pinnedX_mem_and_rootCoord_E6 [Finite K] [CharP K 2]
    {γ' : Fin TwistTag.E6.tag.rank → ℤ} (hγ' : IsRoot TwistTag.E6.tag γ' ∧ 0 < height γ')
    {α β : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (hαp : 0 < height α)
    (hβ : IsRoot TwistTag.E6.tag β) (hβp : 0 < height β)
    (hht : height γ' ≤ height α + height β) (c d : K) :
    ⁅pinnedX TwistTag.E6.tag K α c, pinnedX TwistTag.E6.tag K β d⁆ ∈
        heightSeries TwistTag.E6.tag K (height γ') ∧
      rootCoord hγ' ⁅pinnedX TwistTag.E6.tag K α c, pinnedX TwistTag.E6.tag K β d⁆ =
        if α + β = γ' then c * d else 0 := by
  have hmem : ⁅pinnedX TwistTag.E6.tag K α c, pinnedX TwistTag.E6.tag K β d⁆ ∈
      heightSeries TwistTag.E6.tag K (height γ') := by
    have h1 := commutator_heightSeries_le (τ := TwistTag.E6.tag) K (height α) (height β)
      (Subgroup.commutator_mem_commutator (pinnedX_mem_heightSeries_height ⟨hα, hαp⟩ c)
        (pinnedX_mem_heightSeries_height ⟨hβ, hβp⟩ d))
    exact (iSup₂_le fun ε hε => le_iSup₂_of_le ε ⟨hε.1, hε.2.1, hht.trans hε.2.2⟩ le_rfl :
      heightSeries TwistTag.E6.tag K (height α + height β) ≤
        heightSeries TwistTag.E6.tag K (height γ')) h1
  refine ⟨hmem, ?_⟩
  by_cases hsum : IsRoot TwistTag.E6.tag (α + β)
  · have hne : α ≠ β := by
      rintro rfl
      rcases hsum.eq_one_or_neg_one_of_eq_smul (show α + α = (2 : ℤ) • α by rw [two_zsmul])
        with h | h <;> omega
    rw [commutator_pinnedX_of_isRoot_add_E6 hα hβ hne hsum]
    by_cases hγ : α + β = γ'
    · rw [ite_eq_left hγ]
      subst hγ
      exact rootCoord_self hγ' _
    · rw [ite_eq_right hγ]
      exact rootCoord_pinnedX_of_ne hγ' ⟨hsum, by rw [height_add]; omega⟩
        (by rw [height_add]; exact hht) hγ _
  · have h0 : α + β ≠ 0 := fun h => by
      have := congrArg height h
      rw [height_add, show height (0 : Fin TwistTag.E6.tag.rank → ℤ) = 0 by simp [height]] at this
      omega
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hα hβ hsum h0 c d).eq, rootCoord_one,
      ite_eq_right (fun h : α + β = γ' => hsum (h ▸ hγ'.1))]

theorem mem_rootSpan_of_commute_twistedE6 [Finite K] [CharP K 2] {σ : K →+* K} {d₀ : K}
    (hd₀ : σ d₀ ≠ d₀) {S A : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot TwistTag.E6.tag δ ∧ 0 < height δ)
    (hSρ : ∀ δ ∈ S, permLattice TwistTag.E6.perm δ ∈ S)
    (hAS : ∀ γ ∈ A, ∀ δ ∈ S, ¬IsRoot TwistTag.E6.tag (γ + δ))
    (hdet : ∀ γ, IsRoot TwistTag.E6.tag γ → 0 < height γ → γ ∉ A →
      ∃ δ ∈ S, IsRoot TwistTag.E6.tag (γ + δ))
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ posUnipotent TwistTag.E6.tag K)
    (hc1 : ∀ δ ∈ S, permLattice TwistTag.E6.perm δ = δ →
      z * pinnedX TwistTag.E6.tag K δ 1 = pinnedX TwistTag.E6.tag K δ 1 * z)
    (hc2 : ∀ δ ∈ S, permLattice TwistTag.E6.perm δ ≠ δ → ∀ d : K,
      z * twistedE6PairX σ δ d = twistedE6PairX σ δ d * z) :
    z ∈ rootSpan TwistTag.E6.tag K A := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨α, hα, hrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos (τ := TwistTag.E6.tag)
    (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β}) fun β hβ => hβ)
  have hpos : ∀ l, IsRoot TwistTag.E6.tag (α l) ∧ 0 < height (α l) := fun l => by
    have h : α l ∈ Set.range α := ⟨l, rfl⟩
    rwa [hrange] at h
  obtain ⟨c, -, hcz⟩ := ((positive_root_collection TwistTag.E6.tag K).2 α hα hrange).2.2 hz
  have hcz' : (List.ofFn fun l => pinnedX TwistTag.E6.tag K (α l) (c l)).prod = z := hcz
  have key : ∀ n : ℕ, ∀ l, height (α l) ≤ n → α l ∉ A → c l = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl _
      have := (hpos l).2
      push_cast at hl
      omega
    | succ n ih =>
      intro i hi hiA
      by_cases hle : height (α i) ≤ n
      · exact ih i hle hiA
      obtain ⟨δ, hδS, hγ'⟩ := hdet (α i) (hpos i).1 (hpos i).2 hiA
      obtain ⟨hδ, hδp⟩ := hS δ hδS
      have hγ'p : IsRoot TwistTag.E6.tag (α i + δ) ∧ 0 < height (α i + δ) :=
        ⟨hγ', by rw [height_add]; have := (hpos i).2; omega⟩
      have hlow : ∀ l, height (α l) < height (α i) → α l ∉ A → c l = 0 := fun l hl hlA =>
        ih l (by push_cast at hi; omega) hlA
      have hfac : ∀ β ∈ S, height β = height δ → ∀ (d : K) (l : Fin _),
          ⁅pinnedX TwistTag.E6.tag K (α l) (c l), pinnedX TwistTag.E6.tag K β d⁆ ∈
              heightSeries TwistTag.E6.tag K (height (α i + δ)) ∧
            rootCoord hγ'p ⁅pinnedX TwistTag.E6.tag K (α l) (c l),
                pinnedX TwistTag.E6.tag K β d⁆ =
              if α l + β = α i + δ then c l * d else 0 := by
        intro β hβS hβh d l
        obtain ⟨hβ, hβp⟩ := hS β hβS
        by_cases hl : height (α l) < height (α i)
        · by_cases hlA : α l ∈ A
          · have hnr := hAS _ hlA β hβS
            have h0 : α l + β ≠ 0 := fun h => by
              have := congrArg height h
              rw [height_add, show height (0 : Fin TwistTag.E6.tag.rank → ℤ) = 0 by
                simp [height]] at this
              have := (hpos l).2
              omega
            rw [commutatorElement_eq_one_iff_mul_comm.2
              (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 (hpos l).1 hβ hnr h0 _ _).eq,
              rootCoord_one, ite_eq_right (fun h : α l + β = α i + δ => hnr (h ▸ hγ'))]
            exact ⟨one_mem _, rfl⟩
          · rw [hlow l hl hlA, pinnedX_zero, commutatorElement_one_left, rootCoord_one, zero_mul,
              ite_self]
            exact ⟨one_mem _, rfl⟩
        · exact commutator_pinnedX_mem_and_rootCoord_E6 hγ'p (hpos l).1 (hpos l).2 hβ hβp
            (by rw [height_add, hβh]; omega) (c l) d
      have hsum : ∀ ws : List ((Fin TwistTag.E6.tag.rank → ℤ) × K),
          (∀ p ∈ ws, p.1 ∈ S ∧ height p.1 = height δ) →
          z * (ws.map fun p => pinnedX TwistTag.E6.tag K p.1 p.2).prod =
            (ws.map fun p => pinnedX TwistTag.E6.tag K p.1 p.2).prod * z →
          ∑ l, (ws.map fun p => if α l + p.1 = α i + δ then c l * p.2 else 0).sum = 0 := by
        intro ws hws hcomm
        obtain ⟨-, hπ⟩ := commutator_prod_mem_and_coord (U := posUnipotent TwistTag.E6.tag K)
          (M := heightSeries TwistTag.E6.tag K (height (α i + δ)))
          (heightSeries_le_normalizer K _) (rootCoord hγ'p)
          (fun x hx y hy => rootCoord_mul hγ'p hx hy) (fun g hg x hx => rootCoord_conj hγ'p hg hx)
          (List.ofFn fun l => pinnedX TwistTag.E6.tag K (α l) (c l))
          (ws.map fun p => pinnedX TwistTag.E6.tag K p.1 p.2)
          (fun x hx => by
            obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
            exact rootSubgroup_le_posUnipotent_of_height_pos (hpos l).1 (hpos l).2
              (mem_rootSubgroup.2 ⟨_, rfl⟩))
          (fun y hy => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
            exact rootSubgroup_le_posUnipotent_of_height_pos (hS _ (hws p hp).1).1
              (hS _ (hws p hp).1).2 (mem_rootSubgroup.2 ⟨_, rfl⟩))
          (fun x hx y hy => by
            obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
            exact (hfac p.1 (hws p hp).1 (hws p hp).2 p.2 l).1)
        rw [hcz', commutatorElement_eq_one_iff_mul_comm.2 hcomm, rootCoord_one, List.map_ofFn,
          List.sum_ofFn] at hπ
        refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) hπ.symm
        simp only [Function.comp_apply, List.map_map]
        congr 1
        refine List.map_congr_left fun p hp => ?_
        exact ((hfac p.1 (hws p hp).1 (hws p hp).2 p.2 l).2).symm
      have hsplit : ∀ (β : Fin TwistTag.E6.tag.rank → ℤ) (d : K),
          (∑ l, if α l + β = α i + δ then c l * d else 0) =
            (∑ l, if α l + β = α i + δ then c l else 0) * d := by
        intro β d
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by rw [ite_mul, zero_mul]
      have hself : (∑ l, if α l + δ = α i + δ then c l else 0) = c i := by
        rw [Finset.sum_eq_single i (fun l _ hl => by
          rw [ite_eq_right_iff]
          intro h
          exact absurd (hα (add_right_cancel h)) hl) (fun h => absurd (Finset.mem_univ i) h),
          ite_eq_left_iff.2 fun h => absurd rfl h]
      by_cases hδρ : permLattice TwistTag.E6.perm δ = δ
      · have h1 := hsum [(δ, 1)] (by simp [hδS]) (by simpa using hc1 δ hδS hδρ)
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1
        rw [hsplit, hself, mul_one] at h1
        exact h1
      · have hρh : height (permLattice TwistTag.E6.perm δ) = height δ := height_permLattice _ _
        have hd : ∀ d : K, c i * d +
            (∑ l, if α l + permLattice TwistTag.E6.perm δ = α i + δ then c l else 0) * σ d = 0 := by
          intro d
          have h1 := hsum [(δ, d), (permLattice TwistTag.E6.perm δ, σ d)]
            (by simp [hδS, hSρ δ hδS, hρh]) (by simpa [twistedE6PairX] using hc2 δ hδS hδρ d)
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            Finset.sum_add_distrib] at h1
          rw [hsplit, hsplit, hself] at h1
          exact h1
        set C := ∑ l, if α l + permLattice TwistTag.E6.perm δ = α i + δ then c l else 0
        have h1 := hd 1
        rw [mul_one, map_one, mul_one] at h1
        have hC : C = c i := by linear_combination h1 - c i * h2
        have h3 := hd d₀
        rw [hC] at h3
        have h4 : c i * (σ d₀ - d₀) = 0 := by linear_combination h3 - c i * d₀ * h2
        exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hd₀)
  rw [← hcz']
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
  by_cases hl : α l ∈ A
  · exact Subgroup.mem_iSup_of_mem (α l) (Subgroup.mem_iSup_of_mem hl
      (mem_rootSubgroup.2 ⟨_, rfl⟩))
  · rw [key (height (α l)).toNat l (Int.self_le_toNat _) hl, pinnedX_zero]
    exact one_mem _

end CFSG.SeitzReduction
