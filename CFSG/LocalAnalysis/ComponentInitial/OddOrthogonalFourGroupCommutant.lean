module

public import CFSG.LocalAnalysis.ComponentInitial.OddQuadraticEmptyLayer
public import CFSG.LocalAnalysis.ComponentInitial.LinearOrthogonalCommutant
public import CFSG.LocalAnalysis.ComponentInitial.LinearTraceZero
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalAssemblyAllDimensions

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module QuadraticMap Subgroup
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ComponentClassification

section Groups

variable {G : Type*} [Group G]

theorem le_commutator_of_isPerfect {B : Subgroup G} (hB : Group.IsPerfect B) :
    B ≤ commutator G := by
  rw [← Subgroup.isPerfect_iff.mp hB, _root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top

variable [Finite G]

theorem eq_commutator_of_isComponent {B : Subgroup G} (hB : CFSG.IsComponent B)
    (hq : CFSG.IsQuasisimple (commutator G)) : B = commutator G := by
  have hc : CFSG.IsComponent (commutator G) := ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩
  rcases CFSG.LocalCores.distinct_components_commute hB hc with h | h
  · exact h
  · refine absurd ?_ (not_le_centralizer_self_of_isQuasisimple
      ((AssemblyBPredicates.isQuasisimple_iff_native B).2 hB.1))
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (Subgroup.centralizer_le (le_commutator_of_isPerfect hB.1.1))

theorem eq_or_eq_of_isComponent_of_commutator_eq_sup {B L₁ L₂ : Subgroup G}
    (hB : CFSG.IsComponent B) (hsup : commutator G = L₁ ⊔ L₂) (hq₁ : CFSG.IsQuasisimple L₁)
    (hq₂ : CFSG.IsQuasisimple L₂) (hn₁ : (L₁.subgroupOf (commutator G)).Normal)
    (hn₂ : (L₂.subgroupOf (commutator G)).Normal) : B = L₁ ∨ B = L₂ := by
  have hL₁ : L₁ ≤ commutator G := by rw [hsup]; exact le_sup_left
  have hL₂ : L₂ ≤ commutator G := by rw [hsup]; exact le_sup_right
  rcases CFSG.LocalCores.distinct_components_commute hB
      (isComponent_of_le_of_normal hq₁ hL₁ hn₁) with h₁ | h₁
  · exact Or.inl h₁
  rcases CFSG.LocalCores.distinct_components_commute hB
      (isComponent_of_le_of_normal hq₂ hL₂ hn₂) with h₂ | h₂
  · exact Or.inr h₂
  refine absurd ?_ (not_le_centralizer_self_of_isQuasisimple
    ((AssemblyBPredicates.isQuasisimple_iff_native B).2 hB.1))
  have h₁' : L₁ ≤ centralizer (B : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h₁
  have h₂' : L₂ ≤ centralizer (B : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h₂
  exact (le_commutator_of_isPerfect hB.1.1).trans (hsup ▸ sup_le h₁' h₂')

end Groups

section SpecialLinear

variable {K : Type*} [Field K]

theorem specialLinear_two_eq_one_or_neg_one (h2 : (2 : K) ≠ 0)
    {A : Matrix.SpecialLinearGroup (Fin 2) K} (hA : A ^ 2 = 1) : A = 1 ∨ A = -1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  have hm : (A : Matrix (Fin 2) (Fin 2) K) * A = 1 := by
    have h := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
      (B : Matrix (Fin 2) (Fin 2) K)) hA
    simpa [_root_.sq] using h
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by
    decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e01 e10
  have hs : A 0 0 + A 1 1 ≠ 0 := by
    intro hs
    apply h2
    linear_combination -(e00 + hdet) + A 0 0 * hs
  have hb : A 0 1 = 0 := by
    have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : A 1 0 = 0 := by
    have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hs
  have ha : A 0 0 * A 0 0 = 1 := by rw [hb, zero_mul, add_zero] at e00; exact e00
  have hd : A 1 1 = A 0 0 := by
    have had : A 0 0 * A 1 1 = 1 := by rw [hb, zero_mul, sub_zero] at hdet; exact hdet
    have h0 : A 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one ha
    exact mul_left_cancel₀ h0 (had.trans ha.symm)
  have hsq : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by linear_combination ha
  rcases mul_eq_zero.mp hsq with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd] <;> linear_combination h
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd] <;> linear_combination h

theorem card_le_two_of_le_range {M : Type*} [Group M] (h2 : (2 : K) ≠ 0)
    (φ : Matrix.SpecialLinearGroup (Fin 2) K →* M) (hφ : Function.Injective φ)
    {E : Subgroup M} (hE : E ≤ φ.range) (hsq : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 2 := by
  have hsub : (E : Set M) ⊆ {1, φ (-1)} := by
    intro x hx
    obtain ⟨A, rfl⟩ := hE hx
    have hA : A ^ 2 = 1 := hφ (by rw [map_pow, map_one]; exact hsq _ hx)
    rcases specialLinear_two_eq_one_or_neg_one h2 hA with rfl | rfl
    · simp
    · simp
  calc Nat.card E = (E : Set M).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, φ (-1)} : Set M).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({φ (-1)} : Set M).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

open CatalogueBOrthogonalFourSplit in
theorem specialRho_inl_injective :
    Function.Injective ((specialRho (K := K)).comp (MonoidHom.inl _ _)) := by
  intro A A' h
  have h1 := congrArg (fun y : DeterminantIsometries K => y.val 1) h
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, specialRho_apply, inv_one,
    Matrix.SpecialLinearGroup.coe_one, mul_one] at h1
  exact Subtype.ext h1

open CatalogueBOrthogonalFourSplit in
theorem specialRho_inr_injective :
    Function.Injective ((specialRho (K := K)).comp (MonoidHom.inr _ _)) := by
  intro A A' h
  have h1 := congrArg (fun y : DeterminantIsometries K => y.val 1) h
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, specialRho_apply,
    Matrix.SpecialLinearGroup.coe_one, one_mul] at h1
  exact inv_injective (Subtype.ext h1)

end SpecialLinear

section Commutant

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem natural_commutant_of_le {N B : Subgroup (V ≃ₗ[k] V)} (hNB : N ≤ B)
    (h : (centralizer (N : Set (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) =
        {g | ∃ a : kˣ, ∀ v, g v = (a : k) • v} ∧
      {v : V | ∀ g ∈ N, g v = v} = {0} ∧
      ∀ f : Module.Dual k V, (∀ g ∈ N, ∀ v, f (g v) = f v) → f = 0) :
    (centralizer (B : Set (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) =
        {g | ∃ a : kˣ, ∀ v, g v = (a : k) • v} ∧
      {v : V | ∀ g ∈ B, g v = v} = {0} ∧
      ∀ f : Module.Dual k V, (∀ g ∈ B, ∀ v, f (g v) = f v) → f = 0 := by
  obtain ⟨hc, hfix, hfun⟩ := h
  refine ⟨Set.ext fun g => ⟨fun hg => ?_, ?_⟩, Set.ext fun v => ⟨fun hv => ?_, ?_⟩,
    fun f hf => hfun f fun g hg => hf g (hNB hg)⟩
  · rw [← hc]
    exact Subgroup.centralizer_le hNB hg
  · rintro ⟨a, ha⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h _ => LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, ha, map_smul]
  · rw [← hfix]
    exact fun g hg => hv g (hNB hg)
  · rintro rfl g _
    exact map_zero g

theorem natural_commutant_of_traceZeroConj (hk : ringChar k ≠ 2) {B : Subgroup (V ≃ₗ[k] V)}
    (ψ : V ≃ₗ[k] traceZeroMatrices k)
    (hB : ∀ S : Matrix.SpecialLinearGroup (Fin 2) k, ∃ b ∈ B, ∀ v,
      ψ (b v) = (traceZeroConj k S : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) (ψ v)) :
    (centralizer (B : Set (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) =
        {g | ∃ a : kˣ, ∀ v, g v = (a : k) • v} ∧
      {v : V | ∀ g ∈ B, g v = v} = {0} ∧
      ∀ f : Module.Dual k V, (∀ g ∈ B, ∀ v, f (g v) = f v) → f = 0 := by
  obtain ⟨hc, hfix, hfun⟩ := trace_zero_natural_SL2_commutant k hk
  refine ⟨Set.ext fun g => ⟨fun hg => ?_, ?_⟩, Set.ext fun v => ⟨fun hv => ?_, ?_⟩,
    fun f hf => ?_⟩
  ·
    let A : LinearMap.GeneralLinearGroup k (traceZeroMatrices k) :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv ((ψ.symm.trans g).trans ψ)
    have hA : A ∈ Subgroup.centralizer ((traceZeroConj k).range : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨S, rfl⟩
      obtain ⟨b, hb, hbS⟩ := hB S
      have hgb : ∀ x, b (g x) = g (b x) := fun x =>
        LinearEquiv.congr_fun (Subgroup.mem_centralizer_iff.mp hg b hb) x
      refine Units.ext (LinearMap.ext fun X => ?_)
      change (traceZeroConj k S : traceZeroMatrices k →ₗ[k] traceZeroMatrices k)
          (ψ (g (ψ.symm X))) =
        ψ (g (ψ.symm ((traceZeroConj k S : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X)))
      have h1 := hbS (g (ψ.symm X))
      have h2 := hbS (ψ.symm X)
      rw [LinearEquiv.apply_symm_apply] at h2
      rw [← h1, ← h2, LinearEquiv.symm_apply_apply, hgb]
    obtain ⟨a, ha⟩ := (hc A).mp hA
    refine ⟨a, fun v => ψ.injective ?_⟩
    have h := LinearMap.congr_fun ha (ψ v)
    change ψ (g (ψ.symm (ψ v))) = _ at h
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h, map_smul]
    rfl
  · rintro ⟨a, ha⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h _ => LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, ha, map_smul]
  ·
    have hψv : ψ v ∈ {X : traceZeroMatrices k | ∀ d ∈ (traceZeroConj k).range,
        (d : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X = X} := by
      rintro _ ⟨S, rfl⟩
      obtain ⟨b, hb, hbS⟩ := hB S
      rw [← hbS v, hv b hb]
    rw [hfix, Set.mem_singleton_iff] at hψv
    rw [Set.mem_singleton_iff]
    exact (LinearEquiv.map_eq_zero_iff ψ).mp hψv
  · rintro rfl g _
    exact map_zero g
  ·
    have hφ : f ∘ₗ (ψ.symm : traceZeroMatrices k →ₗ[k] V) ∈
        {φ : Module.Dual k (traceZeroMatrices k) | ∀ d ∈ (traceZeroConj k).range,
          φ ∘ₗ (d : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) = φ} := by
      rintro _ ⟨S, rfl⟩
      obtain ⟨b, hb, hbS⟩ := hB S
      refine LinearMap.ext fun X => ?_
      have h := hbS (ψ.symm X)
      rw [LinearEquiv.apply_symm_apply] at h
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← h, LinearEquiv.symm_apply_apply]
      exact hf b hb _
    rw [hfun, Set.mem_singleton_iff] at hφ
    refine LinearMap.ext fun v => ?_
    have h := LinearMap.congr_fun hφ (ψ v)
    simpa using h

end Commutant

section Orthogonal

variable {k : Type*} [Field k] [Finite k] {V : Type*} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

theorem orthogonal_three_field_three_solvable (hK : Nat.card k = 3) (Q : QuadraticForm k V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank k V = 3) :
    Group.IsSolvable (orthogonalGroup Q) := by
  have hodd : Odd (Nat.card k) := by rw [hK]; decide
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨-, -, e, -, -, -⟩ :=
    CatalogueBOrthogonalThreeSimilarity.exists_trace_zero_similarity_and_orthogonal_equiv hodd Q
      hQ hd
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) k) :=
    CatalogueBGeneralLinear.generalLinear_small_solvable 2 k (Or.inr ⟨rfl, Or.inr hK⟩)
  have : Group.IsSolvable (orthogonalGroup (CatalogueBOrthogonal.traceZeroForm k)) :=
    Group.isSolvable_of_surjective (CatalogueBOrthogonal.traceZeroFullAction_surjective h2)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem odd_orthogonal_component_with_four_group_natural_commutant (hk : ringChar k ≠ 2)
    (Q : QuadraticForm k V) (hQ : (polarBilin Q).Nondegenerate) {B₀ : Subgroup (V ≃ₗ[k] V)}
    (hB₀ : CFSG.Assembly.IsComponentOf B₀ (orthogonalGroup Q))
    (hE : ∃ E : Subgroup (V ≃ₗ[k] V), E ≤ B₀ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 4) :
    3 ≤ finrank k V ∧
      (centralizer (B₀ : Set (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) =
        {g | ∃ a : kˣ, ∀ v, g v = (a : k) • v} ∧
      {v : V | ∀ g ∈ B₀, g v = v} = {0} ∧
      ∀ f : Module.Dual k V, (∀ g ∈ B₀, ∀ v, f (g v) = f v) → f = 0 := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hodd : Odd (Nat.card k) := by
    have : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hk
  have hK2 : Nat.card k ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
  set O := orthogonalGroup Q with hO
  have : Finite V := Module.finite_of_finite k
  have : Finite O := Finite.of_injective (fun g : O => fun x : V => g.val x)
    fun g h hgh => Subtype.ext (LinearEquiv.ext (congrFun hgh))
  set B := B₀.subgroupOf O with hBdef
  have hB : CFSG.IsComponent B := (isComponentOf_iff_isComponent_subgroupOf hB₀.1).1 hB₀
  have hB₀eq : B.map O.subtype = B₀ := Subgroup.map_subgroupOf_eq_of_le hB₀.1
  have hns : ¬ Group.IsSolvable O := fun h => by
    have := h
    exact not_isComponent_of_isSolvable B hB
  have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
  have h3 : 3 ≤ finrank k V := by
    by_contra h
    exact hns ((CatalogueBOrthogonalAssembly.odd_orthogonal_all_dimensional_isometry_p_components
      hodd Q hQ).2 (by omega)).1
  refine ⟨h3, ?_⟩
  rcases h3.lt_or_eq with h4 | h3
  ·
    have hBc : B = commutator O := by
      by_cases hT : ∃ T : Submodule k V, finrank k T = 3 ∧ ∀ x ∈ T, Q x = 0
      · obtain ⟨T, hTdim, hTQ⟩ := hT
        exact eq_commutator_of_isComponent hB
          (CatalogueBOrthogonal.derived_quasisimple Q h2 hQ hTdim.ge hTQ)
      have h6 := (finite_odd_quadratic_low_Witt_dimension_bound hodd Q hQ).2.2 hT
      rcases (show finrank k V = 4 ∨ finrank k V = 5 ∨ finrank k V = 6 by omega) with
        hd | hd | hd
      · by_cases hS : ∃ S : Submodule k V, finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0
        ·
          exfalso
          obtain ⟨S, hSdim, hSQ⟩ := hS
          have hK3 : Nat.card k ≠ 3 := fun hK => hns
            (CatalogueBOrthogonalFourSplitComponents.orthogonal_four_split_three_solvable hK Q
              hQ hd S hSdim hSQ)
          obtain ⟨-, e, -, -, hsup, hq₁, hq₂, hn₁, hn₂, -⟩ :=
            (hcov (Or.inl ⟨hodd, Or.inr (Or.inl hd)⟩)).2.2.2.1 hd ⟨S, hSdim, hSQ⟩ hK2 hK3
          obtain ⟨E, hEB, hEab, hEcard⟩ := hE
          have key : ∀ φ : Matrix.SpecialLinearGroup (Fin 2) k →*
              CatalogueBOrthogonalFourSplit.DeterminantIsometries k, Function.Injective φ →
              B = φ.range.map e.symm.toMonoidHom → False := by
            intro φ hφ hBφ
            let ψ := O.subtype.comp (e.symm.toMonoidHom.comp φ)
            have hψ : Function.Injective ψ :=
              O.subtype_injective.comp (e.symm.injective.comp hφ)
            have hle : E ≤ ψ.range := by
              refine hEB.trans ?_
              rw [← hB₀eq, hBφ]
              rintro _ ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
              exact ⟨A, rfl⟩
            have hc := card_le_two_of_le_range h2 ψ hψ hle fun x hx => hEab.2 x hx
            omega
          rcases eq_or_eq_of_isComponent_of_commutator_eq_sup hB hsup hq₁ hq₂ hn₁ hn₂ with h | h
          · exact key _ specialRho_inl_injective h
          · exact key _ specialRho_inr_injective h
        · obtain ⟨-, -, -, -, -, -, -, -, hq⟩ :=
            (hcov (Or.inl ⟨hodd, Or.inr (Or.inl hd)⟩)).2.2.2.2.1 hodd hd hS
          exact eq_commutator_of_isComponent hB hq
      · obtain ⟨-, -, -, -, -, -, hq⟩ :=
          (hcov (Or.inl ⟨hodd, Or.inr (Or.inr hd)⟩)).2.2.2.2.2.1 hodd hd
        exact eq_commutator_of_isComponent hB hq
      · obtain ⟨-, -, -, -, -, -, -, -, hq⟩ :=
          (hcov (Or.inr (Or.inl ⟨hodd, hd, hT⟩))).2.2.2.2.2.2 hodd hd hT
        exact eq_commutator_of_isComponent hB hq
    have hD : ⁅⁅O, O⁆, ⁅O, O⁆⁆ ≤ B₀ := by
      rw [← hB₀eq, hBc, Subgroup.map_subtype_commutator]
      exact Subgroup.commutator_le_self _
    exact natural_commutant_of_le hD
      (odd_orthogonal_second_derived_natural_commutant hk (by omega) Q hQ)
  ·
    have hd : finrank k V = 3 := h3.symm
    have hK3 : Nat.card k ≠ 3 := fun hK => hns (orthogonal_three_field_three_solvable hK Q hQ hd)
    obtain ⟨-, ψ, e, -, he, hc, hq⟩ := (hcov (Or.inl ⟨hodd, Or.inl hd⟩)).2.2.1 hodd hd hK3
    have hBc : B = commutator O := eq_commutator_of_isComponent hB hq
    refine natural_commutant_of_traceZeroConj hk ψ fun S => ?_
    let y := CatalogueBOrthogonal.traceZeroOrthogonalAction (Matrix.SpecialLinearGroup.toGL S)
    refine ⟨O.subtype (e.symm y), ?_, fun v => ?_⟩
    · rw [← hB₀eq, hBc, hc]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ⟨S, rfl⟩)
    · have h := he (e.symm y) (ψ v)
      rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
      change ψ ((e.symm y).val v) = _
      rw [← h]
      rfl

end Orthogonal

end CFSG.LocalAnalysis.ComponentInitial
