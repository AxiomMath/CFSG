module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714A7
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Lin

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification CFSG.Blueprint CFSG.GH74.GLS.IVK

theorem exists_surjective_of_map_eq_range {A P G : Type*} [Group A] [Group P] [Group G] {L : Subgroup A}
    {ρ : A →* P} (hinj : Function.Injective ρ) (f : G →* P) (h : L.map ρ = f.range) :
    ∃ σ : G →* ↥L, Function.Surjective σ := by
  let e : ↥L ≃* ↥(L.map ρ) := L.equivMapOfInjective ρ hinj
  let σ : G →* ↥L :=
    e.symm.toMonoidHom.comp (f.codRestrict (L.map ρ) (fun g => h ▸ ⟨g, rfl⟩))
  refine ⟨σ, fun l => ?_⟩
  have hl : ρ l ∈ f.range := h ▸ ⟨l, l.2, rfl⟩
  obtain ⟨g, hg⟩ := hl
  refine ⟨g, ?_⟩
  apply e.injective
  apply Subtype.ext
  simp [σ, e, hg]

variable {k : Type} [Field k] [Finite k] {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem split_four_case_alt7_false [Finite A] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 4) k} (hρa : ρ a = conjAut 4 k B * dualAut 4 k)
    (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B)
    (hsplit : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0)
    (hsrc : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7))) : False := by
  classical
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift (by norm_num) B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut 4 k), (L.map ρ).comap (conjAut 4 k)⁆ with hXhdef
  set R : GL (Fin 4) k := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup 4 k R with hOdef
  have hR : (R : Matrix (Fin 4) (Fin 4) k)ᵀ = R := transpose_inv_eq_of_transpose_eq hB
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQdef
  have hQ : Q.polarBilin.Nondegenerate :=
    CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR
  have hdim : Module.finrank k (Fin 4 → k) = 4 := Module.finrank_fin_fun k
  set eO := matrixOrthogonalEquiv hk2 R hR with heO
  set f : TauCeti.QuadraticMap.orthogonalGroup Q →* GL (Fin 4) k :=
    O.subtype.comp eO.toMonoidHom with hf
  have hfi : Function.Injective f := O.subtype_injective.comp eO.injective
  have hfr : (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = O := by
    rw [← MonoidHom.range_eq_map, hf, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      eO.surjective, ← MonoidHom.range_eq_map, range_subtype]
  have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
    (Or.inr (Or.inr ⟨hdim, hsplit⟩))
  have hXq := (AssemblyBPredicates.isQuasisimple_iff_native Xh).1 hXh.2.2
  by_cases hq3 : Nat.card k = 3
  ·
    obtain ⟨hexc, -⟩ := hcov
    obtain ⟨hprime, -⟩ := hexc (Or.inr ⟨⟨hdim, hsplit⟩, Or.inr hq3⟩)
    have : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
      isSolvable_of_prime_dvd_card_eq_or_eq hprime
    have : Group.IsSolvable O :=
      Group.isSolvable_of_isSolvable_injective (f := eO.symm.toMonoidHom) eO.symm.injective
    have : Group.IsSolvable Xh :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXh.1)
        (Subgroup.inclusion_injective hXh.1)
    have : Nontrivial Xh := CFSG.LocalCores.isQuasisimple_nontrivial hXq
    have : Group.IsPerfect Xh := hXq.1
    exact Group.IsPerfect.not_isSolvable Xh inferInstance
  have hq2 : Nat.card k ≠ 2 := by
    intro h
    rw [h] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hq5 : 5 ≤ Nat.card k := by
    have h1 : 2 ≤ Nat.card k := by
      rw [hk]
      exact hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
    have h4 : Nat.card k ≠ 4 := fun h => by
      rw [h] at hodd
      exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
    omega
  obtain ⟨-, -, -, hsplitm, -, -, -⟩ := hcov
  obtain ⟨ψ, e, -, hψe, hsup, hq₁, hq₂, hn₁, hn₂, -⟩ := hsplitm hdim hsplit hq2 hq3
  have hfe : ∀ d : DeterminantIsometries k, f (e.symm d) = linearConjGL ψ d.val := by
    intro d
    apply eq_of_mulVec_eq
    intro v
    rw [linearConjGL_mulVec]
    change ((eO (e.symm d) : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v = _
    rw [matrixOrthogonalEquiv_mulVec]
    have h1 := hψe (e.symm d) (ψ v)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    rw [h1, LinearEquiv.symm_apply_apply]
  have hL₁r : ((determinantLeftFactor k).map e.symm.toMonoidHom).map f =
      (splitLeftHom ψ).range := by
    rw [determinantLeftFactor, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext U : 1
    exact hfe _
  have hL₂r : ((determinantRightFactor k).map e.symm.toMonoidHom).map f =
      (splitRightHom ψ).range := by
    rw [determinantRightFactor, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext W : 1
    exact hfe _
  have hcomp : ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsQuasisimple M → M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) →
      (M.subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal →
      CFSG.Assembly.IsComponentOf (M.map f) O := by
    intro M hMq hMle hMn
    have hM : CFSG.Assembly.IsComponentOf M ⊤ := by
      refine ⟨le_top, CFSG.Assembly.IsSubnormal.step hMle hMn
        (CFSG.Assembly.IsSubnormal.step le_top ?_ (CFSG.Assembly.IsSubnormal.refl _)),
        (AssemblyBPredicates.isQuasisimple_iff_native M).2 hMq⟩
      exact Subgroup.Normal.subgroupOf inferInstance _
    have := SymmetricLocal.isComponentOf_map_of_injective f hfi hM
    rwa [hfr] at this
  have hc₁ := hcomp _ hq₁ (hsup ▸ le_sup_left) hn₁
  have hc₂ := hcomp _ hq₂ (hsup ▸ le_sup_right) hn₂
  rw [hL₁r] at hc₁
  rw [hL₂r] at hc₂
  have hcommO : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = ⁅O, O⁆ := by
    rw [hf, ← Subgroup.map_map, ← Subgroup.map_subtype_commutator]
    congr 1
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eO.surjective]
  have hD : ⁅O, O⁆ = (splitLeftHom ψ).range ⊔ (splitRightHom ψ).range := by
    rw [← hcommO, hsup, Subgroup.map_sup, hL₁r, hL₂r]
  have hXhD : Xh ≤ ⁅O, O⁆ := by
    have : Group.IsPerfect Xh := ⟨hXh.2.2.1⟩
    rw [← Subgroup.commutator_eq_self (H := Xh)]
    exact Subgroup.commutator_mono hXh.1 hXh.1
  have hX : Xh = (splitLeftHom ψ).range ∨ Xh = (splitRightHom ψ).range := by
    rcases isComponentOf_eq_or_commute hXh hc₁ with h1 | h1
    · exact Or.inl h1
    rcases isComponentOf_eq_or_commute hXh hc₂ with h2 | h2
    · exact Or.inr h2
    exfalso
    have h1' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    have h2' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    refine not_commute_of_isQuasisimple hXh.2.2 fun x hx y hy => ?_
    have hle : (splitLeftHom ψ).range ⊔ (splitRightHom ψ).range ≤ centralizer {x} :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h1' hx)) z hz))
        (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h2' hx)) z hz))
    have hy' := hle (hD ▸ hXhD hy)
    exact (mem_centralizer_singleton_iff.mp hy').symm
  have hLX : L.map ρ = Xh.map (conjAut 4 k) := hmap.symm
  obtain ⟨σ, hσ⟩ : ∃ σ : SpecialLinearGroup (Fin 2) k →* ↥L, Function.Surjective σ := by
    rcases hX with h | h
    · rw [h] at hLX
      exact exists_surjective_of_map_eq_range hinj ((conjAut 4 k).comp (splitLeftHom ψ))
        (by rw [MonoidHom.range_comp]; exact hLX)
    · rw [h] at hLX
      exact exists_surjective_of_map_eq_range hinj ((conjAut 4 k).comp (splitRightHom ψ))
        (by rw [MonoidHom.range_comp]; exact hLX)
  obtain ⟨e₀⟩ := hsrc
  exact not_surjective_sl2_alt7 hodd (by omega)
    ((e₀.toMonoidHom.comp (QuotientGroup.mk' (center L))).comp σ)
    ((e₀.surjective.comp (QuotientGroup.mk'_surjective _)).comp hσ)

theorem linear_selector_four_false_alt7 {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hsrc : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    (hrank : Odd (Nat.card (center L)))
    {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ e) (φ : W ≃* projectiveSL 4 k) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hm3 : 3 ≤ 4 := by norm_num
  have hm4 : 4 ≤ 4 := le_rfl
  have hZ := center_projectiveSL_eq_bot (k := k) hm3
  obtain ⟨ρ, hinj, hρW, -, -⟩ := socle_extension hCW φ hZ
  obtain ⟨-, hCA, hCW', hL₁⟩ := socle_images φ hinj hρW hLW hL
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hsrc' : StatedClassicalModel (L ⧸ center L) .PSL 2 3 1 ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := Or.inr (Or.inl hsrc)
  have hPSL : ∀ (E : Type) [Field E] [Finite E], Nat.card E = Nat.card k ^ 2 →
      Nonempty (L ≃* projectiveSL 2 E) → False := by
    intro E _ _ hEc ⟨eL⟩
    have hE : Nat.card E = ℓ ^ (2 * e) := by rw [hEc, hk, ← pow_mul, mul_comm]
    have h4 : 4 ≤ ℓ ^ (2 * e) := by
      have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
      calc 4 ≤ ℓ ^ 2 := by nlinarith
        _ ≤ ℓ ^ (2 * e) := Nat.pow_le_pow_right hℓ.pos (by omega)
    have hX := statedClassicalModel_of_mulEquiv_projectiveSL_two hℓ (by omega) hE h4 eL
    obtain ⟨-, h7, -⟩ :=
      UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated hX
    exact h7.false hsrc.some
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ a)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      obtain ⟨μ, hμ, hsq, -⟩ :=
        inner_case_reduction ha hm4 hℓ hℓ2 he hk hinj hL₁ hρa hp2 hsrc' (fun _ => Or.inr hrank)
      obtain ⟨-, E, _, _, hE, hEL⟩ := selectorRowS_of_inner htwo hinj hCA hCW' hL₁ hρa hμ hsq
      exact hPSL E hE hEL
    · exact field_case_false ha hm3 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc'
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut 4 k B * dualAut 4 k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      rcases transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · by_cases hsp : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
            ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0
        · exact split_four_case_alt7_false hℓ hℓ2 he hk hinj hL₁ hρa hB hsp hsrc
        · obtain ⟨-, E, _, _, hE, hEL⟩ := selectorRowO_of_nonsplit hodd hinj hCA hCW' hL₁ hρa hB hsp
          exact hPSL E hE hEL
      · exact symplectic_case_false hm4 hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc'
    · exact graph_field_case_false ha hm4 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc'

theorem ivk714_psl_four {p f : ℕ} (hp2 : p ≠ 2) :
    Ivk714Empty (fun X _ => LieModel X .PSL 4 p f) := by
  intro K _ _ hs hK z hz h
  have hmodel := CFSG.GH74.Generic.S45.LQ.stated_of_lieModel_PSL hK
  have hZ : center K = ⊥ := center_eq_bot_of_simple_of_nonab hs h.nonabelian
  obtain ⟨L, hLW, hL, hq, hodd⟩ := h.exists_inner_component hZ
  have hCW := centralizer_inner_eq_bot_of_center_eq_bot hZ
  let e : K ≃* ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner K) :=
    MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)
  obtain ⟨⟨hr, hf', -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  let φ : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner K) ≃* projectiveSL 4 F :=
    e.symm.trans (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 F)))
  exact linear_selector_four_false_alt7
    (W := CFSG.ComponentClassification.OuterAutomorphisms.inner K) hCW hz hLW hL hq hodd hr hp2 hf'
    hF φ

theorem ivk714_l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk714Empty (fun X _ => LieModel X .PSL 4 p f) :=
  fun _ _ _ hp2 _ _ => ivk714_psl_four hp2

end CFSG.GH74.GLS.IVK.Proofs2
