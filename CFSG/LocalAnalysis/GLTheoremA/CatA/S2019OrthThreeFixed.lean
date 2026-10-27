module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthHeis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthThreeBlocks
import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal

section Heis

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

private theorem two_ne_zero_of_char_three [CharP K 3] : (2 : K) ≠ 0 := by
  intro h0
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  exact one_ne_zero (by linear_combination h3 - h0 : (1 : K) = 0)

private theorem three_le_card_of_char_three [CharP K 3] : 3 ≤ Nat.card K := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  rw [Nat.card_eq_fintype_card, hn]
  exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) n.pos)

theorem orthBlockThree_heis [CharP K 3] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ finrank K W) (D : OrthHeisData Q) :
    OrthBlockThree ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have h3K : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_char_three
  have h21 : (2 : K) ≠ 1 := fun h => one_ne_zero (by linear_combination h : (1 : K) = 0)
  have hγ : D.γ ≠ 0 := by
    rw [OrthHeisData.γ, polar_self_eq_two_mul]
    exact mul_ne_zero h2 D.hQa
  have hK3 : 3 ≤ Nat.card K := three_le_card_of_char_three
  have he₂ : D.P₂.e ∈ D.P₁.perp := HypPair.mem_perp.2 ⟨D.orth.ee, D.orth.fe⟩
  refine ⟨D.heisGroupO, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, t, c, rfl⟩
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup h2 h21 D.P₁
        (Submodule.smul_mem _ s D.ha₁)
    · exact CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup h2 h21 D.P₂
        (Submodule.smul_mem _ t D.ha₂)
    · exact CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup h2 h21 D.P₁
        (Submodule.smul_mem _ c he₂)
  · rintro ⟨_, s, t, c, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, D.elt_pow_three]; rfl)⟩
  · haveI : Finite W := Module.finite_of_finite K
    haveI : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
    have hinj : Function.Injective (fun st : K × K =>
        (⟨D.elt st.1 st.2 0, st.1, st.2, 0, rfl⟩ : D.heisGroupO)) := by
      rintro ⟨s, t⟩ ⟨s', t'⟩ h
      have := D.elt_injective hγ (congrArg Subtype.val h)
      exact Prod.ext this.1 this.2
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod] at this
    nlinarith
  · intro u hu hcomm
    obtain ⟨hsc, -, -⟩ :=
      CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
        (by omega) Q hQ h3
    obtain ⟨c, hc⟩ := (hsc (u : W →ₗ[K] W)).1 (fun g hg => LinearMap.ext fun w => by
      have := congrArg (fun f : W ≃ₗ[K] W => f w) (hcomm g hg)
      simpa using this)
    have hcw : ∀ w, u w = c • w := fun w => by
      have := LinearMap.congr_fun hc w
      simpa using this
    have hu3 : u ^ 3 = 1 := by
      obtain ⟨s, t, c', rfl⟩ := hu
      exact D.elt_pow_three s t c'
    have ha0 : D.a ≠ 0 := fun h => D.hQa (by rw [h, QuadraticMap.map_zero])
    have hc3 : c ^ 3 = 1 := by
      have h1 : u (u (u D.a)) = D.a := by
        have : (u ^ 3) D.a = D.a := by rw [hu3]; rfl
        rwa [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
      rw [hcw, hcw, hcw, smul_smul, smul_smul] at h1
      have h2' : (c * c * c - 1) • D.a = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      have := (smul_eq_zero.1 h2').resolve_right ha0
      linear_combination this
    have hc1 : c = 1 := by
      have : (c - 1) ^ 3 = 0 := by linear_combination hc3 + (-(c ^ 2) + c) * h3K
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    apply LinearEquiv.ext
    intro w
    rw [hcw, hc1, one_smul]
    rfl
  · rintro _ ⟨s, t, c, rfl⟩ hcent -
    rw [D.eq_eC_of_central hγ hcent]
    exact D.eC_sub_one_sq c

private theorem polar_eq_zero_of_mem_singular {S : Submodule K W} (hS : ∀ y ∈ S, Q y = 0)
    {x y : W} (hx : x ∈ S) (hy : y ∈ S) : polar Q x y = 0 := by
  rw [polar, hS _ (S.add_mem hx hy), hS x hx, hS y hy, sub_zero, sub_zero]

theorem exists_orthHeisData (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank K W) (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ y ∈ S, Q y = 0) :
    Nonempty (OrthHeisData Q) := by
  classical
  obtain ⟨S, hS2, hSQ⟩ := hS
  let b : Module.Basis (Fin 2) K S := Module.finBasisOfFinrankEq K S hS2
  set u₁ : W := (b 0 : W) with hu₁
  set u₂ : W := (b 1 : W) with hu₂
  have hu₁S : u₁ ∈ S := (b 0).2
  have hu₂S : u₂ ∈ S := (b 1).2
  have hu₁0 : u₁ ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
  obtain ⟨P₁, hP₁⟩ := exists_hypPair hQ (hSQ u₁ hu₁S) hu₁0
  set v := P₁.proj u₂ with hv
  have hvperp : v ∈ P₁.perp := P₁.proj_mem_perp u₂
  have h21 : polar Q u₂ u₁ = 0 := polar_eq_zero_of_mem_singular hSQ hu₂S hu₁S
  have hveq : v = u₂ - polar Q u₂ P₁.f • u₁ := by
    rw [hv, HypPair.proj, hP₁, h21, zero_smul, sub_zero]
  have hQv : Q v = 0 := by
    rw [hveq, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_smul_eq_sq,
      hSQ u₂ hu₂S, hSQ u₁ hu₁S, polar_neg_right, polar_smul_right_eq, h21]
    ring
  have hv0 : v ≠ 0 := by
    intro h0
    rw [hveq, sub_eq_zero] at h0
    generalize hc : polar Q u₂ P₁.f = c at h0
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli ![-c, 1] (by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul]
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero, neg_smul,
        Submodule.coe_neg]
      rw [← hu₁, ← hu₂, h0]
      abel) 1
    simp at this
  have hnd₁ := P₁.polarNondegOn_perp hQ
  obtain ⟨y, hy, hvy⟩ := hnd₁.exists_polar_ne_zero hvperp hv0
  have hvy1 : polar Q v ((polar Q v y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hvy]
  set P₂ := HypPair.ofPolarEqOne hQv hvy1 with hP₂
  have hP₂e : P₂.e = v := rfl
  have hP₂f : P₂.f ∈ P₁.perp := by
    rw [hP₂, HypPair.ofPolarEqOne_f]
    exact P₁.perp.sub_mem (P₁.perp.smul_mem _ hy) (P₁.perp.smul_mem _ hvperp)
  have horth : P₁.Orth P₂ := by
    obtain ⟨hee, hfe⟩ := HypPair.mem_perp.1 (show P₂.e ∈ P₁.perp from hP₂e ▸ hvperp)
    obtain ⟨hef, hff⟩ := HypPair.mem_perp.1 hP₂f
    exact ⟨hee, hef, hfe, hff⟩
  have hnd₁₂ := hnd₁.inf_perp P₂ (hP₂e ▸ hvperp) hP₂f
  have hne : P₁.perp ⊓ P₂.perp ≠ ⊥ := by
    intro hbot
    have hle : (⊤ : Submodule K W) ≤ Submodule.span K (Set.range ![P₁.e, P₁.f, P₂.e, P₂.f]) := by
      intro z _
      have hz1 := P₁.eq_add_proj z
      have hp1 := P₁.proj_mem_perp z
      have hz2 := P₂.eq_add_proj (P₁.proj z)
      have hp2 : P₂.proj (P₁.proj z) ∈ P₁.perp ⊓ P₂.perp := by
        refine ⟨?_, P₂.proj_mem_perp _⟩
        rw [HypPair.proj]
        exact P₁.perp.sub_mem (P₁.perp.sub_mem hp1 (P₁.perp.smul_mem _ (hP₂e ▸ hvperp)))
          (P₁.perp.smul_mem _ hP₂f)
      rw [hbot, Submodule.mem_bot] at hp2
      rw [hz2, hp2, add_zero] at hz1
      rw [hz1]
      have hmem : ∀ i : Fin 4, ![P₁.e, P₁.f, P₂.e, P₂.f] i ∈
          Submodule.span K (Set.range ![P₁.e, P₁.f, P₂.e, P₂.f]) :=
        fun i => Submodule.subset_span ⟨i, rfl⟩
      exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem 0))
        (Submodule.smul_mem _ _ (hmem 1))) (Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem 2))
          (Submodule.smul_mem _ _ (hmem 3)))
    have h1 := Submodule.finrank_mono hle
    rw [finrank_top] at h1
    have h2' := finrank_range_le_card (R := K) ![P₁.e, P₁.f, P₂.e, P₂.f]
    simp only [Fintype.card_fin] at h2'
    have : finrank K W ≤ 4 := h1.trans h2'
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨w, hw, huw⟩ := hnd₁₂.exists_polar_ne_zero hu hu0
  obtain ⟨a, ha, hQa⟩ : ∃ a ∈ P₁.perp ⊓ P₂.perp, Q a ≠ 0 := by
    by_cases hQu : Q u = 0
    · by_cases hQw : Q w = 0
      · refine ⟨u + w, Submodule.add_mem _ hu hw, ?_⟩
        rw [QuadraticMap.map_add Q, hQu, hQw, zero_add, zero_add]
        exact huw
      · exact ⟨w, hw, hQw⟩
    · exact ⟨u, hu, hQu⟩
  exact ⟨⟨P₁, P₂, a, horth, ha.1, ha.2, hQa⟩⟩

end Heis

section Split

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K W}

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial

private noncomputable def slUp (a : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem slUp_add (a b : K) : slUp (a + b) = slUp a * slUp b := by
  ext i j
  change (!![1, a + b; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j =
    (!![1, a; 0, 1] * !![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem slUp_zero : slUp (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slUp]

theorem orthBlockThree_split_factors [CharP K 3] (hK9 : 9 ≤ Nat.card K)
    (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃* DeterminantIsometries K)
    (he : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : Matrix (Fin 2) (Fin 2) K),
      (e g).val X = ψ (g.val (ψ.symm X))) :
    OrthBlockThree (((determinantLeftFactor K).map e.symm.toMonoidHom).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) ∧
      OrthBlockThree (((determinantRightFactor K).map e.symm.toMonoidHom).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) := by
  have h3K : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hact : ∀ (z : DeterminantIsometries K) (w : W),
      ((e.symm z : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) w =
        ψ.symm (z.val (ψ w)) := by
    intro z w
    have h := he (e.symm z) (ψ w)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  set M' : Matrix (Fin 2) (Fin 2) K := !![1, 0; 1, 1] with hM'def
  have hdet' : M'.det = 1 := by simp [hM'def, Matrix.det_fin_two]
  set A' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨M', hdet'⟩ with hA'
  let φL : Multiplicative K →* (W ≃ₗ[K] W) :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp (e.symm.toMonoidHom.comp
      ((specialRho (K := K)).comp ((MonoidHom.inl _ _).comp
        { toFun := fun a => slUp (Multiplicative.toAdd a)
          map_one' := slUp_zero
          map_mul' := fun a b => slUp_add _ _ })))
  let φR : Multiplicative K →* (W ≃ₗ[K] W) :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp (e.symm.toMonoidHom.comp
      ((specialRho (K := K)).comp ((MonoidHom.inr _ _).comp
        { toFun := fun a => slUp (-Multiplicative.toAdd a)
          map_one' := by rw [toAdd_one, neg_zero, slUp_zero]
          map_mul' := fun a b => by rw [toAdd_mul, neg_add, slUp_add] })))
  have hφL : ∀ a w, φL a w = ψ.symm (!![1, Multiplicative.toAdd a; 0, 1] * ψ w) := by
    intro a w
    change ((e.symm (specialRho (slUp (Multiplicative.toAdd a), 1)) :
      TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) w = _
    rw [hact, specialRho_apply]
    simp [slUp]
  have hφR : ∀ a w, φR a w = ψ.symm (ψ w * !![1, Multiplicative.toAdd a; 0, 1]) := by
    intro a w
    change ((e.symm (specialRho (1, slUp (-Multiplicative.toAdd a))) :
      TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) w = _
    rw [hact, specialRho_apply]
    have hinv : (slUp (-Multiplicative.toAdd a))⁻¹ = slUp (Multiplicative.toAdd a) := by
      rw [inv_eq_iff_mul_eq_one, ← slUp_add, neg_add_cancel, slUp_zero]
    rw [hinv]
    simp [slUp]
  have hmatL : ∀ a : K, a ≠ 0 → !![1, a; 0, 1] * M' ≠ M' * !![1, a; 0, 1] := by
    intro a ha h
    have h00 := congrFun (congrFun h 0) 0
    simp [hM'def, Matrix.mul_apply, Fin.sum_univ_two] at h00
    exact ha h00
  have key : ∀ (φ : Multiplicative K →* (W ≃ₗ[K] W)) (F : Subgroup (W ≃ₗ[K] W)),
      (∀ a, φ a ∈ F) → Function.Injective φ →
      (∀ a, ((((φ a : W ≃ₗ[K] W) : W →ₗ[K] W) - 1) ^ 2) = 0) →
      (∀ a, a ≠ 1 → ∃ j ∈ F, φ a * j ≠ j * φ a) → OrthBlockThree F := by
    intro φ F hφF hinj hsq hnc
    refine ⟨φ.range, fun _ ⟨a, ha⟩ => ha ▸ hφF a, ?_, ?_, ?_, ?_⟩
    · rintro ⟨_, a, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      have : a ^ 3 = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, Nat.cast_ofNat, h3K, zero_mul]
      rw [pow_one, Subgroup.coe_pow, ← map_pow, this, map_one]
      rfl
    · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)]
      exact hK9
    · rintro _ ⟨a, rfl⟩ hcomm
      by_contra hne
      have ha : a ≠ 1 := fun h => hne (by rw [h, map_one])
      obtain ⟨j, hj, hnj⟩ := hnc a ha
      exact hnj (hcomm j hj)
    · rintro _ ⟨a, rfl⟩ - -
      exact hsq a
  have hsqL : ∀ a, ((((φL a : W ≃ₗ[K] W) : W →ₗ[K] W) - 1) ^ 2) = 0 := by
    intro a
    have h1 : ∀ w, (((φL a : W ≃ₗ[K] W) : W →ₗ[K] W) - 1) w =
        ψ.symm ((!![1, Multiplicative.toAdd a; 0, 1] - 1) * ψ w) := by
      intro w
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, hφL, sub_mul, one_mul,
        map_sub, LinearEquiv.symm_apply_apply]
    have hN : (!![1, Multiplicative.toAdd a; 0, 1] - 1) *
        (!![1, Multiplicative.toAdd a; 0, 1] - 1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    refine LinearMap.ext fun w => ?_
    rw [pow_two, Module.End.mul_apply, h1, h1, LinearEquiv.apply_symm_apply, ← mul_assoc, hN,
      zero_mul, map_zero, LinearMap.zero_apply]
  have hsqR : ∀ a, ((((φR a : W ≃ₗ[K] W) : W →ₗ[K] W) - 1) ^ 2) = 0 := by
    intro a
    have h1 : ∀ w, (((φR a : W ≃ₗ[K] W) : W →ₗ[K] W) - 1) w =
        ψ.symm (ψ w * (!![1, Multiplicative.toAdd a; 0, 1] - 1)) := by
      intro w
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, hφR, mul_sub, mul_one,
        map_sub, LinearEquiv.symm_apply_apply]
    have hN : (!![1, Multiplicative.toAdd a; 0, 1] - 1) *
        (!![1, Multiplicative.toAdd a; 0, 1] - 1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    refine LinearMap.ext fun w => ?_
    rw [pow_two, Module.End.mul_apply, h1, h1, LinearEquiv.apply_symm_apply, mul_assoc, hN,
      mul_zero, map_zero, LinearMap.zero_apply]
  have hinjL : Function.Injective φL := by
    intro a b h
    have h1 := congrArg (fun g : W ≃ₗ[K] W => ψ (g (ψ.symm 1))) h
    simp only [hφL, LinearEquiv.apply_symm_apply, mul_one] at h1
    have := congrFun (congrFun h1 0) 1
    simpa using this
  have hinjR : Function.Injective φR := by
    intro a b h
    have h1 := congrArg (fun g : W ≃ₗ[K] W => ψ (g (ψ.symm 1))) h
    simp only [hφR, LinearEquiv.apply_symm_apply, one_mul] at h1
    have := congrFun (congrFun h1 0) 1
    simpa using this
  constructor
  · refine key φL _ (fun a => ⟨_, ⟨_, ⟨slUp (Multiplicative.toAdd a), rfl⟩, rfl⟩, rfl⟩) hinjL
      hsqL fun a ha => ?_
    refine ⟨((e.symm (specialRho (A', 1)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      W ≃ₗ[K] W), ⟨_, ⟨_, ⟨A', rfl⟩, rfl⟩, rfl⟩, fun h => ?_⟩
    have h1 := congrArg (fun g : W ≃ₗ[K] W => ψ (g (ψ.symm 1))) h
    simp only [LinearEquiv.mul_apply, hφL, hact, specialRho_apply, LinearEquiv.apply_symm_apply,
      mul_one, inv_one, Matrix.SpecialLinearGroup.coe_one] at h1
    have ha' : Multiplicative.toAdd a ≠ 0 := fun h0 =>
      ha (Multiplicative.toAdd.injective (by rw [h0, toAdd_one]))
    exact hmatL _ ha' h1
  · refine key φR _ (fun a => ⟨_, ⟨_, ⟨slUp (-Multiplicative.toAdd a), rfl⟩, rfl⟩, rfl⟩) hinjR
      hsqR fun a ha => ?_
    refine ⟨((e.symm (specialRho (1, A'⁻¹)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      W ≃ₗ[K] W), ⟨_, ⟨_, ⟨A'⁻¹, rfl⟩, rfl⟩, rfl⟩, fun h => ?_⟩
    have h1 := congrArg (fun g : W ≃ₗ[K] W => ψ (g (ψ.symm 1))) h
    simp only [LinearEquiv.mul_apply, hφR, hact, specialRho_apply, LinearEquiv.apply_symm_apply,
      one_mul, inv_inv, Matrix.SpecialLinearGroup.coe_one] at h1
    have ha' : Multiplicative.toAdd a ≠ 0 := fun h0 =>
      ha (Multiplicative.toAdd.injective (by rw [h0, toAdd_one]))
    exact hmatL _ ha' h1.symm

end Split

section Normal

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

open CFSG.LocalAnalysis.ComponentInitial

private theorem not_isQuasisimple_of_comm' {G : Type*} [Group G] (h : ∀ a b : G, a * b = b * a) :
    ¬ CFSG.IsQuasisimple G := by
  rintro ⟨-, -, a, b, hab⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem orthBlockThree_of_normal_quasisimple [CharP K 3] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ finrank K W) (hnexc : ¬ SmallFixedException Q)
    (hS2 : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ y ∈ S, Q y = 0)
    {L : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)} (hLq : CFSG.IsQuasisimple ↥L)
    (hLle : L ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLn : (L.subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))).Normal) :
    OrthBlockThree (L.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_char_three
  by_cases hs : finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ y ∈ S, Q y = 0
  ·
    have hK : ¬ (Nat.card K = 2 ∨ Nat.card K = 3) := fun h => hnexc (Or.inr ⟨hs, h⟩)
    push Not at hK
    have hK9 : 9 ≤ Nat.card K := by
      haveI := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K 3
      have hn' : Nat.card K = 3 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
      have hn2 : 2 ≤ (n : ℕ) := by
        by_contra hlt
        exact hK.2 (by rw [hn', show (n : ℕ) = 1 by have := n.pos; omega, pow_one])
      rw [hn']
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨ψ, e, -, he, hsup, hLq', hRq', hLn', hRn', -, -, -⟩ :=
      orthogonal_split_four_derived hK.1 hK.2 Q hQ hs.1 hs.2
    haveI : Finite W := Module.finite_of_finite K
    haveI : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
    set Lf := (determinantLeftFactor K).map e.symm.toMonoidHom with hLf
    set Rf := (determinantRightFactor K).map e.symm.toMonoidHom with hRf
    have hLfC : Lf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [hsup]
      exact le_sup_left
    have hRfC : Rf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [hsup]
      exact le_sup_right
    have hF : ∀ i, CFSG.Open.IsComponentOf (![Lf, Rf] i)
        (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
      intro i
      fin_cases i
      · exact ⟨hLfC, CFSG.Open.IsSubnormal.step hLfC hLn' (CFSG.Open.IsSubnormal.refl _),
          CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hLq'⟩
      · exact ⟨hRfC, CFSG.Open.IsSubnormal.step hRfC hRn' (CFSG.Open.IsSubnormal.refl _),
          CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hRq'⟩
    have hperf : ∀ P : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
        P ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) → commutator ↥P = ⊤ →
        P ≤ ⨆ i, ![Lf, Rf] i := by
      intro P hP _
      refine hP.trans (hsup.le.trans (sup_le ?_ ?_))
      · exact le_iSup (fun i => ![Lf, Rf] i) 0
      · exact le_iSup (fun i => ![Lf, Rf] i) 1
    have hLc : CFSG.Open.IsComponentOf L (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :=
      ⟨hLle, CFSG.Open.IsSubnormal.step hLle hLn (CFSG.Open.IsSubnormal.refl _),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hLq⟩
    obtain ⟨i, hi⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors _ hF hperf hLc
    obtain ⟨hcL, hcR⟩ := orthBlockThree_split_factors hK9 ψ e he
    fin_cases i
    · rw [hi]
      exact hcL
    · rw [hi]
      exact hcR
  ·
    have hC := orthogonal_regular_space_derived_quasisimple Q hQ h3 hnexc hs
    have hLC : L = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hC hLn with h | h
      · exact le_antisymm hLle (Subgroup.subgroupOf_eq_top.1 h)
      · exfalso
        refine not_isQuasisimple_of_comm' (fun a b => ?_) hLq
        have ha : (⟨a.1, hLle a.2⟩ : ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))) ∈
            L.subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :=
          Subgroup.mem_subgroupOf.2 a.2
        have hc := Subgroup.mem_center_iff.1 (h ha) ⟨b.1, hLle b.2⟩
        exact Subtype.ext (congrArg Subtype.val hc).symm
    have h5 : 5 ≤ finrank K W := by
      obtain ⟨S, hS2', hSQ⟩ := hS2
      have := CFSG.ComponentClassification.UnbalancedCatalog.two_mul_finrank_le_of_singular hQ hSQ
      by_contra hlt
      exact hs ⟨by omega, S, hS2', hSQ⟩
    obtain ⟨D⟩ := exists_orthHeisData h2 hQ h5 hS2
    rw [hLC, Subgroup.map_subtype_commutator]
    exact orthBlockThree_heis hQ h3 D

end Normal

section Fixed

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

open Polynomial CFSG.RankThree.PartOne.KCPrimary

theorem orthBlockThree_of_fixedFactor [CharP K 3] (hx : OddOrderIsometry Q p x)
    (hlist : FixedLayerListed Q x)
    (hS2 : ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
      ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) : OrthBlockThree F := by
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  have hFB : F ≤ supportedBlock Q x (X - 1) :=
    hFle.trans supportedFixedDerived_le_supportedBlock
  have hCB : ∀ g : ↥(supportedBlock Q x (X - 1)), (g : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x →
      g ∈ commutator ↥(supportedBlock Q x (X - 1)) := by
    intro g hg
    rw [← hSFD] at hg
    obtain ⟨g', hg', hgg⟩ := hg
    rwa [show g = g' from Subtype.ext hgg.symm]
  have hmapC : (commutator ↥(supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      (MonoidHom.range_eq_top (f := (fixedBlockEquiv hx).toMonoidHom)).2
        (fixedBlockEquiv hx).surjective]
  set L : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    (F.subgroupOf (supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom with hL
  have hLle : L ≤
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hmapC]
    exact ⟨g, hCB g (hFle hg), rfl⟩
  have hLn : (L.subgroupOf (commutator
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLle]
    rintro _ k ⟨g, hg, rfl⟩ hk
    rw [← hmapC] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    refine ⟨c * g * c⁻¹, ?_, by simp⟩
    have hcS : (c : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x := hSFD ▸ ⟨c, hc, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hFle).1 hFn _ _ hg hcS
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hFB).symm.trans
      ((F.subgroupOf (supportedBlock Q x (X - 1))).equivMapOfInjective
        (fixedBlockEquiv hx).toMonoidHom (fixedBlockEquiv hx).injective)) hFq
  obtain ⟨PW, hPWL, hPW3, hPW9, hPWZ, hPWq⟩ := orthBlockThree_of_normal_quasisimple
    hx.polarBilin_fixed_nondegenerate hlist.1 hlist.2 hS2 hLq hLle hLn
  let O := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)
  have hPWO : PW ≤ O := hPWL.trans (Subgroup.map_subtype_le _)
  let ι : ↥O →* (V ≃ₗ[K] V) :=
    (supportedBlock Q x (X - 1)).subtype.comp (fixedBlockEquiv hx).symm.toMonoidHom
  have hιinj : Function.Injective ι :=
    (supportedBlock Q x (X - 1)).subtype_injective.comp (fixedBlockEquiv hx).symm.injective
  have hιact : ∀ (y : ↥O) (w : fixedSpace x), ι y (w : V) = (((y : fixedSpace x ≃ₗ[K]
      fixedSpace x) w : fixedSpace x) : V) := by
    intro y w
    have h1 := coe_fixedBlockEquiv hx ((fixedBlockEquiv hx).symm y) w
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hιoth : ∀ (y : ↥O) (r : V), r ∈ othersSpace x.toLinearMap (X - 1) → ι y r = r :=
    fun y r hr => (mem_supportedBlock.mp ((fixedBlockEquiv hx).symm y).2).2 r hr
  have hιF : ∀ y : ↥O, (y : fixedSpace x ≃ₗ[K] fixedSpace x) ∈
      L.map O.subtype → ι y ∈ F := by
    rintro y ⟨y', ⟨g, hg, rfl⟩, hy'⟩
    have hy : y = (fixedBlockEquiv hx).toMonoidHom g := Subtype.ext hy'.symm
    rw [hy]
    change (((fixedBlockEquiv hx).symm ((fixedBlockEquiv hx) g) :
      ↥(supportedBlock Q x (X - 1))) : V ≃ₗ[K] V) ∈ F
    rw [MulEquiv.symm_apply_apply]
    exact hg
  have hFι : ∀ g ∈ F, ∃ y : ↥O, (y : fixedSpace x ≃ₗ[K] fixedSpace x) ∈ L.map O.subtype ∧
      ι y = g := by
    intro g hg
    refine ⟨(fixedBlockEquiv hx) ⟨g, hFB hg⟩, ⟨_, ⟨⟨g, hFB hg⟩, hg, rfl⟩, rfl⟩, ?_⟩
    change (((fixedBlockEquiv hx).symm ((fixedBlockEquiv hx) ⟨g, hFB hg⟩) :
      ↥(supportedBlock Q x (X - 1))) : V ≃ₗ[K] V) = g
    rw [MulEquiv.symm_apply_apply]
  refine ⟨(PW.subgroupOf O).map ι, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hιF y (hPWL (Subgroup.mem_subgroupOf.1 hy))
  · exact (hPW3.of_equiv (Subgroup.subgroupOfEquivOfLe hPWO).symm).map ι
  · rw [Subgroup.card_map_of_injective hιinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPWO).toEquiv]
    exact hPW9
  · rintro _ ⟨y, hy, rfl⟩ hcomm
    have hy1 : (y : fixedSpace x ≃ₗ[K] fixedSpace x) = 1 := by
      refine hPWZ _ (Subgroup.mem_subgroupOf.1 hy) fun j hj => ?_
      have hjO : j ∈ O := Subgroup.map_subtype_le _ hj
      have h1 := hcomm (ι ⟨j, hjO⟩) (hιF ⟨j, hjO⟩ hj)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hιinj h1)
    rw [show y = 1 from Subtype.ext hy1, map_one]
  · rintro _ ⟨y, hy, rfl⟩ hcent hcube
    have hyP : (y : fixedSpace x ≃ₗ[K] fixedSpace x) ∈ PW := Subgroup.mem_subgroupOf.1 hy
    have hcent' : ∀ w ∈ PW, (y : fixedSpace x ≃ₗ[K] fixedSpace x) * w = w * y := by
      intro w hw
      have h1 := hcent (ι ⟨w, hPWO hw⟩) ⟨⟨w, hPWO hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hιinj h1)
    have hcube' : (y : fixedSpace x ≃ₗ[K] fixedSpace x) ^ 3 = 1 := by
      have h1 : ι (y ^ 3) = ι 1 := by rw [map_pow, hcube, map_one]
      rw [← Subgroup.coe_pow, hιinj h1, Subgroup.coe_one]
    have hq := hPWq _ hyP hcent' hcube'
    have hNW : ∀ w : fixedSpace x, ((((ι y : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) (w : V)) =
        (((((y : fixedSpace x ≃ₗ[K] fixedSpace x) : fixedSpace x →ₗ[K] fixedSpace x) - 1) w :
          fixedSpace x) : V) := by
      intro w
      rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
        LinearEquiv.coe_coe, LinearEquiv.coe_coe, Submodule.coe_sub, hιact]
    obtain ⟨hc, -⟩ := hx.fixed_others
    ext v
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
    have hr0 : (((ι y : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) r = 0 := by
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, hιoth y r hr, Module.End.one_apply, sub_self]
    have hw0 : (((((ι y : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ^ 2 : V →ₗ[K] V) w) = 0 := by
      have h1 := congrArg (fun f => (f ⟨w, hw⟩ : V)) hq
      simp only [pow_two, Module.End.mul_apply, LinearMap.zero_apply, Submodule.coe_zero] at h1
      rw [pow_two, Module.End.mul_apply]
      change (((ι y : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ((((ι y : V ≃ₗ[K] V) : V →ₗ[K] V) - 1)
        ((⟨w, hw⟩ : fixedSpace x) : V)) = 0
      rw [hNW, hNW]
      exact h1
    rw [map_add, hw0, pow_two, Module.End.mul_apply, hr0, map_zero, zero_add,
      LinearMap.zero_apply]

end Fixed

end CFSG.LocalAnalysis.GLTheoremA.S2019
