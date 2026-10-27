module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailMixedCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryOpposite
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}

section XY

theorem finrank_prod_bot (W : Submodule K (Fin r ⊕ Fin r → K)) :
    finrank K (W.prod (⊥ : Submodule K A)) = finrank K W := by
  rw [← Submodule.map_inl]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ LinearMap.inl_injective W)).symm

theorem finrank_xSpan_tail : finrank K ((flag r K r).prod (⊥ : Submodule K A)) = r := by
  rw [finrank_prod_bot, finrank_flag le_rfl]

theorem finrank_ySpan_tail : finrank K ((ySpan r K).prod (⊥ : Submodule K A)) = r := by
  rw [finrank_prod_bot, finrank_ySpan]

theorem xSpan_inf_ySpan_tail :
    (flag r K r).prod (⊥ : Submodule K A) ⊓ (ySpan r K).prod (⊥ : Submodule K A) = ⊥ := by
  rw [Submodule.prod_inf_prod, flag_top_inf_ySpan, inf_idem, Submodule.prod_bot]

theorem polarImage₂_inf_eq_bot [FiniteDimensional K A] {q₁ q₂ : QuadraticForm K A}
    (h₁ : IsInfOfMax (quadTail r q₁)) (h₂ : IsInfOfMax (quadTail r q₂))
    (φ : Points (quadTail r q₁) ≃ Points (quadTail r q₂))
    (hφ : ∀ L M : Points (quadTail r q₁),
      PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val) :
    polarImage₂ φ ((flag r K r).prod ⊥) ⊓ polarImage₂ φ ((ySpan r K).prod ⊥) = ⊥ := by
  have hXs : ∀ x ∈ (flag r K r).prod (⊥ : Submodule K A), quadTail r q₁ x = 0 :=
    fun _ hx => quadTail_eq_zero_of_mem_xSpan hx
  have hYs : ∀ x ∈ (ySpan r K).prod (⊥ : Submodule K A), quadTail r q₁ x = 0 :=
    fun _ hx => quadTail_eq_zero_of_mem_ySpan hx
  have hX₁ := totSing_polarImage₂ φ hφ hXs
  have hY₁ := totSing_polarImage₂ φ hφ hYs
  have hZs : ∀ v ∈ polarImage₂ φ ((flag r K r).prod ⊥) ⊓ polarImage₂ φ ((ySpan r K).prod ⊥),
      quadTail r q₂ v = 0 := fun v hv => hX₁ v hv.1
  have hφ' := polarOrtho_symm_iff₂ φ hφ
  have h1 : polarImage₂ φ.symm (polarImage₂ φ ((flag r K r).prod ⊥) ⊓
      polarImage₂ φ ((ySpan r K).prod ⊥)) ≤ (flag r K r).prod ⊥ :=
    le_of_le_of_eq ((polarImage₂_le_iff φ.symm hφ' h₂ hZs hX₁).2 inf_le_left)
      (polarImage₂_symm_polarImage₂ φ hφ h₁ hXs)
  have h2 : polarImage₂ φ.symm (polarImage₂ φ ((flag r K r).prod ⊥) ⊓
      polarImage₂ φ ((ySpan r K).prod ⊥)) ≤ (ySpan r K).prod ⊥ :=
    le_of_le_of_eq ((polarImage₂_le_iff φ.symm hφ' h₂ hZs hY₁).2 inf_le_right)
      (polarImage₂_symm_polarImage₂ φ hφ h₁ hYs)
  have h0 : polarImage₂ φ.symm (polarImage₂ φ ((flag r K r).prod ⊥) ⊓
      polarImage₂ φ ((ySpan r K).prod ⊥)) = ⊥ := by
    rw [eq_bot_iff, ← xSpan_inf_ySpan_tail (A := A)]
    exact le_inf h1 h2
  have hd := finrank_polarImage₂ φ.symm hφ' h₂ h₁ hZs
  rw [h0, finrank_bot] at hd
  exact Submodule.finrank_eq_zero.1 hd.symm

end XY

section Coordinates

variable [FiniteDimensional K A] {qA : QuadraticForm K A}

theorem mem_of_forall_polar_eq_zero (hani : qA.Anisotropic)
    {Y : Submodule K ((Fin r ⊕ Fin r → K) × A)} (hYs : ∀ y ∈ Y, quadTail r qA y = 0)
    (hYd : finrank K Y = r) {x : (Fin r ⊕ Fin r → K) × A} (hx : quadTail r qA x = 0)
    (hxY : ∀ y ∈ Y, polar (quadTail r qA) x y = 0) : x ∈ Y := by
  by_contra hxn
  have hx0 : x ≠ 0 := fun h => hxn (h ▸ Y.zero_mem)
  have hdisj : Y ⊓ span K {x} = ⊥ := by
    refine eq_bot_iff.2 fun z ⟨hzY, hzx⟩ => (mem_bot K).2 ?_
    obtain ⟨t, rfl⟩ := mem_span_singleton.1 hzx
    by_cases ht : t = 0
    · rw [ht, zero_smul]
    · exact absurd (by simpa [smul_smul, inv_mul_cancel₀ ht] using Y.smul_mem t⁻¹ hzY) hxn
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Y (span K {x})
  rw [hdisj, finrank_bot, add_zero, hYd, finrank_span_singleton hx0] at hsum
  have hsing : ∀ z ∈ Y ⊔ span K {x}, quadTail r qA z = 0 := by
    intro z hz
    rw [← Y.span_eq, ← span_union] at hz
    refine map_eq_zero_of_mem_span ?_ ?_ hz
    · rintro u (hu | hu)
      · exact hYs u hu
      · rw [Set.mem_singleton_iff.1 hu]
        exact hx
    · rintro u (hu | hu) w (hw | hw)
      · exact polar_eq_zero_of_singular hYs hu hw
      · rw [Set.mem_singleton_iff.1 hw, polar_comm]
        exact hxY u hu
      · rw [Set.mem_singleton_iff.1 hu]
        exact hxY w hw
      · rw [Set.mem_singleton_iff.1 hu, Set.mem_singleton_iff.1 hw]
        exact polar_self_eq_zero hx
  have := finrank_le_of_totSing_tail hani hsing
  omega

theorem span_range_basis_coe {V : Type*} [AddCommGroup V] [Module K V] {W : Submodule K V}
    {ι : Type*} (b : Basis ι K W) : span K (Set.range fun i => (b i : V)) = W := by
  rw [show (Set.range fun i => (b i : V)) = W.subtype '' Set.range b by
    rw [← Set.range_comp]; rfl, ← Submodule.map_span, b.span_eq, Submodule.map_top,
    Submodule.range_subtype]

theorem exists_tail_coordinates (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    {X₁ Y₁ : Submodule K ((Fin r ⊕ Fin r → K) × A)} (hX₁s : ∀ x ∈ X₁, quadTail r qA x = 0)
    (hY₁s : ∀ y ∈ Y₁, quadTail r qA y = 0) (hX₁d : finrank K X₁ = r)
    (hY₁d : finrank K Y₁ = r) (hXY : X₁ ⊓ Y₁ = ⊥) :
    ∃ (q₂ : QuadraticForm K A)
      (T₀ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)),
      q₂.Anisotropic ∧ (polarBilin q₂).Nondegenerate ∧
      (∀ v, quadTail r qA (T₀ v) = quadTail r q₂ v) ∧
      ((flag r K r).prod ⊥).map (T₀ : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = X₁ ∧
      ((ySpan r K).prod ⊥).map (T₀ : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = Y₁ := by
  have hYperp : ∀ y ∈ Y₁, (∀ x ∈ X₁, polar (quadTail r qA) x y = 0) → y = 0 := by
    intro y hy h
    have hyX : y ∈ X₁ := mem_of_forall_polar_eq_zero hani hX₁s hX₁d (hY₁s y hy) fun x hx => by
      rw [polar_comm]
      exact h x hx
    have hm : y ∈ X₁ ⊓ Y₁ := ⟨hyX, hy⟩
    rw [hXY] at hm
    exact (mem_bot K).1 hm
  obtain ⟨P, hPX, hPY, hPef, hspanX⟩ : ∃ P : Fin r → HypPair (quadTail r qA),
      (∀ i, (P i).e ∈ X₁) ∧ (∀ i, (P i).f ∈ Y₁) ∧
      (∀ i j, polar (quadTail r qA) (P i).e (P j).f = if i = j then 1 else 0) ∧
      span K (Set.range fun i => (P i).e) = X₁ := by
    obtain ⟨b⟩ : Nonempty (Basis (Fin r) K X₁) := ⟨Module.finBasisOfFinrankEq K X₁ hX₁d⟩
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Y₁ →ₗ[K] (Fin r → K),
        ∀ y i, ψ y i = polar (quadTail r qA) (b i : (Fin r ⊕ Fin r → K) × A) y :=
      ⟨LinearMap.pi fun i => (polarBilin (quadTail r qA) (b i)).comp Y₁.subtype,
        fun y i => rfl⟩
    have hψinj : Function.Injective ψ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      have h : ∀ x ∈ X₁, polar (quadTail r qA) x y = 0 := by
        intro x hx
        rw [← span_range_basis_coe b] at hx
        refine polar_eq_zero_of_mem_span_left ?_ hx
        rintro _ ⟨i, rfl⟩
        have := congrFun hy i
        rwa [hψ] at this
      exact Subtype.ext (hYperp y y.2 h)
    have hψbij : Function.Bijective ψ := ⟨hψinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [hY₁d, Module.finrank_fin_fun])).1 hψinj⟩
    have hef : ∀ i j, polar (quadTail r qA) (b i : (Fin r ⊕ Fin r → K) × A)
        ((LinearEquiv.ofBijective ψ hψbij).symm (Pi.single j 1) : (Fin r ⊕ Fin r → K) × A) =
          if i = j then 1 else 0 := by
      intro i j
      have h := congrFun ((LinearEquiv.ofBijective ψ hψbij).apply_symm_apply (Pi.single j 1)) i
      rw [LinearEquiv.ofBijective_apply, hψ] at h
      rw [h, Pi.single_apply]
    refine ⟨fun i => ⟨b i, (LinearEquiv.ofBijective ψ hψbij).symm (Pi.single i 1),
      hX₁s _ (b i).2, hY₁s _ ((LinearEquiv.ofBijective ψ hψbij).symm _).2,
      by rw [hef, ite_eq_left rfl]⟩, fun i => (b i).2,
      fun i => ((LinearEquiv.ofBijective ψ hψbij).symm _).2, fun i j => hef i j,
      span_range_basis_coe b⟩
  have hPo : ∀ i j, i ≠ j → (P i).Orth (P j) := fun i j hij =>
    ⟨polar_eq_zero_of_singular hX₁s (hPX i) (hPX j), by rw [hPef, ite_eq_right hij], by
      rw [polar_comm, hPef, ite_eq_right (Ne.symm hij)],
      polar_eq_zero_of_singular hY₁s (hPY i) (hPY j)⟩
  have hQ := nondegenerate_polarBilin_quadTail (r := r) hreg
  have hA'd : finrank K (pairsPerp P) = finrank K A := by
    have h := finrank_pairsPerp hPo hQ
    rw [finrank_tailSpace] at h
    omega
  have hXspan : X₁ ≤ pairsSpan P := by
    rw [← hspanX, span_le]
    rintro _ ⟨i, rfl⟩
    exact subset_span (Or.inl ⟨i, rfl⟩)
  have hA'ani : ∀ x ∈ pairsPerp P, quadTail r qA x = 0 → x = 0 := by
    intro x hx hQx
    have hxX : x ∈ X₁ := mem_of_forall_polar_eq_zero hani hX₁s hX₁d hQx fun y hy => by
      rw [← hspanX] at hy
      rw [polar_comm]
      refine polar_eq_zero_of_mem_span_left ?_ hy
      rintro _ ⟨i, rfl⟩
      exact (HypPair.mem_perp.1 ((mem_pairsPerp P).1 hx i)).1
    have hm : x ∈ pairsSpan P ⊓ pairsPerp P := ⟨hXspan hxX, hx⟩
    rw [pairsSpan_inf_pairsPerp hPo hQ] at hm
    exact (mem_bot K).1 hm
  have hA'nd : PolarNondegOn (quadTail r qA) (pairsPerp P) := polarNondegOn_pairsPerp hPo hQ
  obtain ⟨j, hjA', hjinj, hjsurj⟩ : ∃ j : A →ₗ[K] (Fin r ⊕ Fin r → K) × A,
      (∀ a, j a ∈ pairsPerp P) ∧ Function.Injective j ∧ ∀ y ∈ pairsPerp P, ∃ a, j a = y :=
    ⟨(pairsPerp P).subtype ∘ₗ (LinearEquiv.ofFinrankEq A (pairsPerp P) hA'd.symm).toLinearMap,
      fun a => (LinearEquiv.ofFinrankEq A (pairsPerp P) hA'd.symm a).2,
      fun a b h => (LinearEquiv.ofFinrankEq A (pairsPerp P) hA'd.symm).injective (Subtype.ext h),
      fun y hy => ⟨(LinearEquiv.ofFinrankEq A (pairsPerp P) hA'd.symm).symm ⟨y, hy⟩, by simp⟩⟩
  obtain ⟨q₂, hq₂a⟩ : ∃ q₂ : QuadraticForm K A, ∀ a, q₂ a = quadTail r qA (j a) :=
    ⟨(quadTail r qA).comp j, fun a => rfl⟩
  have hpolq₂ : ∀ a b, polar q₂ a b = polar (quadTail r qA) (j a) (j b) := fun a b => by
    simp only [QuadraticMap.polar, hq₂a, map_add]
  have hq₂ani : q₂.Anisotropic := fun a ha =>
    hjinj ((hA'ani _ (hjA' a) (by rw [← hq₂a]; exact ha)).trans (map_zero j).symm)
  have hq₂reg : (polarBilin q₂).Nondegenerate := by
    refine nondegenerate_polarBilin_of_forall fun a ha => hjinj ?_
    rw [map_zero]
    refine hA'nd _ (hjA' a) fun y hy => ?_
    obtain ⟨c, rfl⟩ := hjsurj y hy
    rw [← hpolq₂]
    exact ha c
  obtain ⟨g, hg⟩ : ∃ g : Fin r ⊕ Fin r → (Fin r ⊕ Fin r → K) × A,
      g = Sum.elim (fun i => (P i).e) (fun i => (P i).f) := ⟨_, rfl⟩
  have hgli : LinearIndependent K g := hg ▸ linearIndependent_pairs hPo
  obtain ⟨T₀l, hT₀lv⟩ : ∃ T₀l : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A),
      ∀ v, T₀l v = ∑ x, v.1 x • g x + j v.2 :=
    ⟨{ toFun := fun v => ∑ x, v.1 x • g x + j v.2
       map_add' := fun v w => by
         simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
           map_add]
         abel
       map_smul' := fun c v => by
         simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, map_smul,
           RingHom.id_apply, smul_add, Finset.smul_sum] }, fun v => rfl⟩
  have hsum_mem : ∀ u : Fin r ⊕ Fin r → K, ∑ x, u x • g x ∈ pairsSpan P := fun u =>
    sum_mem fun x _ => smul_mem _ _ (subset_span (by
      rcases x with i | i
      · exact Or.inl ⟨i, by rw [hg]; rfl⟩
      · exact Or.inr ⟨i, by rw [hg]; rfl⟩))
  have hinj : Function.Injective T₀l := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hT₀lv] at hv
    have h1 : ∑ x, v.1 x • g x ∈ pairsSpan P ⊓ pairsPerp P := by
      refine ⟨hsum_mem v.1, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hv]
      exact neg_mem (hjA' v.2)
    rw [pairsSpan_inf_pairsPerp hPo hQ, mem_bot] at h1
    have hv1 : v.1 = 0 := funext fun x => Fintype.linearIndependent_iff.1 hgli v.1 h1 x
    rw [h1, zero_add] at hv
    have hv2 : v.2 = 0 := hjinj (hv.trans (map_zero j).symm)
    exact Prod.ext hv1 hv2
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A),
      ∀ v, T₀ v = ∑ x, v.1 x • g x + j v.2 :=
    ⟨LinearEquiv.ofBijective T₀l ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩,
      fun v => hT₀lv v⟩
  have hsplit : ∀ u : Fin r ⊕ Fin r → K,
      ∑ x, u x • g x = ∑ i, u (.inl i) • (P i).e + ∑ i, u (.inr i) • (P i).f := fun u => by
    rw [Fintype.sum_sum_type, hg]
    rfl
  have hQT : ∀ v, quadTail r qA (T₀ v) = quadTail r q₂ v := by
    intro v
    have hE : ∑ i, v.1 (.inl i) • (P i).e ∈ X₁ := sum_mem fun i _ => X₁.smul_mem _ (hPX i)
    have hF : ∑ i, v.1 (.inr i) • (P i).f ∈ Y₁ := sum_mem fun i _ => Y₁.smul_mem _ (hPY i)
    have hEF : polar (quadTail r qA) (∑ i, v.1 (.inl i) • (P i).e)
        (∑ i, v.1 (.inr i) • (P i).f) = ∑ i, v.1 (.inl i) * v.1 (.inr i) := by
      rw [polar_sum_smul_left]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [polar_sum_smul_right]
      simp only [hPef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hT₀, QuadraticMap.map_add (quadTail r qA),
      polar_pairsSpan_pairsPerp P (hsum_mem v.1) (hjA' v.2), add_zero, hsplit,
      QuadraticMap.map_add (quadTail r qA), hX₁s _ hE, hY₁s _ hF, hEF, quadTail_apply (qA := q₂),
      quadPlus_apply, hq₂a, zero_add, zero_add]
  have hXmap : ((flag r K r).prod ⊥).map (T₀ : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = X₁ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨hv1, hv2⟩ := Submodule.mem_prod.1 hv
      have hv1' := mem_flag_top_iff.1 hv1
      change T₀ v ∈ X₁
      rw [hT₀, (mem_bot K).1 hv2, map_zero, add_zero, hsplit]
      simp only [hv1', zero_smul, Finset.sum_const_zero, add_zero]
      exact sum_mem fun i _ => X₁.smul_mem _ (hPX i)
    · rw [LinearEquiv.finrank_map_eq, finrank_xSpan_tail, hX₁d]
  have hYmap : ((ySpan r K).prod ⊥).map (T₀ : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = Y₁ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨hv1, hv2⟩ := Submodule.mem_prod.1 hv
      have hv1' := mem_ySpan_iff.1 hv1
      change T₀ v ∈ Y₁
      rw [hT₀, (mem_bot K).1 hv2, map_zero, add_zero, hsplit]
      simp only [hv1', zero_smul, Finset.sum_const_zero, zero_add]
      exact sum_mem fun i _ => Y₁.smul_mem _ (hPY i)
    · rw [LinearEquiv.finrank_map_eq, finrank_ySpan_tail, hY₁d]
  exact ⟨q₂, T₀, hq₂ani, hq₂reg, hQT, hXmap, hYmap⟩

end Coordinates

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
