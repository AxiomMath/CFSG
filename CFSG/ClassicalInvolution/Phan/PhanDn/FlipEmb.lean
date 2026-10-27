module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipflopPoints

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {k n : ℕ}

theorem flipOrth_antitone {U U' : Submodule K (Fin n ⊕ Fin n → K)} (h : U ≤ U') :
    flipOrth σ U' ≤ flipOrth σ U := by
  intro v hv
  rw [mem_flipOrth] at hv ⊢
  exact fun u hu => hv u (h hu)

private theorem polar_stdF (u : Fin n ⊕ Fin n → K) (i : Fin n) :
    polar (quadPlus n K) u (stdF (K := K) i) = u (.inl i) := by
  rw [polar_quadPlus, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [stdF, hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem polar_stdE (u : Fin n ⊕ Fin n → K) (i : Fin n) :
    polar (quadPlus n K) u (stdE (K := K) i) = u (.inr i) := by
  rw [polar_quadPlus, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [stdE, hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem polar_stdF_left (u : Fin n ⊕ Fin n → K) (i : Fin n) :
    polar (quadPlus n K) (stdF (K := K) i) u = u (.inl i) := by
  rw [polar_comm]
  exact polar_stdF u i

private theorem polar_stdE_left (u : Fin n ⊕ Fin n → K) (i : Fin n) :
    polar (quadPlus n K) (stdE (K := K) i) u = u (.inr i) := by
  rw [polar_comm]
  exact polar_stdE u i

private theorem dFlip_finset_sum {ι : Type*} (s : Finset ι) (a : ι → K)
    (u : ι → Fin n ⊕ Fin n → K) :
    dFlip σ (∑ i ∈ s, a i • u i) = ∑ i ∈ s, σ (a i) • dFlip σ (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    ext x
    cases x <;> simp [dFlip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, dFlip_add, dFlip_smul, ih]

private theorem flipHerm_finset_sum_left {ι : Type*} (s : Finset ι) (a : ι → K)
    (u : ι → Fin n ⊕ Fin n → K) (v : Fin n ⊕ Fin n → K) :
    flipHerm σ (∑ i ∈ s, a i • u i) v = ∑ i ∈ s, a i * flipHerm σ (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, flipHerm_add_left, flipHerm_smul_left, ih]

private theorem flipHerm_finset_sum_right {ι : Type*} (s : Finset ι)
    (u : Fin n ⊕ Fin n → K) (a : ι → K) (v : ι → Fin n ⊕ Fin n → K) :
    flipHerm σ u (∑ i ∈ s, a i • v i) = ∑ i ∈ s, σ (a i) * flipHerm σ u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, flipHerm_add_right, flipHerm_smul_right, ih]

private theorem quadPlus_sum_smul_eq_zero {ι : Type*} [Fintype ι]
    (v : ι → (Fin n ⊕ Fin n → K)) (hq : ∀ i, quadPlus n K (v i) = 0)
    (hB : ∀ i j, i ≠ j → polar (quadPlus n K) (v i) (v j) = 0) (a : ι → K) :
    quadPlus n K (∑ i, a i • v i) = 0 := by
  classical
  have h : ∀ s : Finset ι, quadPlus n K (∑ i ∈ s, a i • v i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, QuadraticMap.map_add (quadPlus n K)]
      have hQi : quadPlus n K (a i • v i) = 0 := by
        rw [QuadraticMap.map_smul, smul_eq_mul, hq i, mul_zero]
      have hsum : polar (quadPlus n K) (v i) (∑ j ∈ s, a j • v j) = 0 := by
        have hmap : polar (quadPlus n K) (v i) (∑ j ∈ s, a j • v j) =
            ∑ j ∈ s, polar (quadPlus n K) (v i) (a j • v j) := by
          change (quadPlus n K).polarBilin (v i) (∑ j ∈ s, a j • v j) =
            ∑ j ∈ s, (quadPlus n K).polarBilin (v i) (a j • v j)
          rw [map_sum]
        rw [hmap]
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [QuadraticMap.polar_smul_right, hB i j (fun h => hi (by simpa [h] using hj)),
          smul_zero]
      have hpolar : polar (quadPlus n K) (a i • v i) (∑ j ∈ s, a j • v j) = 0 := by
        rw [QuadraticMap.polar_smul_left, hsum, smul_zero]
      rw [hQi, ih, hpolar, add_zero, add_zero]
  exact h Finset.univ

variable (σ k n) in
structure FlipEmb where
  toLinearMap : (Fin k ⊕ Fin k → K) →ₗ[K] (Fin n ⊕ Fin n → K)
  quadPlus_apply : ∀ x, quadPlus n K (toLinearMap x) = quadPlus k K x
  dFlip_apply : ∀ x, toLinearMap (dFlip σ x) = dFlip σ (toLinearMap x)

namespace FlipEmb

variable (φ : FlipEmb σ k n)

theorem polar_apply (x y : Fin k ⊕ Fin k → K) :
    polar (quadPlus n K) (φ.toLinearMap x) (φ.toLinearMap y) = polar (quadPlus k K) x y := by
  simp only [polar, ← map_add, φ.quadPlus_apply]

theorem flipHerm_apply (x y : Fin k ⊕ Fin k → K) :
    flipHerm σ (φ.toLinearMap x) (φ.toLinearMap y) = flipHerm σ x y := by
  rw [flipHerm, flipHerm, ← φ.dFlip_apply y]
  exact φ.polar_apply x (dFlip σ y)

theorem injective : Function.Injective φ.toLinearMap := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  funext p
  cases p with
  | inl i =>
      have h := φ.polar_apply x (stdF (K := K) i)
      rw [hx, polar_zero_left, polar_stdF] at h
      exact h.symm
  | inr i =>
      have h := φ.polar_apply x (stdE (K := K) i)
      rw [hx, polar_zero_left, polar_stdE] at h
      exact h.symm

theorem finrank_map (U : Submodule K (Fin k ⊕ Fin k → K)) :
    Module.finrank K (U.map φ.toLinearMap) = Module.finrank K U :=
  (Submodule.equivMapOfInjective φ.toLinearMap φ.injective U).finrank_eq.symm

theorem isFlipflopSub_map {U : Submodule K (Fin k ⊕ Fin k → K)} (hU : IsFlipflopSub σ U) :
    IsFlipflopSub σ (U.map φ.toLinearMap) where
  total u hu := by
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    rw [φ.quadPlus_apply, hU.total v hv]
  nondeg u hu hper := by
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    have hv0 : v = 0 := by
      refine hU.nondeg v hv fun w hw => ?_
      have h := hper (φ.toLinearMap w) (Submodule.mem_map_of_mem hw)
      rwa [φ.flipHerm_apply] at h
    rw [hv0, map_zero]

theorem isFlipflopPt_map {p : Submodule K (Fin k ⊕ Fin k → K)} (hp : IsFlipflopPt σ p) :
    IsFlipflopPt σ (p.map φ.toLinearMap) := by
  obtain ⟨v, rfl, hq, hh⟩ := hp.exists_eq_span
  have hv : v ≠ 0 := fun h => hh (by rw [h, flipHerm_zero_right])
  rw [Submodule.map_span, Set.image_singleton]
  refine (isFlipflopPt_span_singleton_iff (σ := σ) (v := φ.toLinearMap v) ?_).mpr
    ⟨?_, ?_⟩
  · intro h
    exact hv (φ.injective (by simpa using h))
  · rw [φ.quadPlus_apply, hq]
  · rw [φ.flipHerm_apply]
    exact hh

theorem exists_isFlipflopSub_map_eq {U : Submodule K (Fin n ⊕ Fin n → K)}
    (hU : IsFlipflopSub σ U) (hle : U ≤ LinearMap.range φ.toLinearMap) :
    ∃ U₀ : Submodule K (Fin k ⊕ Fin k → K), IsFlipflopSub σ U₀ ∧ U₀.map φ.toLinearMap = U := by
  refine ⟨U.comap φ.toLinearMap, ⟨fun u hu => ?_, ?_⟩, ?_⟩
  · rw [← φ.quadPlus_apply u]
    exact hU.total (φ.toLinearMap u) hu
  · intro u hu hper
    have hper' : ∀ w ∈ U, flipHerm σ (φ.toLinearMap u) w = 0 := by
      intro w hw
      obtain ⟨w₀, rfl⟩ := LinearMap.mem_range.mp (hle hw)
      have hw₀ : w₀ ∈ U.comap φ.toLinearMap := hw
      have h1 := hper w₀ hw₀
      rw [φ.flipHerm_apply]
      exact h1
    have h0 : φ.toLinearMap u = 0 := hU.nondeg _ hu hper'
    exact φ.injective (by simpa using h0)
  · exact Submodule.map_comap_eq_self hle

private noncomputable def adjointCoeff (φ : FlipEmb σ k n) (y : Fin n ⊕ Fin n → K) :
    Fin k ⊕ Fin k → K := fun p =>
  match p with
  | .inl i => polar (quadPlus n K) (φ.toLinearMap (stdF (K := K) i)) y
  | .inr i => polar (quadPlus n K) (φ.toLinearMap (stdE (K := K) i)) y

private theorem polar_adjointCoeff (φ : FlipEmb σ k n) (y : Fin n ⊕ Fin n → K)
    (x : Fin k ⊕ Fin k → K) :
    polar (quadPlus k K) x (φ.adjointCoeff y) = polar (quadPlus n K) (φ.toLinearMap x) y := by
  let L₁ : (Fin k ⊕ Fin k → K) →ₗ[K] K :=
    LinearMap.flip ((quadPlus k K).polarBilin) (φ.adjointCoeff y)
  let L₂ : (Fin k ⊕ Fin k → K) →ₗ[K] K :=
    (LinearMap.flip ((quadPlus n K).polarBilin) y).comp φ.toLinearMap
  have hL : L₁ = L₂ := by
    refine (Pi.basisFun K (Fin k ⊕ Fin k)).ext fun i => ?_
    cases i with
    | inl i =>
        rw [Pi.basisFun_apply]
        change L₁ (stdE (K := K) i) = L₂ (stdE (K := K) i)
        simp only [L₁, L₂, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply,
          LinearMap.comp_apply, adjointCoeff, polar_stdE_left]
    | inr i =>
        rw [Pi.basisFun_apply]
        change L₁ (stdF (K := K) i) = L₂ (stdF (K := K) i)
        simp only [L₁, L₂, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply,
          LinearMap.comp_apply, adjointCoeff, polar_stdF_left]
  have h := congrArg (fun L : (Fin k ⊕ Fin k → K) →ₗ[K] K => L x) hL
  simpa only [L₁, L₂, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply,
    LinearMap.comp_apply] using h

theorem exists_adjoint (hσ : ∀ x, σ (σ x) = x) (y : Fin n ⊕ Fin n → K) :
    ∃ f : Fin k ⊕ Fin k → K, ∀ x, polar (quadPlus n K) (φ.toLinearMap x) y =
      polar (quadPlus k K) x f ∧ flipHerm σ (φ.toLinearMap x) y = flipHerm σ x f := by
  refine ⟨φ.adjointCoeff y, fun x => ⟨(φ.polar_adjointCoeff y x).symm, ?_⟩⟩
  have h1 : σ (flipHerm σ (φ.toLinearMap x) y) = σ (flipHerm σ x (φ.adjointCoeff y)) := by
    rw [flipHerm, flipHerm,
      ← polar_dFlip (u := φ.toLinearMap x) (v := dFlip σ y), dFlip_dFlip hσ,
      ← φ.dFlip_apply x, ← φ.polar_adjointCoeff y (dFlip σ x),
      ← polar_dFlip (u := x) (v := dFlip σ (φ.adjointCoeff y)),
      dFlip_dFlip hσ]
  exact σ.injective h1

end FlipEmb

theorem IsFlipflopSub.exists_isFlipflopPt_orth_of_lt (hσ : IsUnitaryInvolution σ)
    {Y : Submodule K (Fin n ⊕ Fin n → K)} (hY : IsFlipflopSub σ Y)
    (hd : Module.finrank K Y < n) :
    ∃ p, IsFlipflopPt σ p ∧ p ≤ qPerp n K Y ∧ p ≤ flipOrth σ Y := by
  obtain ⟨M, -, hM, -, hYM, -, -, -⟩ := hY.exists_solid_le hσ hd
  let W : Submodule K (Fin n ⊕ Fin n → K) := M ⊓ flipOrth σ Y
  have hYW : Y ⊓ W = ⊥ := by
    refine le_bot_iff.mp (le_trans (inf_le_inf_left Y inf_le_right) ?_)
    rw [inf_flipOrth_eq_bot hσ.invol hY]
  have hdimW : Module.finrank K W + Module.finrank K Y = n := by
    simpa only [W, hM.2] using IsFlipflopSub.finrank_inf_flipOrth hσ.invol hM.1 hYM
  have hsup : Y ⊔ W = M := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Y W
    rw [hYW, finrank_bot, add_zero] at h
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hYM inf_le_left) ?_
    rw [h, hM.2]
    omega
  have hWs : IsFlipflopSub σ W :=
    { total := fun w hw => hM.1.total w hw.1
      nondeg := fun w hw hper => by
        refine hM.1.nondeg w hw.1 fun m hm => ?_
        have hm' : m ∈ Y ⊔ W := by rw [hsup]; exact hm
        obtain ⟨y, hy, w', hw', rfl⟩ := Submodule.mem_sup.mp hm'
        have hyw : flipHerm σ w y = 0 :=
          (flipHerm_eq_zero_iff hσ.invol).mpr ((mem_flipOrth.mp hw.2) y hy)
        rw [flipHerm_add_right, hyw, hper w' hw', add_zero] }
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdimW
    omega
  obtain ⟨p, hp, hpW⟩ := hWs.exists_isFlipflopPt_le hσ hWne
  have hMq : M ≤ qPerp n K Y := by
    intro m hm
    rw [mem_qPerp]
    intro y hy
    have h := QuadraticMap.map_add (quadPlus n K) y m
    rw [hM.1.total (y + m) (M.add_mem (hYM hy) hm), hM.1.total y (hYM hy),
      hM.1.total m hm] at h
    simpa using h.symm
  exact ⟨p, hp, hpW.trans (inf_le_left.trans hMq), hpW.trans inf_le_right⟩

private theorem linearCombination_preserves_quadPlus (hσ : ∀ x, σ (σ x) = x)
    (v : Fin k → (Fin n ⊕ Fin n → K)) (hq : ∀ i, quadPlus n K (v i) = 0)
    (hh : ∀ i, flipHerm σ (v i) (v i) = 1)
    (horth : ∀ i j, i ≠ j → flipHerm σ (v i) (v j) = 0)
    (hB : ∀ i j, i ≠ j → polar (quadPlus n K) (v i) (v j) = 0)
    (y : Fin k ⊕ Fin k → K) :
    quadPlus n K (Fintype.linearCombination K (Sum.elim v (fun i => dFlip σ (v i))) y)
      = quadPlus k K y := by
  classical
  let w : Fin k ⊕ Fin k → (Fin n ⊕ Fin n → K) := Sum.elim v (fun i => dFlip σ (v i))
  let a : Fin k → K := fun i => y (Sum.inl i)
  let b : Fin k → K := fun i => y (Sum.inr i)
  let A : Fin n ⊕ Fin n → K := ∑ i, a i • v i
  let A' : Fin n ⊕ Fin n → K := ∑ i, σ (b i) • v i
  have hL : Fintype.linearCombination K w y = A + dFlip σ A' := by
    rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
    have h1 : (∑ i, y (Sum.inl i) • w (Sum.inl i)) = A := rfl
    have h2 : (∑ i, y (Sum.inr i) • w (Sum.inr i)) = dFlip σ A' := by
      rw [dFlip_finset_sum]
      simp only [hσ, w, Sum.elim_inr, b]
    rw [h1, h2]
  have hQA : quadPlus n K A = 0 :=
    quadPlus_sum_smul_eq_zero v hq hB a
  have hQA' : quadPlus n K A' = 0 :=
    quadPlus_sum_smul_eq_zero v hq hB (fun i => σ (b i))
  have hQB : quadPlus n K (dFlip σ A') = 0 := by
    rw [quadPlus_dFlip, hQA', map_zero]
  have hAB : polar (quadPlus n K) A (dFlip σ A') = ∑ i, a i * b i := by
    show flipHerm σ A A' = ∑ i, a i * b i
    rw [show A' = ∑ i, σ (b i) • v i from rfl, flipHerm_finset_sum_right]
    have h1 : ∀ i, flipHerm σ A (v i) = a i := by
      intro i
      rw [show A = ∑ j, a j • v j from rfl, flipHerm_finset_sum_left,
        Finset.sum_eq_single i]
      · simp [hh i]
      · intro j _ hji
        rw [horth j i hji, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [Finset.sum_congr rfl fun i _ => by rw [hσ, h1 i]]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hL, QuadraticMap.map_add (quadPlus n K), hQA, hQB, hAB, quadPlus_apply]
  simp [a, b]

private theorem linearCombination_dFlip (hσ : ∀ x, σ (σ x) = x)
    (w : Fin k ⊕ Fin k → (Fin n ⊕ Fin n → K))
    (hw : ∀ i, w (Sum.inr i) = dFlip σ (w (Sum.inl i))) (y : Fin k ⊕ Fin k → K) :
    Fintype.linearCombination K w (dFlip σ y) = dFlip σ (Fintype.linearCombination K w y) := by
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, dFlip_finset_sum]
  conv_lhs => rw [Fintype.sum_sum_type]
  conv_rhs => rw [Fintype.sum_sum_type]
  simp only [dFlip_apply_inl, dFlip_apply_inr, hw, dFlip_dFlip hσ]
  rw [add_comm]

private theorem exists_gen_of_isFlipflopPt (hσ : IsUnitaryInvolution σ)
    {p : Submodule K (Fin n ⊕ Fin n → K)} (hp : IsFlipflopPt σ p) :
    ∃ v ∈ p, quadPlus n K v = 0 ∧ flipHerm σ v v = 1 ∧ p = K ∙ v := by
  obtain ⟨u, hu, hq, hh⟩ := hp.exists_eq_span
  have hfix : σ (flipHerm σ u u) = flipHerm σ u u := flipHerm_self_mem_fixed hσ.invol u
  have hfixinv : σ ((flipHerm σ u u)⁻¹) = (flipHerm σ u u)⁻¹ := by
    rw [map_inv₀, hfix]
  obtain ⟨c, hc⟩ := hσ.norm_surj ((flipHerm σ u u)⁻¹) hfixinv (inv_ne_zero hh)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hc
    exact inv_ne_zero hh hc.symm
  have hQv : quadPlus n K (c • u) = 0 := by
    rw [QuadraticMap.map_smul, smul_eq_mul, hq, mul_zero]
  have hvv : flipHerm σ (c • u) (c • u) = 1 := by
    rw [flipHerm_smul_left, flipHerm_smul_right, ← mul_assoc, mul_comm c (σ c), hc,
      inv_mul_cancel₀ hh]
  have hline : p = K ∙ (c • u) := by
    rw [hu, ← Submodule.span_singleton_smul_eq hc0.isUnit u]
  exact ⟨c • u, hline ▸ Submodule.mem_span_singleton_self _, hQv, hvv, hline⟩

theorem exists_flipEmb_of_orth (hσ : IsUnitaryInvolution σ)
    (z : Fin k → Submodule K (Fin n ⊕ Fin n → K)) (hz : ∀ i, IsFlipflopPt σ (z i))
    (hB : ∀ i j, i ≠ j → ∀ u ∈ z i, ∀ v ∈ z j, polar (quadPlus n K) u v = 0)
    (hH : ∀ i j, i ≠ j → ∀ u ∈ z i, ∀ v ∈ z j, flipHerm σ u v = 0) :
    ∃ φ : FlipEmb σ k n, (∀ i, (K ∙ stdE (K := K) i).map φ.toLinearMap = z i) ∧
      LinearMap.range φ.toLinearMap = ⨆ i, (z i ⊔ dFlipSub σ (z i)) := by
  classical
  choose v hv using fun i => exists_gen_of_isFlipflopPt hσ (hz i)
  have hvmem : ∀ i, v i ∈ z i := fun i => (hv i).1
  have hq : ∀ i, quadPlus n K (v i) = 0 := fun i => (hv i).2.1
  have hh : ∀ i, flipHerm σ (v i) (v i) = 1 := fun i => (hv i).2.2.1
  have hline : ∀ i, z i = K ∙ v i := fun i => (hv i).2.2.2
  let w : Fin k ⊕ Fin k → (Fin n ⊕ Fin n → K) := Sum.elim v (fun i => dFlip σ (v i))
  let Llin : (Fin k ⊕ Fin k → K) →ₗ[K] (Fin n ⊕ Fin n → K) := Fintype.linearCombination K w
  have hw : ∀ i, w (Sum.inr i) = dFlip σ (w (Sum.inl i)) := by
    intro i
    simp [w]
  have hL_Q : ∀ y, quadPlus n K (Llin y) = quadPlus k K y := fun y =>
    linearCombination_preserves_quadPlus hσ.invol v hq hh
      (fun i j hij => hH i j hij (v i) (hvmem i) (v j) (hvmem j))
      (fun i j hij => hB i j hij (v i) (hvmem i) (v j) (hvmem j)) y
  have hL_flip : ∀ y, Llin (dFlip σ y) = dFlip σ (Llin y) := fun y =>
    linearCombination_dFlip hσ.invol w hw y
  refine ⟨⟨Llin, hL_Q, hL_flip⟩, ?_, ?_⟩
  · intro i
    rw [Submodule.map_span, Set.image_singleton]
    have hstd : Llin (stdE (K := K) i) = v i := by
      change Fintype.linearCombination K w (Pi.single (Sum.inl i) (1 : K)) = v i
      rw [Fintype.linearCombination_apply_single, one_smul]
      rfl
    rw [hstd]
    exact (hline i).symm
  · change LinearMap.range
      (Fintype.linearCombination K (Sum.elim v (fun i => dFlip σ (v i)))) = _
    have hterm : ∀ i, z i ⊔ dFlipSub σ (z i) = K ∙ v i ⊔ K ∙ dFlip σ (v i) := by
      intro i
      rw [hline i, dFlipSub_span_singleton]
    rw [Fintype.range_linearCombination, Set.Sum.elim_range, Submodule.span_union,
      Submodule.span_range_eq_iSup, Submodule.span_range_eq_iSup, ← iSup_sup_eq]
    exact iSup_congr fun i => (hterm i).symm

private theorem iSup_fin_cons {α : Type*} [CompleteLattice α] {j : ℕ} (q : α)
    (p : Fin j → α) : ⨆ i : Fin (j+1), Fin.cons q p i = q ⊔ ⨆ i : Fin j, p i := by
  let p' : Fin (j+1) → α := Fin.cons q p
  have hp'eq : p' = Fin.cons q p := rfl
  change ⨆ i, p' i = q ⊔ ⨆ i : Fin j, p i
  refine le_antisymm (iSup_le fun i => ?_) ?_
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · exact le_sup_left
    · exact le_sup_of_le_right (le_iSup p i)
  · refine sup_le ?_ ?_
    · exact le_iSup p' 0
    · refine iSup_le fun i => ?_
      exact le_iSup p' i.succ

private theorem exists_orthogonal_points_succ (hσ : IsUnitaryInvolution σ)
    {X : Submodule K (Fin n ⊕ Fin n → K)} {k : ℕ} {p : Fin k → Submodule K (Fin n ⊕ Fin n → K)}
    (hp : ∀ i, IsFlipflopPt σ (p i))
    (hpp : ∀ i i', i ≠ i' → ∀ u ∈ p i, ∀ v ∈ p i',
      polar (quadPlus n K) u v = 0 ∧ flipHerm σ u v = 0)
    (hpX : ∀ i, ∀ v ∈ p i, ∀ u ∈ X,
      polar (quadPlus n K) u v = 0 ∧ flipHerm σ u v = 0)
    (hY : IsFlipflopSub σ (X ⊔ ⨆ i, p i))
    (hdim : Module.finrank K ↥(X ⊔ ⨆ i, p i) = Module.finrank K X + k)
    (hd : Module.finrank K X + (k+1) ≤ n) :
    ∃ p' : Fin (k+1) → Submodule K (Fin n ⊕ Fin n → K),
      (∀ i, IsFlipflopPt σ (p' i)) ∧
      (∀ i i', i ≠ i' → ∀ u ∈ p' i, ∀ v ∈ p' i',
        polar (quadPlus n K) u v = 0 ∧ flipHerm σ u v = 0) ∧
      (∀ i, ∀ v ∈ p' i, ∀ u ∈ X,
        polar (quadPlus n K) u v = 0 ∧ flipHerm σ u v = 0) ∧
      IsFlipflopSub σ (X ⊔ ⨆ i, p' i) ∧
      Module.finrank K ↥(X ⊔ ⨆ i, p' i) = Module.finrank K X + (k+1) := by
  let Y : Submodule K (Fin n ⊕ Fin n → K) := X ⊔ ⨆ i, p i
  have hlt : Module.finrank K ↥Y < n := by
    rw [show Module.finrank K ↥Y = Module.finrank K X + k from hdim]
    exact Nat.lt_of_succ_le (by rwa [← Nat.add_assoc] at hd)
  obtain ⟨q, hq, hqY, hqfY⟩ := hY.exists_isFlipflopPt_orth_of_lt hσ hlt
  let p' : Fin (k+1) → Submodule K (Fin n ⊕ Fin n → K) := Fin.cons q p
  have hp'eq : p' = Fin.cons q p := rfl
  have hsup : X ⊔ ⨆ i, p' i = q ⊔ Y := by
    rw [hp'eq, iSup_fin_cons, sup_comm X (q ⊔ ⨆ i, p i), sup_assoc,
      sup_comm (⨆ i, p i) X]
  have hqsub : IsFlipflopSub σ q := IsFlipflopPt.isFlipflopSub hq
  have hsupY : IsFlipflopSub σ (q ⊔ Y) :=
    (IsFlipflopSub.sup_of_orth hσ.invol hqsub hY hqY hqfY).1
  have hdisj : Disjoint q Y :=
    (IsFlipflopSub.sup_of_orth hσ.invol hqsub hY hqY hqfY).2
  have hpY : ∀ i, p i ≤ X ⊔ ⨆ i, p i := fun i => le_sup_of_le_right (le_iSup p i)
  refine ⟨p', ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simpa [hp'eq] using hq
    · simpa [hp'eq] using hp i
  · intro i i' hii' u hu v hv
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨i', rfl⟩
      · exact absurd rfl hii'
      · have hu' : u ∈ q := by simpa [hp'eq] using hu
        have hv' : v ∈ p i' := by simpa [hp'eq] using hv
        refine ⟨?_, ?_⟩
        · rw [polar_comm]
          exact (mem_qPerp.mp (hqY hu')) v (hpY i' hv')
        · exact (flipHerm_eq_zero_iff hσ.invol).mpr
            ((mem_flipOrth.mp (hqfY hu')) v (hpY i' hv'))
    · rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨i', rfl⟩
      · have hu' : u ∈ p i := by simpa [hp'eq] using hu
        have hv' : v ∈ q := by simpa [hp'eq] using hv
        exact ⟨(mem_qPerp.mp (hqY hv')) u (hpY i hu'),
          (mem_flipOrth.mp (hqfY hv')) u (hpY i hu')⟩
      · have hu' : u ∈ p i := by simpa [hp'eq] using hu
        have hv' : v ∈ p i' := by simpa [hp'eq] using hv
        exact hpp i i' (by simpa using hii') u hu' v hv'
  · intro i v hv u hu
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have hv' : v ∈ q := by simpa [hp'eq] using hv
      exact ⟨(mem_qPerp.mp (hqY hv')) u (Submodule.mem_sup_left hu),
        (mem_flipOrth.mp (hqfY hv')) u (Submodule.mem_sup_left hu)⟩
    · have hv' : v ∈ p i := by simpa [hp'eq] using hv
      exact hpX i v hv' u hu
  · rw [hsup]
    exact hsupY
  · rw [hsup]
    have h := Submodule.finrank_sup_add_finrank_inf_eq q Y
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    rw [h, IsFlipflopPt.finrank_eq_one hq, hdim]
    ring

private theorem exists_orthogonal_points (hσ : IsUnitaryInvolution σ)
    {X : Submodule K (Fin n ⊕ Fin n → K)} (hX : IsFlipflopSub σ X) :
    ∀ k, Module.finrank K X + k ≤ n →
      ∃ p : Fin k → Submodule K (Fin n ⊕ Fin n → K),
        (∀ i, IsFlipflopPt σ (p i)) ∧
        (∀ i i', i ≠ i' → ∀ u ∈ p i, ∀ v ∈ p i',
          polar (quadPlus n K) u v = 0 ∧ flipHerm σ u v = 0) ∧
        (∀ i, ∀ v ∈ p i, ∀ u ∈ X,
          polar (quadPlus n K) u v = 0 ∧ flipHerm σ u v = 0) ∧
        IsFlipflopSub σ (X ⊔ ⨆ i, p i) ∧
        Module.finrank K ↥(X ⊔ ⨆ i, p i) = Module.finrank K X + k := by
  intro k
  induction k with
  | zero =>
    intro hd
    refine ⟨Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact i.elim0
    · intro i
      exact i.elim0
    · intro i
      exact i.elim0
    · simpa using hX
    · rw [iSup_of_empty, sup_bot_eq]
      simp
  | succ k ih =>
    intro hd
    obtain ⟨p, hp, hpp, hpX, hY, hdim⟩ := ih (by omega)
    exact exists_orthogonal_points_succ hσ hp hpp hpX hY hdim hd

theorem exists_flipEmb_orth (hσ : IsUnitaryInvolution σ) {X : Submodule K (Fin n ⊕ Fin n → K)}
    (hX : IsFlipflopSub σ X) (hd : Module.finrank K X + k ≤ n) :
    ∃ φ : FlipEmb σ k n, ∀ x, ∀ v ∈ X,
      polar (quadPlus n K) v (φ.toLinearMap x) = 0 ∧ flipHerm σ v (φ.toLinearMap x) = 0 := by
  obtain ⟨p, hp, hpp, hpX, -, -⟩ := exists_orthogonal_points hσ hX k hd
  obtain ⟨φ, -, hrange⟩ := exists_flipEmb_of_orth hσ p hp
    (fun i j hij u hu v hv => (hpp i j hij u hu v hv).1)
    (fun i j hij u hu v hv => (hpp i j hij u hu v hv).2)
  have hle_q : (⨆ i, (p i ⊔ dFlipSub σ (p i))) ≤ qPerp n K X := by
    refine iSup_le fun i => sup_le ?_ ?_
    · intro y hy
      rw [mem_qPerp]
      intro u hu
      exact (hpX i y hy u hu).1
    · intro y hy
      rw [mem_qPerp]
      intro u hu
      rw [mem_dFlipSub hσ.invol] at hy
      have h := (hpX i (dFlip σ y) hy u hu).2
      change polar (quadPlus n K) u (dFlip σ (dFlip σ y)) = 0 at h
      rwa [dFlip_dFlip hσ.invol] at h
  have hle_f : (⨆ i, (p i ⊔ dFlipSub σ (p i))) ≤ flipOrth σ X := by
    refine iSup_le fun i => sup_le ?_ ?_
    · intro y hy
      rw [mem_flipOrth]
      intro u hu
      exact (hpX i y hy u hu).2
    · intro y hy
      rw [mem_flipOrth]
      intro u hu
      rw [mem_dFlipSub hσ.invol] at hy
      have h := (hpX i (dFlip σ y) hy u hu).1
      simpa only [flipHerm] using h
  refine ⟨φ, fun x v hv => ?_⟩
  have hmem : φ.toLinearMap x ∈ ⨆ i, (p i ⊔ dFlipSub σ (p i)) := by
    rw [← hrange]
    exact LinearMap.mem_range_self φ.toLinearMap x
  exact ⟨(mem_qPerp.mp (hle_q hmem)) v hv, (mem_flipOrth.mp (hle_f hmem)) v hv⟩

end CFSG.ClassicalInvolution.PhanDn
