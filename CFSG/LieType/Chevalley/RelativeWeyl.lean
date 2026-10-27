module

public import CFSG.LieType.Chevalley.WeylSpace
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem RootSpace Matrix
open scoped RealInnerProductSpace

variable {τ : Tag}

@[expose] def fixedSpace (ψ : RootSpace τ ≃ₗᵢ[ℝ] RootSpace τ) : Submodule ℝ (RootSpace τ) where
  carrier := {x | ψ x = x}
  add_mem' {x y} hx hy := by
    have hx' : ψ x = x := hx
    have hy' : ψ y = y := hy
    change ψ (x + y) = x + y
    rw [map_add, hx', hy']
  zero_mem' := map_zero ψ
  smul_mem' c x hx := by
    have hx' : ψ x = x := hx
    change ψ (c • x) = c • x
    rw [map_smul, hx']

theorem mem_fixedSpace {ψ : RootSpace τ ≃ₗᵢ[ℝ] RootSpace τ} {x : RootSpace τ} :
    x ∈ fixedSpace ψ ↔ ψ x = x :=
  Iff.rfl

variable (τ) in
@[expose] def cartanFun (i : Fin τ.rank) (y : RootSpace τ) : ℝ :=
  ∑ l, (τ.cartan i l : ℝ) * y l

theorem inner_single_eq_cartanFun (i : Fin τ.rank) (y : RootSpace τ) :
    ⟪ofLattice (Pi.single i 1), y⟫ =
      (symmetrizer (isFiniteType_cartan τ) i : ℝ) * cartanFun τ i y :=
  inner_ofLattice_single_left i y

theorem inner_single_neg_iff (i : Fin τ.rank) (y : RootSpace τ) :
    ⟪ofLattice (Pi.single i 1), y⟫ < 0 ↔ cartanFun τ i y < 0 := by
  have hd : (0 : ℝ) < symmetrizer (isFiniteType_cartan τ) i :=
    Rat.cast_pos.2 (symmetrizer_pos _ i)
  rw [inner_single_eq_cartanFun]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    nlinarith
  · intro h
    nlinarith

theorem sum_smul_single_apply (m : Fin τ.rank → ℝ) (l : Fin τ.rank) :
    (∑ j, m j • ofLattice (Pi.single j 1 : Fin τ.rank → ℤ)) l = m l := by
  simp [toPi_ofLattice_single, Pi.single_apply]

theorem eq_zero_of_inner_single_eq_zero {v : RootSpace τ}
    (h : ∀ i, ⟪ofLattice (Pi.single i 1), v⟫ = 0) : v = 0 := by
  have hvv : ⟪v, v⟫ = 0 := calc
    ⟪v, v⟫ = ⟪∑ i, v i • ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), v⟫ := by
      rw [sum_smul_ofLattice_single]
    _ = 0 := by
      rw [sum_inner]
      exact Finset.sum_eq_zero fun i _ => by rw [real_inner_smul_left, h, mul_zero]
  exact inner_self_eq_zero.1 hvv

variable (τ) in
@[expose] def wordCoeff : List (Fin τ.rank) → Fin τ.rank → Fin τ.rank → ℤ
  | [] => fun _ _ => 0
  | i :: ω => fun j k =>
    if j = i then
      wordCoeff ω i k + (if k = i then 1 else 0) - ∑ l, τ.cartan i l * wordCoeff ω l k
    else wordCoeff ω j k

theorem cartanFun_sum_smul_single (i : Fin τ.rank) (m : Fin τ.rank → ℝ) :
    cartanFun τ i (∑ j, m j • ofLattice (Pi.single j 1 : Fin τ.rank → ℤ)) =
      ∑ l, (τ.cartan i l : ℝ) * m l := by
  simp only [cartanFun, sum_smul_single_apply]

theorem cartanFun_sub (i : Fin τ.rank) (x y : RootSpace τ) :
    cartanFun τ i (x - y) = cartanFun τ i x - cartanFun τ i y := by
  simp only [cartanFun, toPi_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem weylAct_wordProd (ω : List (Fin τ.rank)) (y : RootSpace τ) :
    weylAct τ ((coxeterSystem τ).wordProd ω) y =
      y - ∑ j, (∑ k, (wordCoeff τ ω j k : ℝ) * cartanFun τ k y) •
        ofLattice (Pi.single j 1 : Fin τ.rank → ℤ) := by
  induction ω with
  | nil => simp [wordCoeff]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, weylAct_mul_apply, ih, weylAct_simple]
    set m : Fin τ.rank → ℝ := fun j => ∑ k, (wordCoeff τ ω j k : ℝ) * cartanFun τ k y with hm
    have hcx : (∑ j, (τ.cartan i j : ℝ) *
        (y - ∑ j, m j • ofLattice (Pi.single j 1 : Fin τ.rank → ℤ)) j) =
        cartanFun τ i y - ∑ l, (τ.cartan i l : ℝ) * m l := by
      change cartanFun τ i (y - _) = _
      rw [cartanFun_sub, cartanFun_sum_smul_single]
    rw [hcx, sub_sub, sub_right_inj]
    ext l
    rw [toPi_add, Pi.add_apply, sum_smul_single_apply, sum_smul_single_apply, toPi_smul,
      toPi_ofLattice_single]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hl : l = i
    · subst hl
      simp only [↓reduceIte, wordCoeff]
      have e1 : ∀ k, ((wordCoeff τ ω l k + (if k = l then 1 else 0) -
          ∑ l', τ.cartan l l' * wordCoeff τ ω l' k : ℤ) : ℝ) * cartanFun τ k y =
          (wordCoeff τ ω l k : ℝ) * cartanFun τ k y + (if k = l then cartanFun τ k y else 0) -
            ∑ l', (τ.cartan l l' : ℝ) * ((wordCoeff τ ω l' k : ℝ) * cartanFun τ k y) := by
        intro k
        push_cast
        rw [sub_mul, add_mul, Finset.sum_mul]
        congr 1
        · split_ifs <;> simp
        · exact Finset.sum_congr rfl fun l' _ => mul_assoc _ _ _
      rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      rw [Finset.sum_comm]
      simp only [hm, Finset.mul_sum]
      ring
    · simp only [hl, ↓reduceIte, add_zero, wordCoeff]

theorem inner_weylAct_wordProd (ω : List (Fin τ.rank)) (y v : RootSpace τ) :
    ⟪weylAct τ ((coxeterSystem τ).wordProd ω) y, v⟫ =
      ⟪y, v⟫ - ∑ j, (∑ k, (wordCoeff τ ω j k : ℝ) * cartanFun τ k y) *
        ⟪ofLattice (Pi.single j 1), v⟫ := by
  rw [weylAct_wordProd, inner_sub_left, sum_inner]
  simp only [real_inner_smul_left]

theorem lt_inner_weylAct_wordProd {ω : List (Fin τ.rank)} {J : Finset (Fin τ.rank)}
    (hM : ∀ j k, 0 ≤ wordCoeff τ ω j k) (hJ : ∀ j k, wordCoeff τ ω j k ≠ 0 → k ∈ J)
    (hne : ∃ j k, wordCoeff τ ω j k ≠ 0) {y v : RootSpace τ}
    (hy : ∀ k ∈ J, cartanFun τ k y < 0) (hv : v ∈ openDominantCone τ) :
    ⟪y, v⟫ < ⟪weylAct τ ((coxeterSystem τ).wordProd ω) y, v⟫ := by
  rw [inner_weylAct_wordProd]
  have hterm : ∀ j k, (wordCoeff τ ω j k : ℝ) * cartanFun τ k y ≤ 0 := by
    intro j k
    by_cases h0 : wordCoeff τ ω j k = 0
    · rw [h0, Int.cast_zero, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hM j k) (hy k (hJ j k h0)).le
  have hrow : ∀ j, ∑ k, (wordCoeff τ ω j k : ℝ) * cartanFun τ k y ≤ 0 := fun j =>
    Finset.sum_nonpos fun k _ => hterm j k
  obtain ⟨j₀, k₀, h₀⟩ := hne
  have hrow₀ : ∑ k, (wordCoeff τ ω j₀ k : ℝ) * cartanFun τ k y < 0 := by
    refine Finset.sum_neg' (fun k _ => hterm j₀ k) ⟨k₀, Finset.mem_univ _, ?_⟩
    exact mul_neg_of_pos_of_neg
      (by exact_mod_cast lt_of_le_of_ne (hM j₀ k₀) (Ne.symm h₀)) (hy k₀ (hJ j₀ k₀ h₀))
  have hsum : ∑ j, (∑ k, (wordCoeff τ ω j k : ℝ) * cartanFun τ k y) *
      ⟪ofLattice (Pi.single j 1), v⟫ < 0 :=
    Finset.sum_neg' (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hrow j) (hv j).le)
      ⟨j₀, Finset.mem_univ _, mul_neg_of_neg_of_pos hrow₀ (hv j₀)⟩
  linarith

variable {ψ : RootSpace τ ≃ₗᵢ[ℝ] RootSpace τ} {π : Equiv.Perm (Fin τ.rank)}
  {c : Fin τ.rank → ℝ}

theorem inner_single_of_mem_fixedSpace
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1))
    {y : RootSpace τ} (hy : y ∈ fixedSpace ψ) (i : Fin τ.rank) :
    ⟪ofLattice (Pi.single i 1), y⟫ = c i * ⟪ofLattice (Pi.single (π i) 1), y⟫ := by
  rw [← LinearIsometryEquiv.inner_map_map ψ, hψ, mem_fixedSpace.1 hy, real_inner_smul_left]

theorem inner_single_pow_neg (hc : ∀ i, 0 < c i)
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1))
    {y : RootSpace τ} (hy : y ∈ fixedSpace ψ) {i : Fin τ.rank}
    (hi : ⟪ofLattice (Pi.single i 1), y⟫ < 0) (m : ℕ) :
    ⟪ofLattice (Pi.single ((π ^ m) i) 1), y⟫ < 0 := by
  induction m with
  | zero => simpa using hi
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    have h := inner_single_of_mem_fixedSpace hψ hy ((π ^ m) i)
    have hcm := hc ((π ^ m) i)
    by_contra hge
    push Not at hge
    rw [h] at ih
    nlinarith

theorem exists_mem_dominantCone_of_improve (W' : Subgroup (WeylGroup τ))
    (hW' : ∀ w ∈ W', ∀ x ∈ fixedSpace ψ, weylAct τ w x ∈ fixedSpace ψ) (v₀ : RootSpace τ)
    (himp : ∀ y ∈ fixedSpace ψ, y ∉ dominantCone τ →
      ∃ w ∈ W', ⟪y, v₀⟫ < ⟪weylAct τ w y, v₀⟫)
    {x : RootSpace τ} (hx : x ∈ fixedSpace ψ) :
    ∃ w ∈ W', ∃ y ∈ fixedSpace ψ, y ∈ dominantCone τ ∧ x = weylAct τ w y := by
  obtain ⟨u, hu⟩ := Finite.exists_max fun u : W' => ⟪weylAct τ u x, v₀⟫
  have hyE : weylAct τ u x ∈ fixedSpace ψ := hW' u u.2 x hx
  refine ⟨(u : WeylGroup τ)⁻¹, inv_mem u.2, weylAct τ u x, hyE, ?_, ?_⟩
  · by_contra hD
    obtain ⟨w, hw, hlt⟩ := himp _ hyE hD
    have := hu ⟨w * u, mul_mem hw u.2⟩
    change ⟪weylAct τ (w * u) x, v₀⟫ ≤ _ at this
    rw [weylAct_mul_apply] at this
    linarith
  · rw [← weylAct_mul_apply, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]

theorem eq_zero_of_improve (W' : Subgroup (WeylGroup τ)) (v₀ : RootSpace τ)
    (himp : ∀ y ∈ fixedSpace ψ, y ∉ dominantCone τ →
      ∃ w ∈ W', ⟪y, v₀⟫ < ⟪weylAct τ w y, v₀⟫)
    {v : RootSpace τ} (hv : v ∈ fixedSpace ψ) (hfix : ∀ w ∈ W', weylAct τ w v = v) : v = 0 := by
  have hD : ∀ y ∈ fixedSpace ψ, (∀ w ∈ W', weylAct τ w y = y) → y ∈ dominantCone τ := by
    intro y hy hfy
    by_contra hD
    obtain ⟨w, hw, hlt⟩ := himp y hy hD
    rw [hfy w hw] at hlt
    exact lt_irrefl _ hlt
  have h₁ := hD v hv hfix
  have h₂ := hD (-v) (neg_mem hv) fun w hw => by rw [map_neg, hfix w hw]
  refine eq_zero_of_inner_single_eq_zero fun i => le_antisymm ?_ (h₁ i)
  have := h₂ i
  rw [inner_neg_right] at this
  linarith

theorem exists_improve_of_words (hc : ∀ i, 0 < c i)
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1))
    (W' : Subgroup (WeylGroup τ)) {v₀ : RootSpace τ} (hv₀ : v₀ ∈ openDominantCone τ)
    (word : Fin τ.rank → List (Fin τ.rank))
    (hword : ∀ i, (coxeterSystem τ).wordProd (word i) ∈ W')
    (hM : ∀ i j k, 0 ≤ wordCoeff τ (word i) j k)
    (hJ : ∀ i j k, wordCoeff τ (word i) j k ≠ 0 → ∃ m ∈ List.range 6, (π ^ m) i = k)
    (hne : ∀ i, ∃ j k, wordCoeff τ (word i) j k ≠ 0) :
    ∀ y ∈ fixedSpace ψ, y ∉ dominantCone τ → ∃ w ∈ W', ⟪y, v₀⟫ < ⟪weylAct τ w y, v₀⟫ := by
  classical
  intro y hy hD
  obtain ⟨i, hi⟩ : ∃ i, ⟪ofLattice (Pi.single i 1), y⟫ < 0 := by
    by_contra h
    push Not at h
    exact hD h
  refine ⟨_, hword i, lt_inner_weylAct_wordProd (J := ((List.range 6).map fun m => (π ^ m) i).toFinset)
    (hM i) (fun j k hjk => ?_) (hne i) (fun k hk => ?_) hv₀⟩
  · obtain ⟨m, hm, rfl⟩ := hJ i j k hjk
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨m, hm, rfl⟩)
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hk)
    exact (inner_single_neg_iff _ _).1 (inner_single_pow_neg hc hψ hy hi m)

@[expose] noncomputable def graphLinear (π : Equiv.Perm (Fin τ.rank)) (c : Fin τ.rank → ℝ) :
    RootSpace τ →ₗ[ℝ] RootSpace τ where
  toFun x := ofPi fun l => c (π.symm l) * x (π.symm l)
  map_add' x y := by
    ext l
    simp only [toPi_add, Pi.add_apply, mul_add]
  map_smul' r x := by
    ext l
    simp only [toPi_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem graphLinear_apply (x : RootSpace τ) (l : Fin τ.rank) :
    graphLinear π c x l = c (π.symm l) * x (π.symm l) :=
  rfl

@[expose] noncomputable def graphLinearInv (π : Equiv.Perm (Fin τ.rank)) (c : Fin τ.rank → ℝ) :
    RootSpace τ →ₗ[ℝ] RootSpace τ where
  toFun y := ofPi fun k => y (π k) / c k
  map_add' x y := by
    ext l
    simp only [toPi_add, Pi.add_apply, add_div]
  map_smul' r x := by
    ext l
    simp only [toPi_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[expose] noncomputable def graphIsometry (π : Equiv.Perm (Fin τ.rank)) (c : Fin τ.rank → ℝ)
    (hc : ∀ i, c i ≠ 0)
    (hform : ∀ i j, c i * c j * formMatrix τ (π i) (π j) = formMatrix τ i j) :
    RootSpace τ ≃ₗᵢ[ℝ] RootSpace τ :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofLinearMap (graphLinear π c) (graphLinearInv π c)
      (LinearMap.ext fun y => by
        ext l
        change c (π.symm l) * (y (π (π.symm l)) / c (π.symm l)) = y l
        rw [Equiv.apply_symm_apply]
        field_simp [hc (π.symm l)])
      (LinearMap.ext fun x => by
        ext k
        change c (π.symm (π k)) * x (π.symm (π k)) / c k = x k
        rw [Equiv.symm_apply_apply]
        field_simp [hc k]))
    (fun x y => by
      change (graphLinear π c x).toPi ⬝ᵥ (formMatrix τ *ᵥ (graphLinear π c y).toPi) =
        x.toPi ⬝ᵥ (formMatrix τ *ᵥ y.toPi)
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      rw [← Equiv.sum_comp π]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Equiv.sum_comp π]
      refine Finset.sum_congr rfl fun j _ => ?_
      change c (π.symm (π i)) * x (π.symm (π i)) *
          (formMatrix τ (π i) (π j) * (c (π.symm (π j)) * y (π.symm (π j)))) =
        x i * (formMatrix τ i j * y j)
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hform i j]
      ring)

theorem graphIsometry_apply (hc : ∀ i, c i ≠ 0)
    (hform : ∀ i j, c i * c j * formMatrix τ (π i) (π j) = formMatrix τ i j)
    (x : RootSpace τ) (l : Fin τ.rank) :
    graphIsometry π c hc hform x l = c (π.symm l) * x (π.symm l) :=
  rfl

theorem graphIsometry_single (hc : ∀ i, c i ≠ 0)
    (hform : ∀ i j, c i * c j * formMatrix τ (π i) (π j) = formMatrix τ i j) (i : Fin τ.rank) :
    graphIsometry π c hc hform (ofLattice (Pi.single i 1)) =
      c i • ofLattice (Pi.single (π i) 1) := by
  ext l
  change c (π.symm l) * (ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)).toPi (π.symm l) =
    (c i • ofLattice (Pi.single (π i) 1 : Fin τ.rank → ℤ)).toPi l
  rw [toPi_smul, toPi_ofLattice_single, toPi_ofLattice_single]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, Equiv.symm_apply_eq]
  split_ifs with h
  · rw [h, Equiv.symm_apply_apply]
  · simp

theorem exists_formMatrix_eq (τ : Tag) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ i j, formMatrix τ i j =
      κ * ((τ.symmetrizer i i : ℤ) : ℝ) * ((τ.cartan i j : ℤ) : ℝ) := by
  obtain ⟨κ, hκ, hd⟩ := exists_symmetrizer_eq τ
  refine ⟨κ, Rat.cast_pos.2 hκ, fun i j => ?_⟩
  rw [formMatrix_apply, hd]
  push_cast
  ring

theorem symm_single (hc : ∀ i, 0 < c i)
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1))
    (j : Fin τ.rank) :
    ψ.symm (ofLattice (Pi.single j 1)) =
      (c (π.symm j))⁻¹ • ofLattice (Pi.single (π.symm j) 1) := by
  have h := hψ (π.symm j)
  rw [Equiv.apply_symm_apply] at h
  have h' : ψ ((c (π.symm j))⁻¹ • ofLattice (Pi.single (π.symm j) 1)) =
      ofLattice (Pi.single j 1) := by
    rw [map_smul, h, smul_smul, inv_mul_cancel₀ (hc _).ne', one_smul]
  rw [← h', LinearIsometryEquiv.symm_apply_apply]

theorem inner_single_map (hc : ∀ i, 0 < c i)
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1))
    (j : Fin τ.rank) (y : RootSpace τ) :
    ⟪ofLattice (Pi.single j 1), ψ y⟫ =
      (c (π.symm j))⁻¹ * ⟪ofLattice (Pi.single (π.symm j) 1), y⟫ := by
  conv_lhs => rw [← LinearIsometryEquiv.apply_symm_apply ψ (ofLattice (Pi.single j 1))]
  rw [LinearIsometryEquiv.inner_map_map, symm_single hc hψ, real_inner_smul_left]

theorem pow_heightVector_mem_openDominantCone (hc : ∀ i, 0 < c i)
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1)) (k : ℕ) :
    (ψ ^ k) (heightVector τ) ∈ openDominantCone τ := by
  induction k with
  | zero =>
    intro j
    rw [pow_zero, LinearIsometryEquiv.coe_one, id, inner_ofLattice_heightVector, height_single,
      Int.cast_one]
    exact one_pos
  | succ k ih =>
    intro j
    rw [pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply, inner_single_map hc hψ]
    exact mul_pos (inv_pos.2 (hc _)) (ih _)

@[expose] noncomputable def sumPowHeight (ψ : RootSpace τ ≃ₗᵢ[ℝ] RootSpace τ) (n : ℕ) :
    RootSpace τ :=
  ∑ k ∈ Finset.range n, (ψ ^ k) (heightVector τ)

theorem sumPowHeight_mem_fixedSpace {n : ℕ} (hn : ψ ^ n = 1) :
    sumPowHeight ψ n ∈ fixedSpace ψ := by
  rw [mem_fixedSpace, sumPowHeight, map_sum]
  have h : ∀ k, ψ ((ψ ^ k) (heightVector τ)) = (ψ ^ (k + 1)) (heightVector τ) := fun k => by
    rw [pow_succ']
    rfl
  simp only [h]
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ, hn, Finset.sum_range_succ']
    simp only [pow_zero, LinearIsometryEquiv.coe_one, id, add_comm]

theorem sumPowHeight_mem_openDominantCone (hc : ∀ i, 0 < c i)
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1)) {n : ℕ}
    (hn : 1 ≤ n) : sumPowHeight ψ n ∈ openDominantCone τ := by
  intro j
  rw [sumPowHeight, inner_sum]
  exact Finset.sum_pos (fun k _ => pow_heightVector_mem_openDominantCone hc hψ k j)
    ⟨0, Finset.mem_range.2 hn⟩

end CFSG.LieType.Chevalley
