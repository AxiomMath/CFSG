module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabTensorOps
public import CFSG.LieType.SeitzGeneration.UnitaryNonabFrame
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorCenters
public import CFSG.LieType.SeitzGeneration.UnitaryNonabTensorWH

public section

namespace CFSG.LieType.SeitzGeneration.HeisP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {σ : K ≃+* K} {n m : ℕ} {p : ℕ} [NeZero p]

theorem herm_pair_two {N : ℕ} {i j : Fin N} (hij : i ≠ j) (x y x' y' : K) :
    herm σ (Pi.single i x + Pi.single j y : Fin N → K) (Pi.single i x' + Pi.single j y') =
      σ x * x' + σ y * y' := by
  simp only [herm_add_left, herm_add_right, herm_single_left, herm_single_right, Pi.add_apply,
    Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm]
  ring

theorem castAdd_ne_natAdd_fin (k l : Fin p) :
    (Fin.castAdd p k : Fin (p + p)) ≠ Fin.natAdd p l := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h'
  have := k.isLt
  omega

theorem natAdd_ne_castAdd_fin (k l : Fin p) :
    (Fin.natAdd p k : Fin (p + p)) ≠ Fin.castAdd p l :=
  fun h => castAdd_ne_natAdd_fin l k h.symm

theorem castAdd_ne_of_le (k : Fin p) (i : Fin (p + p)) (hi : p ≤ (i : ℕ)) :
    (Fin.castAdd p k : Fin (p + p)) ≠ i := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.coe_castAdd] at h'
  have := k.isLt
  omega

theorem natAdd_eq_natAdd_fin (k l : Fin p) :
    (Fin.natAdd p k : Fin (p + p)) = Fin.natAdd p l ↔ k = l :=
  ⟨fun h => Fin.ext (by have h' := congrArg Fin.val h; simp only [Fin.coe_natAdd] at h'; omega),
    fun h => by rw [h]⟩

namespace HeisFrameP

variable {X Y : Matrix (Fin n) (Fin n) K} {α ζ : K} (F : HeisFrameP σ p n m X Y α ζ)

theorem vec_single (ξ : Fin p → K) (r : Fin m) :
    F.vec ξ (Pi.single r 1) = ∑ k, ξ k • F.f k r := by
  have e : ∀ k, F.vecw k (Pi.single r 1) = F.f k r := fun k => by
    simp only [vecw, Pi.single_apply, ite_smul, one_smul, zero_smul]
    simp
  simp only [vec, e]

theorem rho_add_vec {u : Fin m → K} (hu : herm σ u u = 0) (v : Fin n → K) (c : K)
    (η : Fin p → K) : F.rho u (v + c • F.vec η u) = F.rho u v := by
  have e : ∀ w, F.rho u w = F.Ru u *ᵥ w := fun w => (F.Ru_mulVec u w).symm
  rw [e, e v, mulVec_add, mulVec_smul, ← e (F.vec η u), F.rho_vec_self hu, smul_zero, add_zero]

theorem isCenter_vec_of_dec (hσ : IsUnitaryInvolution σ)
    (hdec : ∀ S : Matrix (Fin p) (Fin p) K, (∀ a b, σ (S b a) = S a b) →
      ∃ Q : Fin (p + 1) → Matrix (Fin p) (Fin p) K, (∀ i a b, σ (Q i b a) = Q i a b) ∧
        Q 0 * Zm ζ = Zm ζ * Q 0 ∧ (∀ j : Fin p, Q j.succ * Gj ζ α j = Gj ζ α j * Q j.succ) ∧
        S = ∑ i, Q i)
    {H : Subgroup (SUid σ n)} (hY : HeisTensor.Cent H Y)
    (hX : ∀ j : ℕ, j < p → HeisTensor.Cent H (X * Y ^ j))
    (ξ : Fin p → K) {u : Fin m → K} (hu : herm σ u u = 0) :
    IsCenter H (F.vec ξ u) := by
  have hσi := hσ.invol
  refine ⟨by rw [F.herm_vec_vec, hu, mul_zero], fun c hc => ?_⟩
  set S : Matrix (Fin p) (Fin p) K := Matrix.of fun a b => ξ a * σ (ξ b) with hSdef
  have hS : ∀ a b, σ (S b a) = S a b := fun a b => by
    simp only [hSdef, Matrix.of_apply, map_mul, hσi]
    ring
  obtain ⟨Q, hQσ, hQ0, hQj, hsum⟩ := hdec S hS
  have hmem : ∀ i : Fin (p + 1), F.Mel hσi (hQσ i) hc hu ∈ H := by
    intro i
    induction i using Fin.cases with
    | zero => exact hY _ (F.Mmat_commute hσi F.actY hQ0 c u)
    | succ j => exact hX j j.isLt _ (F.Mmat_commute hσi (F.act_XY_pow j) (hQj j) c u)
  have hstep : ∀ s : Finset (Fin (p + 1)), ∃ g ∈ H, ∀ v : Fin n → K,
      g • v = v + c • F.vec ((∑ i ∈ s, Q i) *ᵥ F.rho u v) u := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, H.one_mem, fun v => by simp [F.vec_zero_left]⟩
    | insert i s hi ih =>
      obtain ⟨g, hg, hgv⟩ := ih
      refine ⟨F.Mel hσi (hQσ i) hc hu * g, H.mul_mem (hmem i) hg, fun v => ?_⟩
      rw [mul_smul, hgv v, F.Mel_smul hσi (hQσ i) hc hu, F.rho_add_vec hu, Finset.sum_insert hi,
        add_mulVec, F.vec_add_left, smul_add]
      abel
  have hSρ : ∀ v : Fin n → K, S *ᵥ F.rho u v = herm σ (F.vec ξ u) v • ξ := fun v => by
    funext a
    simp only [mulVec, dotProduct, hSdef, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
      F.herm_left_vec, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  obtain ⟨g, hg, hgv⟩ := hstep Finset.univ
  rw [← hsum] at hgv
  refine ⟨g, hg, fun v => ?_⟩
  rw [hgv v, hSρ v, F.vec_smul_left, smul_smul]

@[expose] def blk (a b : Fin m) : Fin (p + p) → Fin n → K :=
  Fin.append (fun k => F.f k a) (fun k => F.f k b)

theorem blk_castAdd (a b : Fin m) (k : Fin p) : F.blk a b (Fin.castAdd p k) = F.f k a := by
  simp [blk]

theorem blk_natAdd (a b : Fin m) (k : Fin p) : F.blk a b (Fin.natAdd p k) = F.f k b := by
  simp only [blk, Fin.append_right]

theorem blk_on {a b : Fin m} (hab : a ≠ b) (i j : Fin (p + p)) :
    herm σ (F.blk a b i) (F.blk a b j) = if i = j then 1 else 0 := by
  induction i using Fin.addCases with
  | left k =>
    induction j using Fin.addCases with
    | left l => simp [F.blk_castAdd, F.on]
    | right l =>
      rw [F.blk_castAdd, F.blk_natAdd, F.on, if_neg (castAdd_ne_natAdd_fin k l),
        if_neg (show ¬(k = l ∧ a = b) from fun h => hab h.2)]
  | right k =>
    induction j using Fin.addCases with
    | left l =>
      rw [F.blk_natAdd, F.blk_castAdd, F.on, if_neg (natAdd_ne_castAdd_fin k l),
        if_neg (show ¬(k = l ∧ b = a) from fun h => hab h.2.symm)]
    | right l =>
      rw [F.blk_natAdd, F.blk_natAdd, F.on]
      simp only [natAdd_eq_natAdd_fin, eq_self_iff_true, and_true]

theorem herm_f_blk_of_ne {a b s : Fin m} (hsa : s ≠ a) (hsb : s ≠ b) (l : Fin p)
    (i : Fin (p + p)) : herm σ (F.f l s) (F.blk a b i) = 0 := by
  induction i using Fin.addCases with
  | left k => simp [F.blk_castAdd, F.on, hsa]
  | right k => rw [F.blk_natAdd, F.on, if_neg (show ¬(l = k ∧ s = b) from fun h => hsb h.2)]

theorem eq_zero_of_herm_f (hσ : ∀ c, σ (σ c) = c) {w : Fin n → K}
    (h : ∀ l s, herm σ (F.f l s) w = 0) : w = 0 := by
  refine eq_zero_of_herm σ fun y => ?_
  obtain ⟨c, rfl⟩ := F.span y
  rw [herm_sum_right]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [herm_sum_right]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [herm_smul_right, herm_conj σ hσ, h, map_zero, mul_zero]

@[expose] def Supp (S : Finset (Fin m)) (v : Fin n → K) : Prop :=
  ∀ l s, s ∉ S → herm σ (F.f l s) v = 0

theorem herm_f_phi_of_ne {a b s : Fin m} (hsa : s ≠ a) (hsb : s ≠ b) (l : Fin p)
    (γ : Fin (p + p) → K) : herm σ (F.f l s) (orthoEmb (F.blk a b) γ) = 0 := by
  rw [herm_orthoEmb_right]
  exact Finset.sum_eq_zero fun i _ => by rw [F.herm_f_blk_of_ne hsa hsb, mul_zero]

theorem herm_f_phi_first {a b : Fin m} (hab : a ≠ b) (l : Fin p) {γ : Fin (p + p) → K}
    (h : ∀ i : Fin (p + p), p ≤ (i : ℕ) → γ i = 0) :
    herm σ (F.f l b) (orthoEmb (F.blk a b) γ) = 0 := by
  rw [herm_orthoEmb_right]
  refine Finset.sum_eq_zero fun i _ => ?_
  induction i using Fin.addCases with
  | left k => simp [F.blk_castAdd, F.on, hab.symm]
  | right k => rw [h (Fin.natAdd p k) (by simp), zero_mul]

theorem herm_blk_phi {a b : Fin m} (hab : a ≠ b) (γ : Fin (p + p) → K) (i : Fin (p + p)) :
    herm σ (F.blk a b i) (orthoEmb (F.blk a b) γ) = γ i := by
  rw [herm_orthoEmb_right]
  simp [F.blk_on hab]

theorem exists_blk_a (a b : Fin m) (l : Fin p) : ∃ i : Fin (p + p), F.f l a = F.blk a b i :=
  ⟨Fin.castAdd p l, (F.blk_castAdd a b l).symm⟩

theorem exists_blk_b (a b : Fin m) (l : Fin p) : ∃ i : Fin (p + p), F.f l b = F.blk a b i :=
  ⟨Fin.natAdd p l, (F.blk_natAdd a b l).symm⟩

theorem orthoEmb_blk_eq {a b : Fin m} {μ μ' : K} {u u' : Fin m → K}
    (hu : u = Pi.single a 1 + μ • Pi.single b 1) (hu' : u' = Pi.single a 1 + μ' • Pi.single b 1)
    (hd : μ' - μ ≠ 0) (c : Fin (p + p) → K) :
    orthoEmb (F.blk a b) c =
      F.vec (fun k => (μ' * c (Fin.castAdd p k) - c (Fin.natAdd p k)) / (μ' - μ)) u +
      F.vec (fun k => (c (Fin.natAdd p k) - μ * c (Fin.castAdd p k)) / (μ' - μ)) u' := by
  subst hu hu'
  simp only [orthoEmb_apply, Fin.sum_univ_add, F.blk_castAdd, F.blk_natAdd, F.vec_add_right,
    F.vec_smul_right, F.vec_single, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  match_scalars <;> field_simp <;> ring

theorem isCenter_pair_of_dec (hσ : IsUnitaryInvolution σ) (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (hζσ : σ ζ = ζ⁻¹) (hαN : σ α * α = 1)
    (hdec : ∀ S : Matrix (Fin p) (Fin p) K, (∀ a b, σ (S b a) = S a b) →
      ∃ Q : Fin (p + 1) → Matrix (Fin p) (Fin p) K, (∀ i a b, σ (Q i b a) = Q i a b) ∧
        Q 0 * Zm ζ = Zm ζ * Q 0 ∧ (∀ j : Fin p, Q j.succ * Gj ζ α j = Gj ζ α j * Q j.succ) ∧
        S = ∑ i, Q i)
    {H : Subgroup (SUid σ n)} (hY : HeisTensor.Cent H Y)
    (hX : ∀ j : ℕ, j < p → HeisTensor.Cent H (X * Y ^ j))
    {a b : Fin m} (hab : a ≠ b) (c : Fin (p + p) → K) (hc : herm σ c c = 0) :
    IsCenter H (orthoEmb (F.blk a b) c) := by
  have hσi := hσ.invol
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by have := hp.two_le; omega)
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζN : σ ζ * ζ = 1 := by rw [hζσ, inv_mul_cancel₀ hζ0]
  obtain ⟨μ, hμ⟩ := hσ.exists_norm_neg_one
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  set μ' := ζ * μ with hμ'def
  have hμ' : σ μ' * μ' = -1 := by
    rw [hμ'def, map_mul]
    linear_combination (σ μ * μ) * hζN + hμ
  have hd : μ' - μ ≠ 0 := by
    rw [hμ'def]
    intro h
    have : (ζ - 1) * μ = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hζ1 (sub_eq_zero.mp h1)
    · exact hμ0 h1
  obtain ⟨u, hu⟩ : ∃ u : Fin m → K, u = Pi.single a 1 + μ • Pi.single b 1 := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : Fin m → K, u' = Pi.single a 1 + μ' • Pi.single b 1 := ⟨_, rfl⟩
  have hsm : ∀ ν : K, (Pi.single a 1 + ν • Pi.single b 1 : Fin m → K) =
      Pi.single a 1 + Pi.single b ν := fun ν => by
    funext i
    by_cases h : i = b <;> simp [Pi.single_apply, h]
  have hiu : herm σ u u = 0 := by
    rw [hu, hsm, herm_pair_two hab]
    simp [hμ]
  have hiu' : herm σ u' u' = 0 := by
    rw [hu', hsm, herm_pair_two hab]
    simp [hμ']
  have hiuu' : herm σ u u' ≠ 0 := by
    rw [hu, hu', hsm, hsm, herm_pair_two hab]
    simp only [map_one, one_mul, mul_one]
    intro h
    have h1 : σ μ * μ' = σ μ * μ := by linear_combination h - hμ
    have h2 : μ' = μ := mul_left_cancel₀ ((map_ne_zero σ).mpr hμ0) h1
    exact hd (by rw [h2]; ring)
  have memX : ∀ (w : Fin m → K), ∀ x ∈ LinearMap.range (Matrix.mulVecLin (F.Vu w)),
      ∃ ξ, x = F.vec ξ w := fun w x hx => by
    obtain ⟨ξ, rfl⟩ := hx
    exact ⟨ξ, by rw [Matrix.mulVecLin_apply, F.Vu_mulVec]⟩
  have memX' : ∀ (w : Fin m → K) (ξ : Fin p → K),
      F.vec ξ w ∈ LinearMap.range (Matrix.mulVecLin (F.Vu w)) := fun w ξ =>
    ⟨ξ, by rw [Matrix.mulVecLin_apply, F.Vu_mulVec]⟩
  have hXi : ∀ (w : Fin m → K), herm σ w w = 0 →
      ∀ x ∈ LinearMap.range (Matrix.mulVecLin (F.Vu w)),
        ∀ y ∈ LinearMap.range (Matrix.mulVecLin (F.Vu w)), herm σ x y = 0 := by
    intro w hw x hx y hy
    obtain ⟨ξ, rfl⟩ := memX w x hx
    obtain ⟨ξ', rfl⟩ := memX w y hy
    rw [F.herm_vec_vec, hw, mul_zero]
  have hXc : ∀ (w : Fin m → K), herm σ w w = 0 →
      ∀ x ∈ LinearMap.range (Matrix.mulVecLin (F.Vu w)), IsCenter H x := by
    intro w hw x hx
    obtain ⟨ξ, rfl⟩ := memX w x hx
    exact F.isCenter_vec_of_dec hσ hdec hY hX ξ hw
  have hdual : ∀ a' ∈ LinearMap.range (Matrix.mulVecLin (F.Vu u')), a' ≠ 0 →
      ∃ b ∈ LinearMap.range (Matrix.mulVecLin (F.Vu u)), herm σ b a' ≠ 0 := by
    intro a' ha' h0
    obtain ⟨ξ₂, rfl⟩ := memX u' _ ha'
    have hξ : ξ₂ ≠ 0 := fun h => h0 (by rw [h, F.vec_zero_left])
    obtain ⟨j, hj⟩ : ∃ j, ξ₂ j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hξ (funext hcon)
    refine ⟨F.vec (Pi.single j 1) u, memX' u _, ?_⟩
    rw [F.herm_vec_vec, herm_single_left]
    simp only [map_one, one_mul]
    exact mul_ne_zero hj hiuu'
  rw [F.orthoEmb_blk_eq hu hu' hd c]
  refine HeisTensor.isCenter_add_dual hσ _ _ (hXi u hiu) (hXi u' hiu') (hXc u hiu) (hXc u' hiu')
    hdual (memX' u _) (memX' u' _) ?_
  rw [← F.orthoEmb_blk_eq hu hu' hd c, herm_orthoEmb (F.blk_on hab)]
  exact hc

theorem exists_move (hσ : IsUnitaryInvolution σ) (hp : p.Prime) {H : Subgroup (SUid σ n)}
    {a b : Fin m} (hab : a ≠ b)
    (hH6 : ∀ c : Fin (p + p) → K, herm σ c c = 0 → IsCenter H (orthoEmb (F.blk a b) c))
    (hμ : ∃ μ : K, σ μ * μ = -1) (γ : Fin (p + p) → K) :
    ∃ (g : SUid σ n) (γ' : Fin (p + p) → K), g ∈ H ∧
      (∀ i : Fin (p + p), p ≤ (i : ℕ) → γ' i = 0) ∧
      g • orthoEmb (F.blk a b) γ = orthoEmb (F.blk a b) γ' ∧
      ∀ w, (∀ u, herm σ (orthoEmb (F.blk a b) u) w = 0) → g • w = w := by
  have hφ := herm_orthoEmb (F.blk_on hab)
  have h2 := hp.two_le
  have h1 := hp.one_lt
  by_cases h0 : γ = 0
  · refine ⟨1, 0, H.one_mem, fun i _ => rfl, ?_, fun w _ => one_smul _ _⟩
    rw [h0, one_smul]
  by_cases hs : herm σ γ γ = 0
  · obtain ⟨μ, hμ⟩ := hμ
    have hi01 : (Fin.castAdd p ⟨0, by omega⟩ : Fin (p + p)) ≠ Fin.castAdd p ⟨1, h1⟩ := by
      intro h
      have h' := congrArg Fin.val h
      simp at h'
    set e : Fin (p + p) → K := Pi.single (Fin.castAdd p ⟨0, by omega⟩) 1 +
      Pi.single (Fin.castAdd p ⟨1, h1⟩) μ with he
    have hc' : herm σ e e = 0 := by
      rw [he, herm_pair_two hi01]
      simp [hμ]
    have hne : e ≠ 0 := by
      intro h
      have h' := congrFun h (Fin.castAdd p ⟨0, by omega⟩)
      rw [he, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hi01, Pi.zero_apply] at h'
      simp at h'
    obtain ⟨g, hg, hgγ, hgw⟩ := Centers.exists_mem_fix_of_iso hσ (by omega) hφ hH6 h0 hs hne hc'
    refine ⟨g, e, hg, fun i hi => ?_, hgγ, hgw⟩
    rw [he, Pi.add_apply, Pi.single_eq_of_ne (castAdd_ne_of_le ⟨0, by omega⟩ i hi).symm,
      Pi.single_eq_of_ne (castAdd_ne_of_le ⟨1, h1⟩ i hi).symm, add_zero]
  · obtain ⟨t, ht⟩ := hσ.exists_norm (herm_self_fixed σ hσ.invol γ)
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hs
      rw [← ht]
      simp
    set e : Fin (p + p) → K := Pi.single (Fin.castAdd p ⟨0, by omega⟩) t with he
    have hc' : herm σ e e = herm σ γ γ := by
      rw [he, herm_single_left, Pi.single_eq_same, ht]
    have hne : e ≠ 0 := by
      intro h
      have h' := congrFun h (Fin.castAdd p ⟨0, by omega⟩)
      rw [he, Pi.single_eq_same, Pi.zero_apply] at h'
      exact ht0 h'
    obtain ⟨g, hg, hgγ, hgw⟩ :=
      Centers.exists_mem_fix_of_norm hσ (Or.inl (by omega)) hφ hH6 hs rfl hc'
    refine ⟨g, e, hg, fun i hi => ?_, hgγ, hgw⟩
    rw [he, Pi.single_eq_of_ne (castAdd_ne_of_le ⟨0, by omega⟩ i hi).symm]

theorem merge (hσ : IsUnitaryInvolution σ) (hp : p.Prime) {H : Subgroup (SUid σ n)}
    (hμ : ∃ μ : K, σ μ * μ = -1)
    (hH6 : ∀ a b : Fin m, a ≠ b → ∀ c : Fin (p + p) → K, herm σ c c = 0 →
      IsCenter H (orthoEmb (F.blk a b) c))
    {S : Finset (Fin m)} {a b : Fin m} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    {v : Fin n → K} (hv : F.Supp S v) :
    ∃ g : SUid σ n, g ∈ H ∧ F.Supp (S.erase b) (g • v) := by
  set γ : Fin (p + p) → K := fun i => herm σ (F.blk a b i) v with hγ
  set y := orthoEmb (F.blk a b) γ with hy
  have hwblk : ∀ i, herm σ (F.blk a b i) (v - y) = 0 := fun i => by
    rw [herm_sub_right, hy, F.herm_blk_phi hab γ i, hγ]
    simp
  have hw : ∀ u, herm σ (orthoEmb (F.blk a b) u) (v - y) = 0 := by
    intro u
    rw [orthoEmb_apply, herm_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [herm_smul_left, hwblk, mul_zero]
  obtain ⟨g, γ', hg, hγ', hgy, hgw⟩ := F.exists_move hσ hp hab (hH6 a b hab) hμ γ
  refine ⟨g, hg, ?_⟩
  have hvv : v = y + (v - y) := by abel
  have hv' : g • v = orthoEmb (F.blk a b) γ' + (v - y) := by
    conv_lhs => rw [hvv]
    rw [smul_add, hgy, hgw _ hw]
  intro l s hs
  rw [hv', herm_add_right]
  by_cases hsb : s = b
  · subst hsb
    obtain ⟨i, hi⟩ := F.exists_blk_b a s l
    rw [F.herm_f_phi_first hab l hγ', hi, hwblk i, zero_add]
  · have hsS : s ∉ S := fun h => hs (Finset.mem_erase.mpr ⟨hsb, h⟩)
    have hsa : s ≠ a := fun h => hsS (h ▸ ha)
    rw [F.herm_f_phi_of_ne hsa hsb, herm_sub_right, hv l s hsS, hy, F.herm_f_phi_of_ne hsa hsb]
    simp

theorem isCenter_of_supp_of_dec (hσ : IsUnitaryInvolution σ) (hp : p.Prime)
    {H : Subgroup (SUid σ n)} (hμ : ∃ μ : K, σ μ * μ = -1)
    (hH6 : ∀ a b : Fin m, a ≠ b → ∀ c : Fin (p + p) → K, herm σ c c = 0 →
      IsCenter H (orthoEmb (F.blk a b) c)) :
    ∀ (N : ℕ) (S : Finset (Fin m)), S.card = N + 2 → ∀ v, F.Supp S v → herm σ v v = 0 →
      IsCenter H v := by
  intro N
  induction N with
  | zero =>
    intro S hS v hv hiso
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
    set γ : Fin (p + p) → K := fun i => herm σ (F.blk a b i) v with hγ
    have hvγ : v = orthoEmb (F.blk a b) γ := by
      have h0 : v - orthoEmb (F.blk a b) γ = 0 := by
        refine F.eq_zero_of_herm_f hσ.invol fun l s => ?_
        rw [herm_sub_right]
        by_cases hsa : s = a
        · subst hsa
          obtain ⟨i, hi⟩ := F.exists_blk_a s b l
          rw [hi, F.herm_blk_phi hab, hγ]
          simp
        by_cases hsb : s = b
        · subst hsb
          obtain ⟨i, hi⟩ := F.exists_blk_b a s l
          rw [hi, F.herm_blk_phi hab, hγ]
          simp
        · have hsS : s ∉ ({a, b} : Finset (Fin m)) := by simp [hsa, hsb]
          rw [hv l s hsS, F.herm_f_phi_of_ne hsa hsb, sub_zero]
      exact sub_eq_zero.mp h0
    rw [hvγ]
    refine hH6 a b hab γ ?_
    rw [← herm_orthoEmb (F.blk_on hab) γ γ, ← hvγ]
    exact hiso
  | succ N ih =>
    intro S hS v hv hiso
    have h2 : 1 < S.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
    obtain ⟨g, hg, hgv⟩ := F.merge hσ hp hμ hH6 ha hb hab hv
    have hS' : (S.erase b).card = N + 2 := by
      rw [Finset.card_erase_of_mem hb]
      omega
    have h3 := ih (S.erase b) hS' (g • v) hgv (by rw [herm_smul_smul]; exact hiso)
    have h4 := h3.map (H.inv_mem hg)
    rwa [inv_smul_smul] at h4

include F in
theorem eq_top_of_dec (hσ : IsUnitaryInvolution σ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : IsPrimitiveRoot ζ p) (hζσ : σ ζ = ζ⁻¹) (hαN : σ α * α = 1)
    (hdec : ∀ S : Matrix (Fin p) (Fin p) K, (∀ a b, σ (S b a) = S a b) →
      ∃ Q : Fin (p + 1) → Matrix (Fin p) (Fin p) K, (∀ i a b, σ (Q i b a) = Q i a b) ∧
        Q 0 * Zm ζ = Zm ζ * Q 0 ∧ (∀ j : Fin p, Q j.succ * Gj ζ α j = Gj ζ α j * Q j.succ) ∧
        S = ∑ i, Q i)
    (hm : 2 ≤ m) {H : Subgroup (SUid σ n)} (hY : HeisTensor.Cent H Y)
    (hX : ∀ j : ℕ, j < p → HeisTensor.Cent H (X * Y ^ j)) : H = ⊤ := by
  have hμ : ∃ μ : K, σ μ * μ = -1 := hσ.exists_norm_neg_one
  have hH6 : ∀ a b : Fin m, a ≠ b → ∀ c : Fin (p + p) → K, herm σ c c = 0 →
      IsCenter H (orthoEmb (F.blk a b) c) := fun a b hab c hc =>
    F.isCenter_pair_of_dec hσ hp hζ hζσ hαN hdec hY hX hab c hc
  have hn : n = p * m := F.card_eq hσ.invol
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hn6 : 6 ≤ n := by
    rw [hn]
    calc 6 = 3 * 2 := by norm_num
      _ ≤ p * m := Nat.mul_le_mul hp3 hm
  refine Centers.eq_top_of_forall_isCenter hσ (by omega) (fun h => by omega) fun v hv => ?_
  obtain ⟨N, hN⟩ : ∃ N, (Finset.univ : Finset (Fin m)).card = N + 2 :=
    ⟨m - 2, by simp; omega⟩
  exact F.isCenter_of_supp_of_dec hσ hp hμ hH6 N Finset.univ hN v
    (fun l s hs => absurd (Finset.mem_univ s) hs) hv

end HeisFrameP

theorem HeisFrameP.eq_top {X Y : Matrix (Fin n) (Fin n) K} {α ζ : K}
    (F : HeisFrameP σ p n m X Y α ζ) (hσ : IsUnitaryInvolution σ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) (hζ : IsPrimitiveRoot ζ p) (hζσ : σ ζ = ζ⁻¹) (hαN : σ α * α = 1)
    (hm : 2 ≤ m) {H : Subgroup (SUid σ n)} (hY : HeisTensor.Cent H Y)
    (hX : ∀ j : ℕ, j < p → HeisTensor.Cent H (X * Y ^ j)) : H = ⊤ := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hαN
  have hασ : σ α = α⁻¹ := eq_inv_of_mul_eq_one_left hαN
  exact F.eq_top_of_dec hσ hp hp2 hζ hζσ hαN
    (fun S hS => decompP hσ.invol hp hp2 hpK hζ hζσ hα0 hασ S hS) hm hY hX

end CFSG.LieType.SeitzGeneration.HeisP
