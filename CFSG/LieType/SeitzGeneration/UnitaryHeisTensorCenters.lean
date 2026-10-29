module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorOps

public section

namespace CFSG.LieType.SeitzGeneration.HeisTensor

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {σ : K ≃+* K} {n m : ℕ}

@[expose] def Cent (H : Subgroup (SUid σ n)) (L : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * L =
    L * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H

theorem isCenter_add_dual (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ n)}
    (X X' : Submodule K (Fin n → K)) (hXi : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0)
    (hX'i : ∀ x ∈ X', ∀ y ∈ X', herm σ x y = 0) (hXc : ∀ x ∈ X, IsCenter H x)
    (hX'c : ∀ x ∈ X', IsCenter H x) (hdual : ∀ a' ∈ X', a' ≠ 0 → ∃ b ∈ X, herm σ b a' ≠ 0)
    {a a' : Fin n → K} (ha : a ∈ X) (ha' : a' ∈ X') (hiso : herm σ (a + a') (a + a') = 0) :
    IsCenter H (a + a') := by
  have hσi := hσ.invol
  by_cases h0' : a' = 0
  · rw [h0', add_zero]; exact hXc a ha
  by_cases h0 : a = 0
  · rw [h0, zero_add]; exact hX'c a' ha'
  set z := herm σ a a' with hz
  have haa : herm σ a a = 0 := hXi a ha a ha
  have ha'a' : herm σ a' a' = 0 := hX'i a' ha' a' ha'
  have hsum : z + σ z = 0 := by
    have h1 := hiso
    simp only [herm_add_left, herm_add_right, haa, ha'a', zero_add, add_zero] at h1
    rw [herm_conj σ hσi a a'] at h1
    linear_combination h1
  by_cases hzne : z = 0
  ·
    obtain ⟨b, hb, hbw⟩ := hdual a' ha' h0'
    obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
    set w := herm σ b a' with hw
    have hστ : σ τ = -τ := by linear_combination hτ
    have hbb : herm σ b b = 0 := hXi b hb b hb
    have hab : herm σ a b = 0 := hXi a ha b hb
    have ha₁ : IsCenter H (a' + (τ * w) • b) := (hXc b hb).move (hX'c a' ha') hτ
    have ha₂ : IsCenter H (a - (τ * w) • b) :=
      hXc _ (X.sub_mem ha (X.smul_mem _ hb))
    have hne : herm σ (a - (τ * w) • b) (a' + (τ * w) • b) ≠ 0 := by
      have e : herm σ (a - (τ * w) • b) (a' + (τ * w) • b) = τ * (σ w * w) := by
        simp only [herm_sub_left, herm_add_right, herm_smul_left, herm_smul_right, hbb, hab,
          map_mul, hστ]
        rw [← hz, hzne, ← hw]
        ring
      rw [e]
      exact mul_ne_zero hτ0 (mul_ne_zero ((map_ne_zero σ).mpr hbw) hbw)
    have hsumeq : (a' + (τ * w) • b) + (a - (τ * w) • b) = a + a' := by abel
    have := IsCenter.add hσi ha₁ ha₂ (by rw [hsumeq]; exact hiso) hne
    rwa [hsumeq] at this
  · have hc : z⁻¹ + σ z⁻¹ = 0 := by
      have hσz : σ z = -z := by linear_combination hsum
      rw [map_inv₀, hσz, inv_neg]
      ring
    have := (hXc a ha).move (hX'c a' ha') hc
    rw [← hz, inv_mul_cancel₀ hzne, one_smul] at this
    rwa [add_comm] at this

namespace HeisFrame

variable {X Y : Matrix (Fin n) (Fin n) K} {α ζ : K} (F : HeisFrame σ n m X Y α ζ)

theorem rho_add_vec {u : Fin m → K} (hu : herm σ u u = 0) (v : Fin n → K) (c : K)
    (η : Fin 3 → K) : F.rho u (v + c • F.vec η u) = F.rho u v := by
  have e : ∀ w, F.rho u w = F.Ru u *ᵥ w := fun w => (F.Ru_mulVec u w).symm
  rw [e, e v, mulVec_add, mulVec_smul, ← e (F.vec η u), F.rho_vec_self hu, smul_zero, add_zero]

theorem isCenter_vec (hσ : IsUnitaryInvolution σ) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hζσ : σ ζ = ζ ^ 2) (hαN : σ α * α = 1) (h3 : (3 : K) ≠ 0) {H : Subgroup (SUid σ n)}
    (hY : Cent H Y) (hX : Cent H X) (hXY : Cent H (X * Y)) (hXYY : Cent H (X * Y * Y))
    (ξ : Fin 3 → K) {u : Fin m → K} (hu : herm σ u u = 0) : IsCenter H (F.vec ξ u) := by
  have hσi := hσ.invol
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hαN
  have hασ : σ α = α⁻¹ := by
    exact eq_inv_of_mul_eq_one_left hαN
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  have hζN : σ ζ * ζ = 1 := by rw [hζσ]; linear_combination hζ3
  refine ⟨by rw [F.herm_vec_vec, hu, mul_zero], fun c hc => ?_⟩
  set S : Matrix (Fin 3) (Fin 3) K := Matrix.of fun a b => ξ a * σ (ξ b) with hSdef
  have hS : ∀ a b, σ (S b a) = S a b := fun a b => by
    simp only [hSdef, Matrix.of_apply, map_mul, hσi]
    ring
  have hdec := decomp σ hζ hζσ hα0 hασ h3 S hS
  set SD : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal (fun a => S a a) with hSD
  have hSDh : ∀ a b, σ (SD b a) = SD a b := fun a b => by
    by_cases h : a = b
    · subst h
      simp [hSD, hS a a]
    · simp [hSD, Matrix.diagonal_apply, h, Ne.symm h]
  have hQ : ∀ j, ∀ a b, σ (Qm σ ζ α S j b a) = Qm σ ζ α S j a b := fun j => Qm_herm σ hσi ζ α S j
  have hmD : F.Mel hσi hSDh hc hu ∈ H :=
    hY _ (F.Mmat_commute hσi F.actY (diag_comm ζ _) c u)
  have hm0 : F.Mel hσi (hQ 0) hc hu ∈ H :=
    hX _ (F.Mmat_commute hσi F.actX (Qm_comm σ hζN hαN S 0) c u)
  have hm1 : F.Mel hσi (hQ 1) hc hu ∈ H :=
    hXY _ (F.Mmat_commute hσi F.actXY (Qm_comm σ hζN hαN S 1) c u)
  have hm2 : F.Mel hσi (hQ 2) hc hu ∈ H :=
    hXYY _ (F.Mmat_commute hσi F.actXYY (Qm_comm σ hζN hαN S 2) c u)
  refine ⟨F.Mel hσi hSDh hc hu * F.Mel hσi (hQ 0) hc hu * F.Mel hσi (hQ 1) hc hu *
    F.Mel hσi (hQ 2) hc hu, H.mul_mem (H.mul_mem (H.mul_mem hmD hm0) hm1) hm2, fun v => ?_⟩
  simp only [mul_smul, F.Mel_smul hσi hSDh hc hu, F.Mel_smul hσi (hQ 0) hc hu,
    F.Mel_smul hσi (hQ 1) hc hu, F.Mel_smul hσi (hQ 2) hc hu, F.rho_add_vec hu]
  have hSρ : S *ᵥ F.rho u v = herm σ (F.vec ξ u) v • ξ := by
    funext a
    simp only [mulVec, dotProduct, hSdef, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
      F.herm_left_vec, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hvec : herm σ (F.vec ξ u) v • F.vec ξ u = F.vec (S *ᵥ F.rho u v) u := by
    rw [hSρ, F.vec_smul_left]
  have hsplit : S *ᵥ F.rho u v = SD *ᵥ F.rho u v + Qm σ ζ α S 0 *ᵥ F.rho u v +
      Qm σ ζ α S 1 *ᵥ F.rho u v + Qm σ ζ α S 2 *ᵥ F.rho u v := by
    conv_lhs => rw [hdec]
    simp only [add_mulVec]
  rw [hvec, hsplit]
  simp only [F.vec_add_left, smul_add]
  abel

@[expose] def blk (a b : Fin m) : Fin 6 → Fin n → K :=
  ![F.f 0 a, F.f 1 a, F.f 2 a, F.f 0 b, F.f 1 b, F.f 2 b]

theorem blk_on {a b : Fin m} (hab : a ≠ b) (i j : Fin 6) :
    herm σ (F.blk a b i) (F.blk a b j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [blk, F.on, hab, hab.symm]

theorem vec_single (ξ : Fin 3 → K) (r : Fin m) :
    F.vec ξ (Pi.single r 1) = ∑ k, ξ k • F.f k r := by
  have e : ∀ k, F.vecw k (Pi.single r 1) = F.f k r := fun k => by
    simp only [vecw, Pi.single_apply, ite_smul, one_smul, zero_smul]
    simp
  simp only [vec, e]

theorem orthoEmb_blk_eq {a b : Fin m} {μ μ' : K} {u u' : Fin m → K}
    (hu : u = Pi.single a 1 + μ • Pi.single b 1) (hu' : u' = Pi.single a 1 + μ' • Pi.single b 1)
    (hd : μ' - μ ≠ 0) (c : Fin 6 → K) :
    orthoEmb (F.blk a b) c =
      F.vec (fun k => (μ' * ![c 0, c 1, c 2] k - ![c 3, c 4, c 5] k) / (μ' - μ)) u +
      F.vec (fun k => (![c 3, c 4, c 5] k - μ * ![c 0, c 1, c 2] k) / (μ' - μ)) u' := by
  subst hu hu'
  simp only [orthoEmb_apply, Fin.sum_univ_six, blk, F.vec_add_right, F.vec_smul_right,
    F.vec_single, Fin.sum_univ_three]
  simp
  match_scalars <;> field_simp <;> ring

theorem herm_pair {a b : Fin m} (hab : a ≠ b) (x y x' y' : K) :
    herm σ (Pi.single a x + Pi.single b y : Fin m → K) (Pi.single a x' + Pi.single b y') =
      σ x * x' + σ y * y' := by
  simp only [herm_add_left, herm_add_right, herm_single_left, herm_single_right, Pi.add_apply,
    Pi.single_eq_same, Pi.single_eq_of_ne hab, Pi.single_eq_of_ne hab.symm]
  ring

theorem isCenter_pair (hσ : IsUnitaryInvolution σ) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hζσ : σ ζ = ζ ^ 2) (hαN : σ α * α = 1) (h3 : (3 : K) ≠ 0) {H : Subgroup (SUid σ n)}
    (hY : Cent H Y) (hX : Cent H X) (hXY : Cent H (X * Y)) (hXYY : Cent H (X * Y * Y))
    {a b : Fin m} (hab : a ≠ b) (c : Fin 6 → K) (hc : herm σ c c = 0) :
    IsCenter H (orthoEmb (F.blk a b) c) := by
  have hσi := hσ.invol
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  have hζN : σ ζ * ζ = 1 := by rw [hζσ]; linear_combination hζ3
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hζ
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
  have hsm : ∀ (ν : K), (Pi.single a 1 + ν • Pi.single b 1 : Fin m → K) =
      Pi.single a 1 + Pi.single b ν := fun ν => by
    funext i
    by_cases h : i = b <;> simp [Pi.single_apply, h]
  have hiu : herm σ u u = 0 := by
    rw [hu, hsm, herm_pair hab]
    simp [hμ]
  have hiu' : herm σ u' u' = 0 := by
    rw [hu', hsm, herm_pair hab]
    simp [hμ']
  have hiuu' : herm σ u u' ≠ 0 := by
    rw [hu, hu', hsm, hsm, herm_pair hab]
    simp only [map_one, one_mul, mul_one]
    intro h
    have h1 : σ μ * μ' = σ μ * μ := by linear_combination h - hμ
    have h2 : μ' = μ := mul_left_cancel₀ ((map_ne_zero σ).mpr hμ0) h1
    exact hd (by rw [h2]; ring)
  have hblk := F.blk_on hab
  have memX : ∀ (w : Fin m → K), ∀ x ∈ LinearMap.range (Matrix.mulVecLin (F.Vu w)),
      ∃ ξ, x = F.vec ξ w := fun w x hx => by
    obtain ⟨ξ, rfl⟩ := hx
    exact ⟨ξ, by rw [Matrix.mulVecLin_apply, F.Vu_mulVec]⟩
  have memX' : ∀ (w : Fin m → K) (ξ : Fin 3 → K),
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
    exact F.isCenter_vec hσ hζ hζσ hαN h3 hY hX hXY hXYY ξ hw
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
  refine isCenter_add_dual hσ _ _ (hXi u hiu) (hXi u' hiu') (hXc u hiu) (hXc u' hiu') hdual
    (memX' u _) (memX' u' _) ?_
  rw [← F.orthoEmb_blk_eq hu hu' hd c, herm_orthoEmb hblk]
  exact hc

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

theorem herm_f_blk_of_ne {a b s : Fin m} (hsa : s ≠ a) (hsb : s ≠ b) (l : Fin 3) (i : Fin 6) :
    herm σ (F.f l s) (F.blk a b i) = 0 := by
  fin_cases i <;> simp [blk, F.on, hsa, hsb]

theorem herm_f_phi_of_ne {a b s : Fin m} (hsa : s ≠ a) (hsb : s ≠ b) (l : Fin 3)
    (γ : Fin 6 → K) : herm σ (F.f l s) (orthoEmb (F.blk a b) γ) = 0 := by
  rw [herm_orthoEmb_right]
  exact Finset.sum_eq_zero fun i _ => by rw [F.herm_f_blk_of_ne hsa hsb, mul_zero]

theorem herm_f_phi_first {a b : Fin m} (hab : a ≠ b) (l : Fin 3) {γ : Fin 6 → K}
    (h : ∀ i : Fin 6, 3 ≤ (i : ℕ) → γ i = 0) :
    herm σ (F.f l b) (orthoEmb (F.blk a b) γ) = 0 := by
  rw [herm_orthoEmb_right, Fin.sum_univ_six, h 3 (by decide), h 4 (by decide), h 5 (by decide)]
  simp [blk, F.on, hab.symm]

theorem exists_move (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ n)} {a b : Fin m}
    (hab : a ≠ b) (hH6 : ∀ c : Fin 6 → K, herm σ c c = 0 → IsCenter H (orthoEmb (F.blk a b) c))
    (hμ : ∃ μ : K, σ μ * μ = -1) (γ : Fin 6 → K) :
    ∃ (g : SUid σ n) (γ' : Fin 6 → K), g ∈ H ∧ (∀ i : Fin 6, 3 ≤ (i : ℕ) → γ' i = 0) ∧
      g • orthoEmb (F.blk a b) γ = orthoEmb (F.blk a b) γ' ∧
      ∀ w, (∀ u, herm σ (orthoEmb (F.blk a b) u) w = 0) → g • w = w := by
  have hφ := herm_orthoEmb (F.blk_on hab)
  by_cases h0 : γ = 0
  · refine ⟨1, 0, H.one_mem, fun i _ => rfl, ?_, fun w _ => one_smul _ _⟩
    rw [h0, one_smul]
  by_cases hs : herm σ γ γ = 0
  · obtain ⟨μ, hμ⟩ := hμ
    have hc' : herm σ (![1, μ, 0, 0, 0, 0] : Fin 6 → K) ![1, μ, 0, 0, 0, 0] = 0 := by
      simp [herm_def, Fin.sum_univ_six, hμ]
    have hne : (![1, μ, 0, 0, 0, 0] : Fin 6 → K) ≠ 0 := fun h => by
      have := congrFun h 0
      simp at this
    obtain ⟨g, hg, hgγ, hgw⟩ := Centers.exists_mem_fix_of_iso hσ (by norm_num : 3 ≤ 6) hφ hH6 h0
      hs hne hc'
    exact ⟨g, ![1, μ, 0, 0, 0, 0], hg, fun i hi => by fin_cases i <;> simp_all, hgγ, hgw⟩
  · obtain ⟨t, ht⟩ := hσ.exists_norm (herm_self_fixed σ hσ.invol γ)
    have hc' : herm σ (![t, 0, 0, 0, 0, 0] : Fin 6 → K) ![t, 0, 0, 0, 0, 0] =
        herm σ γ γ := by
      simp [herm_def, Fin.sum_univ_six, ht]
    obtain ⟨g, hg, hgγ, hgw⟩ := Centers.exists_mem_fix_of_norm hσ (Or.inl (by norm_num : 4 ≤ 6))
      hφ hH6 hs rfl hc'
    exact ⟨g, ![t, 0, 0, 0, 0, 0], hg, fun i hi => by fin_cases i <;> simp_all, hgγ, hgw⟩

theorem herm_blk_phi {a b : Fin m} (hab : a ≠ b) (γ : Fin 6 → K) (i : Fin 6) :
    herm σ (F.blk a b i) (orthoEmb (F.blk a b) γ) = γ i := by
  rw [herm_orthoEmb_right]
  simp [F.blk_on hab]

theorem exists_blk_a (a b : Fin m) (l : Fin 3) : ∃ i : Fin 6, F.f l a = F.blk a b i := by
  fin_cases l
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

theorem exists_blk_b (a b : Fin m) (l : Fin 3) : ∃ i : Fin 6, F.f l b = F.blk a b i := by
  fin_cases l
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

theorem merge (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ n)}
    (hμ : ∃ μ : K, σ μ * μ = -1)
    (hH6 : ∀ a b : Fin m, a ≠ b → ∀ c : Fin 6 → K, herm σ c c = 0 →
      IsCenter H (orthoEmb (F.blk a b) c))
    {S : Finset (Fin m)} {a b : Fin m} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    {v : Fin n → K} (hv : F.Supp S v) :
    ∃ g : SUid σ n, g ∈ H ∧ F.Supp (S.erase b) (g • v) := by
  set γ : Fin 6 → K := fun i => herm σ (F.blk a b i) v with hγ
  set y := orthoEmb (F.blk a b) γ with hy
  have hwblk : ∀ i, herm σ (F.blk a b i) (v - y) = 0 := fun i => by
    rw [herm_sub_right, hy, F.herm_blk_phi hab γ i, hγ]
    simp
  have hw : ∀ u, herm σ (orthoEmb (F.blk a b) u) (v - y) = 0 := by
    intro u
    rw [orthoEmb_apply, herm_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [herm_smul_left, hwblk, mul_zero]
  obtain ⟨g, γ', hg, hγ', hgy, hgw⟩ := F.exists_move hσ hab (hH6 a b hab) hμ γ
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

theorem isCenter_of_supp (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ n)}
    (hμ : ∃ μ : K, σ μ * μ = -1)
    (hH6 : ∀ a b : Fin m, a ≠ b → ∀ c : Fin 6 → K, herm σ c c = 0 →
      IsCenter H (orthoEmb (F.blk a b) c)) :
    ∀ (N : ℕ) (S : Finset (Fin m)), S.card = N + 2 → ∀ v, F.Supp S v → herm σ v v = 0 →
      IsCenter H v := by
  intro N
  induction N with
  | zero =>
    intro S hS v hv hiso
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
    set γ : Fin 6 → K := fun i => herm σ (F.blk a b i) v with hγ
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
    obtain ⟨g, hg, hgv⟩ := F.merge hσ hμ hH6 ha hb hab hv
    have hS' : (S.erase b).card = N + 2 := by
      rw [Finset.card_erase_of_mem hb]
      omega
    have h3 := ih (S.erase b) hS' (g • v) hgv (by rw [herm_smul_smul]; exact hiso)
    have h4 := h3.map (H.inv_mem hg)
    rwa [inv_smul_smul] at h4

include F in
theorem eq_top (hσ : IsUnitaryInvolution σ) (hζ : ζ ^ 2 + ζ + 1 = 0) (hζσ : σ ζ = ζ ^ 2)
    (hαN : σ α * α = 1) (h3 : (3 : K) ≠ 0) {H : Subgroup (SUid σ n)} (hY : Cent H Y)
    (hX : Cent H X) (hXY : Cent H (X * Y)) (hXYY : Cent H (X * Y * Y)) (hn : 4 ≤ n) :
    H = ⊤ := by
  have hμ : ∃ μ : K, σ μ * μ = -1 := hσ.exists_norm_neg_one
  have hH6 : ∀ a b : Fin m, a ≠ b → ∀ c : Fin 6 → K, herm σ c c = 0 →
      IsCenter H (orthoEmb (F.blk a b) c) := fun a b hab c hc =>
    F.isCenter_pair hσ hζ hζσ hαN h3 hY hX hXY hXYY hab c hc
  have hm2 : 2 ≤ m := by
    have := F.le_three_mul
    omega
  refine Centers.eq_top_of_forall_isCenter hσ (by omega) (fun h => by omega) fun v hv => ?_
  obtain ⟨N, hN⟩ : ∃ N, (Finset.univ : Finset (Fin m)).card = N + 2 :=
    ⟨m - 2, by simp; omega⟩
  exact F.isCenter_of_supp hσ hμ hH6 N Finset.univ hN v
    (fun l s hs => absurd (Finset.mem_univ s) hs) hv

end HeisFrame

end CFSG.LieType.SeitzGeneration.HeisTensor
