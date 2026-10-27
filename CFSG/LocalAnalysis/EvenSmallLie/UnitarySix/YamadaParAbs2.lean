module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParAbs

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

@[expose] noncomputable def eSU (m : ℕ) : SU42b := ⟨wordGL (eWord m), wordGL_mem _⟩

@[expose] noncomputable def nuSU (j : ℕ) : SU42b := ⟨wordGL (nuWord j), wordGL_mem _⟩

@[expose] noncomputable def E16 : Subgroup SU42b := Subgroup.closure (Set.range fun m : Fin 4 => eSU m)

theorem coe_eSU (m : ℕ) (hm : m < 4) :
    ((eSU m : GL (Fin 8) (ZMod 2)) : Mat8) = toMat 8 8 (eBits m) := by
  rw [eSU, coe_wordGL]
  exact wordCheck_spec.1 m hm

theorem coe_nuSU (j : ℕ) (hj : j < 2) :
    ((nuSU j : GL (Fin 8) (ZMod 2)) : Mat8) = toMat 8 8 (nuBits j) := by
  rw [nuSU, coe_wordGL]
  exact (wordCheck_spec.2 j hj).1

theorem coe_nuSU_inv (j : ℕ) (hj : j < 2) :
    (((nuSU j)⁻¹ : SU42b) : GL (Fin 8) (ZMod 2)) = toMat 8 8 (nuInvBits j) := by
  have h := (wordCheck_spec.2 j hj).2.2
  rw [← coe_nuSU j hj] at h
  have h' : ((nuSU j : GL (Fin 8) (ZMod 2)) : Mat8) * (((nuSU j)⁻¹ : SU42b) :
      GL (Fin 8) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have h3 := (mul_eq_one_comm_of_card_eq (Fin 8) (Fin 8) (ZMod 2) rfl).mp h'
  calc (((nuSU j)⁻¹ : SU42b) : GL (Fin 8) (ZMod 2)) =
      (((nuSU j)⁻¹ : SU42b) : GL (Fin 8) (ZMod 2)) * (((nuSU j : GL (Fin 8) (ZMod 2)) : Mat8) *
        toMat 8 8 (nuInvBits j)) := by rw [h, mul_one]
    _ = toMat 8 8 (nuInvBits j) := by rw [← mul_assoc, h3, one_mul]

theorem rhoM_eSU (m : ℕ) (hm : m < 4) :
    rhoM ((eSU m : GL (Fin 8) (ZMod 2)) : Mat8) = 1 + embedM (aM m) := by
  rw [coe_eSU m hm]
  exact embedCheck_spec.1 m hm

theorem rhoM_E16 {g : SU42b} (hg : g ∈ E16) :
    ∃ ψ ∈ aSpan, rhoM ((g : GL (Fin 8) (ZMod 2)) : Mat8) = 1 + embedM ψ := by
  refine Subgroup.closure_induction (G := SU42b) (p := fun (g : SU42b) _ =>
    ∃ ψ ∈ aSpan, rhoM ((g : GL (Fin 8) (ZMod 2)) : Mat8) = 1 + embedM ψ) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨m, rfl⟩
    exact ⟨aM m, aM_mem_aSpan m, rhoM_eSU m m.isLt⟩
  · exact ⟨0, zero_mem _, by rw [Subgroup.coe_one, Units.val_one, rhoM_one, embedM_zero,
      add_zero]⟩
  · rintro x y _ _ ⟨ψ, hψ, hx⟩ ⟨ψ', hψ', hy⟩
    refine ⟨ψ + ψ', add_mem hψ hψ', ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, rhoM_mul, hx, hy, embedM_add]
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, embedM_mul_embedM, add_zero]
    abel
  · rintro x _ ⟨ψ, hψ, hx⟩
    refine ⟨ψ, hψ, ?_⟩
    have h1 : rhoM (((x⁻¹ : SU42b) : GL (Fin 8) (ZMod 2)) : Mat8) * rhoM ((x : GL (Fin 8) (ZMod 2))
        : Mat8) = 1 := by
      rw [← rhoM_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
        Units.val_one, rhoM_one]
    have h2 : (1 + embedM ψ) * (1 + embedM ψ) = 1 := by
      rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, embedM_mul_embedM, add_zero,
        add_assoc, mat8_add_self16, add_zero]
    rw [hx] at h1
    calc rhoM (((x⁻¹ : SU42b) : GL (Fin 8) (ZMod 2)) : Mat8)
        = rhoM (((x⁻¹ : SU42b) : GL (Fin 8) (ZMod 2)) : Mat8) * ((1 + embedM ψ) *
            (1 + embedM ψ)) := by rw [h2, mul_one]
      _ = 1 + embedM ψ := by rw [← mul_assoc, h1, one_mul]

theorem toVec_bitsOf (n : ℕ) (w : Fin n → ZMod 2) :
    toVec n (bitsOf n fun j => if h : j < n then w ⟨j, h⟩ == 1 else false) = w := by
  ext j
  rw [toVec, testBit_bitsOf]
  simp only [j.isLt, decide_true, Bool.true_and, dite_true, Fin.eta, bz_beq_one]

theorem eq_zero_of_toVec_eq_zero {n v : ℕ} (hv : v < 2 ^ n) (h : toVec n v = 0) : v = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < n
  · have := congrFun h ⟨i, hi⟩
    simp only [toVec, Pi.zero_apply] at this
    cases hb : v.testBit i
    · rfl
    · rw [hb] at this; exact absurd this (by decide)
  · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
      (not_lt.mp hi)))

theorem bmulVec_lt (n m : ℕ) (A : Array ℕ) (v : ℕ) : bmulVec n m A v < 2 ^ n := bitsOf_lt n _

theorem eq_zero_of_aM_mulVec {w : Fin 8 → ZMod 2} (h : ∀ m < 4, aM m *ᵥ w = 0) : w = 0 := by
  set v := bitsOf 8 fun j => if h : j < 8 then w ⟨j, h⟩ == 1 else false with hv
  have hw : toVec 8 v = w := toVec_bitsOf 8 w
  have hlt : v < 2 ^ 8 := bitsOf_lt 8 _
  have hc := aKerCheck_eq_true
  simp only [aKerCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, bne_iff_ne, ne_eq] at hc
  rcases hc v hlt with h0 | ⟨m, hm, hne⟩
  · rw [← hw, h0]; ext j; simp [toVec]
  · exfalso
    apply hne
    apply eq_zero_of_toVec_eq_zero (bmulVec_lt 8 8 _ _)
    rw [toVec_bmulVec, hw]
    exact h m hm

@[expose] def W0sup (v : Fin 16 → ZMod 2) : Prop := ∀ c : Fin 16, inW1 c = true → v c = 0

theorem w1idx_injective : Function.Injective w1idx := fun b b' h => by
  have := congrArg (fun c : Fin 16 => posW1 c) h
  simp only [(w1idx_spec b).2, (w1idx_spec b').2] at this
  exact Fin.ext this

theorem sum_inW1 (g : Fin 16 → ZMod 2) (hg : ∀ c : Fin 16, inW1 c = false → g c = 0) :
    ∑ c, g c = ∑ b : Fin 8, g (w1idx b) := by
  rw [← Finset.sum_image (f := g) (s := Finset.univ) (g := w1idx)
    (fun x _ y _ h => w1idx_injective h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro c _ hc
  apply hg
  cases h : inW1 c
  · rfl
  · exact absurd (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, w1idx_posW1 c h⟩) hc

theorem embedM_mulVec_w0idx (ψ : Mat8) (v : Fin 16 → ZMod 2) (a : Fin 8) :
    (embedM ψ *ᵥ v) (w0idx a) = (ψ *ᵥ fun b => v (w1idx b)) a := by
  rw [mulVec, dotProduct, sum_inW1]
  · rw [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [embedM, Matrix.of_apply, (w0idx_spec a).1, (w1idx_spec b).1, Bool.and_self,
      ite_true, (w0idx_spec a).2, (w1idx_spec b).2]
    rw [entry, dite_eq_left ⟨a.isLt, b.isLt⟩]
  · intro c hc
    simp [embedM, hc]

theorem embedM_mulVec_eq_zero_of_W0sup (ψ : Mat8) {v : Fin 16 → ZMod 2} (hv : W0sup v) :
    embedM ψ *ᵥ v = 0 := by
  ext r
  rw [mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp only [embedM, Matrix.of_apply]
  split_ifs with h
  · rw [Bool.and_eq_true] at h
    rw [hv c h.2, mul_zero]
  · rw [zero_mul]

theorem W0sup_iff (v : Fin 16 → ZMod 2) : W0sup v ↔ ∀ m < 4, embedM (aM m) *ᵥ v = 0 := by
  constructor
  · intro hv m _
    exact embedM_mulVec_eq_zero_of_W0sup _ hv
  · intro h c hc
    have hw : (fun b => v (w1idx b)) = 0 := eq_zero_of_aM_mulVec fun m hm => by
      ext a
      rw [← embedM_mulVec_w0idx, h m hm, Pi.zero_apply, Pi.zero_apply]
    have := congrFun hw ⟨posW1 c, by revert c; decide +revert⟩
    simp only [Pi.zero_apply] at this
    rwa [w1idx_posW1 c hc] at this

section Blocks

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem matOf_injective (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) {f g : W →ₗ[ZMod 2] W}
    (h : matOf e f = matOf e g) : f = g := by
  ext x
  apply e.injective
  rw [← matOf_mulVec, h, matOf_mulVec]

theorem one_add_embedM_mul (ψ ψ' : Mat8) :
    (1 + embedM ψ) * (1 + embedM ψ') = 1 + embedM (ψ + ψ') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, embedM_mul_embedM, add_zero,
    embedM_add, add_assoc, add_comm (embedM ψ')]

theorem eq_one_add_embedM (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (f : W →ₗ[ZMod 2] W)
    (hW0 : ∀ x, W0sup (e x) → f x = x) (hW1 : ∀ x, W0sup (e (f x + x))) :
    matOf e f = 1 + embedM (blockOf (matOf e f + 1)) := by
  set N := matOf e f + 1 with hN
  have hNv : ∀ v, N *ᵥ v = e (f (e.symm v) + e.symm v) := fun v => by
    rw [hN, add_mulVec, one_mulVec, map_add, LinearEquiv.apply_symm_apply, ← matOf_mulVec,
      LinearEquiv.apply_symm_apply]
  have hE : N = embedM (blockOf N) := by
    apply eq_embedM_blockOf
    · intro r c hc
      have hv : W0sup (Pi.single c 1) := fun c' hc' => by
        rw [Pi.single_apply, ite_eq_right]
        intro hcc
        subst hcc
        exact absurd ⟨hc, hc'⟩ (not_inW0_and_inW1 c')
      have := hNv (Pi.single c 1)
      rw [hW0 _ (by rwa [LinearEquiv.apply_symm_apply]), add_self_W, map_zero,
        mulVec_single_one] at this
      exact congrFun this r
    · intro r c hr
      have := hW1 (e.symm (Pi.single c 1))
      rw [← hNv, mulVec_single_one] at this
      exact this r hr
  calc matOf e f = 1 + N := by rw [hN, ← add_assoc, add_comm 1, add_assoc, mat8_add_self16,
        add_zero]
    _ = 1 + embedM (blockOf N) := by rw [← hE]

end Blocks

theorem alt_symm {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hB : ∀ x, B x x = 0) (x y : W) : B y x = B x y := by
  have h := hB (x + y)
  simp only [map_add, LinearMap.add_apply, hB x, hB y, zero_add, add_zero] at h
  exact zmod2_eq_of_add_eq_zero h

theorem tM16_conj_one_add (x : Mat8) :
    tM16 * ((1 + embedM x) * tM16) = 1 + embedM (tM * x * tM) := by
  rw [← mul_assoc, mul_add, add_mul, mul_one, tM16_mul_tM16, tM16_embedM]

section Main

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {Γ : Type*} [Group Γ]

theorem r3_blocks (π : Γ →* (W →ₗ[ZMod 2] W)) (K : Subgroup Γ) (θ : K ≃* SU42b)
    (τ : W →ₗ[ZMod 2] W) (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (hτ : matOf e τ = tM16)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (D : Subgroup Γ) [Finite D] (hDcard : Nat.card D ≤ 2 ^ 8)
    (hE : ∀ m < 4, ((θ.symm (eSU m) : K) : Γ) ∈ D)
    (hν : ∀ j < 2, ∀ d ∈ D, ((θ.symm (nuSU j) : K) : Γ) * d * ((θ.symm (nuSU j) : K) : Γ)⁻¹ ∈ D)
    (hW0 : ∀ d ∈ D, ∀ x, (∀ m < 4, π ((θ.symm (eSU m) : K) : Γ) x = x) → π d x = x)
    (hW1 : ∀ d ∈ D, ∀ x, ∀ m < 4,
      π ((θ.symm (eSU m) : K) : Γ) (π d x + x) = π d x + x)
    (hfix : ∀ d ∈ D, τ ∘ₗ π d ∘ₗ τ = π d → ∃ g ∈ E16, π d = π ((θ.symm g : K) : Γ))
    (hsurj : ∀ m < 4, ∃ d ∈ D, π d ∘ₗ τ ∘ₗ π d ∘ₗ τ = π ((θ.symm (eSU m) : K) : Γ))
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hB0 : B ≠ 0) (hBalt : ∀ x, B x x = 0)
    (hBK : ∀ k : K, ∀ x y, B (π k x) (π k y) = B x y)
    (hBD : ∀ d ∈ D, ∀ x y, B (π d x) (π d y) = B x y) :
    ∃ z < 4, (∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ) ∧
      ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ := by
  have hEm : ∀ m < 4, matOf e (π ((θ.symm (eSU m) : K) : Γ)) = 1 + embedM (aM m) := fun m hm => by
    rw [hK, MulEquiv.apply_symm_apply, rhoM_eSU m hm]
  have hW0e : ∀ x, W0sup (e x) ↔ ∀ m < 4, π ((θ.symm (eSU m) : K) : Γ) x = x := fun x => by
    rw [W0sup_iff]
    refine forall₂_congr fun m hm => ?_
    rw [← e.injective.eq_iff, ← matOf_mulVec, hEm m hm, add_mulVec, one_mulVec]
    constructor
    · intro h; rw [h, add_zero]
    · intro h
      have := congrArg (· + e x) h
      simpa [add_comm, ← add_assoc, add_self_W] using this
  have hblk : ∀ d ∈ D, matOf e (π d) = 1 + embedM (blockOf (matOf e (π d) + 1)) := fun d hd =>
    eq_one_add_embedM e (π d) (fun x hx => hW0 d hd x ((hW0e x).mp hx))
      (fun x => (hW0e _).mpr (hW1 d hd x))
  have hembed_inj : ∀ x y : Mat8, 1 + embedM x = 1 + embedM y → x = y := fun x y h => by
    have := congrArg blockOf (add_left_cancel h)
    rwa [blockOf_embedM, blockOf_embedM] at this
  set ψ : D → Mat8 := fun d => blockOf (matOf e (π d) + 1) with hψ
  have hψd : ∀ d : D, matOf e (π d) = 1 + embedM (ψ d) := fun d => hblk d d.2
  set Ψ : Set Mat8 := Set.range ψ with hΨ
  have hmul : ∀ d d' : D, ψ (d * d') = ψ d + ψ d' := fun d d' => by
    apply hembed_inj
    rw [← hψd, Subgroup.coe_mul, map_mul, matOf_mul, hψd, hψd, one_add_embedM_mul]
  have h0 : (0 : Mat8) ∈ Ψ := ⟨1, by
    apply hembed_inj
    rw [← hψd, Subgroup.coe_one, map_one, matOf_one, embedM_zero, add_zero]⟩
  have hadd : ∀ x ∈ Ψ, ∀ y ∈ Ψ, x + y ∈ Ψ := by
    rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩
    exact ⟨d * d', hmul d d'⟩
  have hcard : Nat.card Ψ ≤ 2 ^ 8 := (Finite.card_range_le ψ).trans hDcard
  have ha : ∀ m : Fin 4, aM m ∈ Ψ := fun m => ⟨⟨_, hE m m.isLt⟩, by
    apply hembed_inj
    rw [← hψd]
    exact hEm m m.isLt⟩
  have hνΨ : ∀ j < 2, ∀ x ∈ Ψ, n0M j * x * n1M j ∈ Ψ := by
    rintro j hj _ ⟨d, rfl⟩
    refine ⟨⟨_, hν j hj d d.2⟩, ?_⟩
    apply hembed_inj
    rw [← hψd]
    have hνinv : matOf e (π ((θ.symm (nuSU j) : K) : Γ)⁻¹) = rhoM (toMat 8 8 (nuInvBits j)) := by
      rw [← Subgroup.coe_inv, ← map_inv, hK, MulEquiv.apply_symm_apply, coe_nuSU_inv j hj]
    have hνm : matOf e (π ((θ.symm (nuSU j) : K) : Γ)) = rhoM (toMat 8 8 (nuBits j)) := by
      rw [hK, MulEquiv.apply_symm_apply, coe_nuSU j hj]
    simp only [map_mul, matOf_mul]
    rw [hψd d, hνm, hνinv, mul_add, add_mul, mul_one, ← rhoM_mul, (wordCheck_spec.2 j hj).2.2,
      rhoM_one, rhoM_nu_embedM j hj]
  have hfixΨ : ∀ x ∈ Ψ, tM * x * tM = x → x ∈ aSpan := by
    rintro _ ⟨d, rfl⟩ hx
    have hτd : τ ∘ₗ π d ∘ₗ τ = π d := by
      apply matOf_injective e
      rw [matOf_comp, matOf_comp, hτ, hψd, tM16_conj_one_add, hx]
    obtain ⟨g, hg, hgd⟩ := hfix d d.2 hτd
    obtain ⟨x', hx', hgx⟩ := rhoM_E16 hg
    have : matOf e (π d) = 1 + embedM x' := by
      rw [hgd, hK, MulEquiv.apply_symm_apply, hgx]
    rw [hψd] at this
    rw [hembed_inj _ _ this]
    exact hx'
  have hsurjΨ : ∀ m : Fin 4, ∃ x ∈ Ψ, tM * x * tM + x = aM m := by
    intro m
    obtain ⟨d, hd, hdm⟩ := hsurj m m.isLt
    refine ⟨ψ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩, ?_⟩
    have := congrArg (matOf e) hdm
    rw [matOf_comp, matOf_comp, matOf_comp, hτ, hψd ⟨d, hd⟩, hEm m m.isLt] at this
    rw [tM16_conj_one_add, one_add_embedM_mul] at this
    rw [add_comm]
    exact hembed_inj _ _ this
  obtain ⟨z, hz8, hΨz⟩ := exists_eq_psiZ h0 hadd hcard ha hνΨ hfixΨ hsurjΨ
  set B' := B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap with hB'
  set Bt := LinearMap.toMatrix₂' (ZMod 2) B' with hBt
  have hinv : ∀ g : Γ, (∀ x y, B (π g x) (π g y) = B x y) →
      (matOf e (π g))ᵀ * Bt * matOf e (π g) = Bt := by
    intro g hg
    rw [hBt, matOf, ← LinearMap.toMatrix₂'_compl₁₂]
    congr 1
    ext u v
    simp only [hB', LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact hg _ _
  have hBt_symm : Btᵀ = Bt := by
    ext r c
    rw [transpose_apply, hBt, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply]
    simp only [hB', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    exact alt_symm B hBalt _ _
  have hBt_diag : ∀ r, Bt r r = 0 := fun r => by
    rw [hBt, LinearMap.toMatrix₂'_apply]
    simp only [hB', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    exact hBalt _
  have hBt0 : Bt ≠ 0 := by
    intro h
    apply hB0
    have hB'0 : B' = 0 := (LinearMap.toMatrix₂' (ZMod 2)).injective (by rw [← hBt, h, map_zero])
    ext x y
    have := congrArg (fun F : (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2) →ₗ[ZMod 2] ZMod 2 =>
      F (e x) (e y)) hB'0
    simpa [hB'] using this
  have hKs : ∀ s : Fin 3, (rhoM (genMat s))ᵀ * Bt * rhoM (genMat s) = Bt := fun s => by
    have h := hinv _ (hBK (θ.symm (genSU s)))
    rwa [hK, MulEquiv.apply_symm_apply, show ((genSU s : GL (Fin 8) (ZMod 2)) : Mat8) = genMat s
      from coe_genGL s] at h
  have hDinv : ∀ ψ' ∈ psiZ z, (1 + embedM ψ')ᵀ * Bt * (1 + embedM ψ') = Bt := by
    intro ψ' hψ'
    have hmem : ψ' ∈ Ψ := by rw [hΨz]; exact hψ'
    obtain ⟨d, rfl⟩ := hmem
    rw [← hψd]
    exact hinv _ (hBD d d.2)
  have hz4 := lt_four_of_form hz8 hBt0 hBt_symm hBt_diag (hKs 0) (hKs 1) hDinv
  refine ⟨z, hz4, fun d hd => ⟨ψ ⟨d, hd⟩, ?_, hψd ⟨d, hd⟩⟩, fun ψ' hψ' => ?_⟩
  · have : ψ ⟨d, hd⟩ ∈ Ψ := ⟨_, rfl⟩
    rwa [hΨz] at this
  · have hmem : ψ' ∈ Ψ := by rw [hΨz]; exact hψ'
    obtain ⟨d, rfl⟩ := hmem
    exact ⟨d, d.2, hψd d⟩

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
