module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalHermitianBlock

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NormTail

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal OrthogonalTail

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (T : NormTailData K F) {r : ℕ}

@[expose] def tailTwist (u : ℤˣ) : F ≃ₗ[K] F :=
  if u = 1 then LinearEquiv.refl K F else T.bar.toLinearEquiv

theorem tailTwist_one : tailTwist T 1 = LinearEquiv.refl K F :=
  ite_eq_left_iff.2 fun h => absurd rfl h

theorem tailTwist_neg_one : tailTwist T (-1) = T.bar.toLinearEquiv :=
  ite_eq_right_iff.2 fun h => absurd h (by decide)

theorem tailTwist_mul (u u' : ℤˣ) : tailTwist T (u * u') = tailTwist T u * tailTwist T u' := by
  refine LinearEquiv.ext fun z => ?_
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl
  · simp [tailTwist_one]
  · simp [tailTwist_one, tailTwist_neg_one]
  · simp [tailTwist_one, tailTwist_neg_one]
  · simp [tailTwist_one, tailTwist_neg_one, T.bar_bar]

@[expose] def sperm (τ : Equiv.Perm (Fin r ⊕ Fin r)) :
    ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) :=
  (LinearEquiv.funCongrLeft K K τ.symm).prodCongr (tailTwist T (Equiv.Perm.sign τ))

theorem sperm_apply (τ : Equiv.Perm (Fin r ⊕ Fin r)) (v : (Fin r ⊕ Fin r → K) × F) :
    sperm T τ v = (v.1 ∘ τ.symm, tailTwist T (Equiv.Perm.sign τ) v.2) :=
  rfl

variable (r) in
@[expose] def spermHom :
    Equiv.Perm (Fin r ⊕ Fin r) →* ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun := sperm T
  map_one' := LinearEquiv.ext fun v => by
    rw [sperm_apply, map_one, tailTwist_one]
    rfl
  map_mul' τ τ' := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, sperm_apply, sperm_apply, sperm_apply, map_mul, tailTwist_mul]
    rfl

theorem spermHom_apply (τ : Equiv.Perm (Fin r ⊕ Fin r)) : spermHom T r τ = sperm T τ :=
  rfl

@[expose] def blockDiag (A B : Matrix (Fin r) (Fin r) K) :
    ((Fin r ⊕ Fin r → K) × F) →ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun v := (Sum.elim (A *ᵥ (v.1 ∘ Sum.inl)) (B *ᵥ (v.1 ∘ Sum.inr)), v.2)
  map_add' v w := by
    refine Prod.ext (funext fun c => ?_) rfl
    rcases c with i | i
    · simp only [Prod.fst_add, Sum.elim_inl, Pi.add_apply]
      rw [show (v.1 + w.1) ∘ Sum.inl = v.1 ∘ Sum.inl + w.1 ∘ Sum.inl from rfl, Matrix.mulVec_add]
      rfl
    · simp only [Prod.fst_add, Sum.elim_inr, Pi.add_apply]
      rw [show (v.1 + w.1) ∘ Sum.inr = v.1 ∘ Sum.inr + w.1 ∘ Sum.inr from rfl, Matrix.mulVec_add]
      rfl
  map_smul' c v := by
    refine Prod.ext (funext fun d => ?_) rfl
    rcases d with i | i
    · simp only [Prod.smul_fst, Sum.elim_inl, Pi.smul_apply, RingHom.id_apply]
      rw [show (c • v.1) ∘ Sum.inl = c • (v.1 ∘ Sum.inl) from rfl, Matrix.mulVec_smul]
      rfl
    · simp only [Prod.smul_fst, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply]
      rw [show (c • v.1) ∘ Sum.inr = c • (v.1 ∘ Sum.inr) from rfl, Matrix.mulVec_smul]
      rfl

theorem blockDiag_apply (A B : Matrix (Fin r) (Fin r) K) (v : (Fin r ⊕ Fin r → K) × F) :
    blockDiag (F := F) A B v = (Sum.elim (A *ᵥ (v.1 ∘ Sum.inl)) (B *ᵥ (v.1 ∘ Sum.inr)), v.2) :=
  rfl

theorem blockDiag_mul (A A' B B' : Matrix (Fin r) (Fin r) K) :
    blockDiag (F := F) (A * A') (B * B') = blockDiag A B ∘ₗ blockDiag A' B' := by
  refine LinearMap.ext fun v => Prod.ext (funext fun c => ?_) rfl
  rcases c with i | i <;> simp [blockDiag_apply, Matrix.mulVec_mulVec, Function.comp_def]

theorem blockDiag_one : blockDiag (F := F) (1 : Matrix (Fin r) (Fin r) K) 1 = LinearMap.id := by
  refine LinearMap.ext fun v => Prod.ext (funext fun c => ?_) rfl
  rcases c with i | i <;> simp [blockDiag_apply]

theorem coe_mul_coe_inv (A : SpecialLinearGroup (Fin r) K) :
    (A : Matrix (Fin r) (Fin r) K) * ((A⁻¹ : SpecialLinearGroup (Fin r) K) :
      Matrix (Fin r) (Fin r) K) = 1 :=
  congrArg Subtype.val (mul_inv_cancel A)

theorem coe_inv_mul_coe (A : SpecialLinearGroup (Fin r) K) :
    ((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      (A : Matrix (Fin r) (Fin r) K) = 1 :=
  congrArg Subtype.val (inv_mul_cancel A)

variable (F r) in
@[expose] def psi :
    SpecialLinearGroup (Fin r) K →* ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun A := LinearEquiv.ofLinearMap (blockDiag A.1 (A⁻¹).1ᵀ) (blockDiag (A⁻¹).1 A.1ᵀ)
    (by rw [← blockDiag_mul, coe_mul_coe_inv, ← Matrix.transpose_mul, coe_mul_coe_inv,
      Matrix.transpose_one, blockDiag_one])
    (by rw [← blockDiag_mul, coe_inv_mul_coe, ← Matrix.transpose_mul, coe_inv_mul_coe,
      Matrix.transpose_one, blockDiag_one])
  map_one' := LinearEquiv.ext fun v => by
    change blockDiag (1 : SpecialLinearGroup (Fin r) K).1
      ((1 : SpecialLinearGroup (Fin r) K)⁻¹).1ᵀ v = v
    rw [inv_one]
    change blockDiag (1 : Matrix (Fin r) (Fin r) K) (1 : Matrix (Fin r) (Fin r) K)ᵀ v = v
    rw [Matrix.transpose_one, blockDiag_one, LinearMap.id_apply]
  map_mul' A B := LinearEquiv.ext fun v => by
    change blockDiag (A.1 * B.1) ((A * B)⁻¹).1ᵀ v =
      blockDiag A.1 (A⁻¹).1ᵀ (blockDiag B.1 (B⁻¹).1ᵀ v)
    rw [_root_.mul_inv_rev]
    change blockDiag (A.1 * B.1) ((B⁻¹).1 * (A⁻¹).1)ᵀ v = _
    rw [Matrix.transpose_mul, blockDiag_mul, LinearMap.comp_apply]

theorem psi_apply (A : SpecialLinearGroup (Fin r) K) (v : (Fin r ⊕ Fin r → K) × F) :
    psi F r A v = (Sum.elim (A.1 *ᵥ (v.1 ∘ Sum.inl)) ((A⁻¹).1ᵀ *ᵥ (v.1 ∘ Sum.inr)), v.2) :=
  rfl

theorem psi_transvection {i j : Fin r} (hij : i ≠ j) (c : K) :
    psi F r (SpecialLinearGroup.transvection hij c) =
      eichler (quadTail r (normForm T)) (hypVec K F (.inl i)) ((-c) • hypVec K F (.inr j)) := by
  have hji : (Sum.inr j : Fin r ⊕ Fin r) ≠ (Sum.inl i).swap := by simpa using hij.symm
  refine LinearEquiv.ext fun v => ?_
  rw [psi_apply, SpecialLinearGroup.transvection_inv,
    eichler_apply (quadTail_hypVec _) (polar_hypVec_smul_hypVec hji _)]
  refine Prod.ext (funext fun d => ?_) ?_
  · rcases d with k | k
    · simp only [Sum.elim_inl, SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply, Function.update_apply,
        Pi.zero_apply, Function.comp_apply, Prod.fst_sub, Prod.fst_add, Prod.smul_fst,
        Pi.sub_apply, Pi.smul_apply, hypVec_fst, polar_hypVec, polar_smul_right, smul_eq_mul,
        Sum.swap_inl, quadTail_hypVec, QuadraticMap.map_smul, mul_zero]
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    · simp only [Sum.elim_inr, SpecialLinearGroup.transvection_coe, Matrix.transpose_add,
        Matrix.transpose_one, Matrix.transpose_single, Matrix.add_mulVec, Matrix.one_mulVec,
        Matrix.single_mulVec, Pi.add_apply, Function.update_apply, Pi.zero_apply,
        Function.comp_apply, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Pi.sub_apply,
        Pi.smul_apply, hypVec_fst, polar_hypVec, polar_smul_right, smul_eq_mul, Sum.swap_inl,
        quadTail_hypVec, QuadraticMap.map_smul, mul_zero]
      by_cases hk : k = j
      · subst hk
        simp
        ring
      · simp [hk]
  · simp [hypVec_snd]

theorem psi_mem (A : SpecialLinearGroup (Fin r) K) :
    psi F r A ∈ orthElementaryGroup (quadTail r (normForm T)) := by
  have h : (⊤ : Subgroup (SpecialLinearGroup (Fin r) K)).map (psi F r) ≤
      orthElementaryGroup (quadTail r (normForm T)) := by
    rw [← CFSG.LinearGroups.special_linear_elementary_generation, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, b, hab, c, rfl⟩, rfl⟩
    rw [psi_transvection T hab c]
    exact eichler_mem_elementaryGroup _ _ _
  exact h ⟨A, trivial, rfl⟩

theorem psi_injective : Function.Injective (psi (K := K) F r) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  refine Matrix.SpecialLinearGroup.ext _ _ fun k j => ?_
  have h := congrArg (fun g : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) =>
    (g ((Pi.single (Sum.inl j) 1, 0) : (Fin r ⊕ Fin r → K) × F)).1 (Sum.inl k)) hA
  have hs : (fun l : Fin r => (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K) (Sum.inl l)) =
      Pi.single j 1 := by
    funext l
    by_cases hl : l = j
    · subst hl
      simp
    · simp [hl]
  simp only [psi_apply, Sum.elim_inl, Function.comp_def, hs, Matrix.mulVec_single_one,
    LinearEquiv.coe_one, id_eq] at h
  have h' : A.1 k j = (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K) (Sum.inl k) := h
  change A.1 k j = (1 : Matrix (Fin r) (Fin r) K) k j
  rw [h']
  by_cases hkj : k = j
  · subst hkj
    simp
  · simp [hkj, Matrix.one_apply_ne hkj]

variable (r) in
abbrev G0 : Type _ :=
  ↥(orthElementaryGroup (quadTail r (normForm T)))

@[expose] def psiG : SpecialLinearGroup (Fin r) K →* G0 T r :=
  (psi F r).codRestrict _ (psi_mem T)

theorem coe_psiG (A : SpecialLinearGroup (Fin r) K) :
    (psiG T A : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) = psi F r A :=
  rfl

theorem psiG_injective : Function.Injective (psiG T (r := r)) := fun _ _ h =>
  psi_injective (congrArg Subtype.val h)

@[expose] def barSL : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F :=
  SpecialLinearGroup.map (T.bar : F →+* F)

theorem coe_barSL (A : SpecialLinearGroup (Fin 2) F) :
    (barSL T A : Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F).map T.bar :=
  rfl

variable [CharP K 2]

@[expose] def rhoG (i : Fin r) : SpecialLinearGroup (Fin 2) F →* G0 T r :=
  (rho T i).codRestrict _ (rho_mem T i)

theorem coe_rhoG (i : Fin r) (A : SpecialLinearGroup (Fin 2) F) :
    (rhoG T i A : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) = rho T i A :=
  rfl

theorem rhoG_injective (i : Fin r) : Function.Injective (rhoG T i) := fun _ _ h =>
  rho_injective T i (congrArg Subtype.val h)

@[expose] def wG (i : Fin r) : G0 T r :=
  rhoG T i (swapSL F)

theorem sign_swap_inl_inr (i : Fin r) :
    Equiv.Perm.sign (Equiv.swap (Sum.inl i : Fin r ⊕ Fin r) (.inr i)) = -1 :=
  Equiv.Perm.sign_swap (by simp)

theorem coe_wG (i : Fin r) :
    (wG T i : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) =
      sperm T (Equiv.swap (.inl i) (.inr i)) := by
  refine LinearEquiv.ext fun v => ?_
  rw [wG, coe_rhoG, rho_swapSL, sperm_apply, sign_swap_inl_inr, tailTwist_neg_one,
    Equiv.symm_swap]
  rfl

theorem wG_apply (i : Fin r) (v : (Fin r ⊕ Fin r → K) × F) :
    (wG T i : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) v =
      (v.1 ∘ Equiv.swap (.inl i) (.inr i), T.bar v.2) :=
  rho_swapSL T i v

theorem wG_mul_self (i : Fin r) : wG T i * wG T i = 1 := by
  refine Subtype.ext ?_
  change ((wG T i : G0 T r) : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) *
      ((wG T i : G0 T r) : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) = 1
  rw [coe_wG, ← spermHom_apply, ← map_mul, Equiv.swap_mul_self, map_one]

theorem swap_apply_ne_inl {i j : Fin r} (hji : j ≠ i) {c : Fin r ⊕ Fin r} (h : c ≠ .inl i) :
    Equiv.swap (Sum.inl j) (Sum.inr j) c ≠ .inl i := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem swap_apply_ne_inr {i j : Fin r} (hji : j ≠ i) {c : Fin r ⊕ Fin r} (h : c ≠ .inr i) :
    Equiv.swap (Sum.inl j) (Sum.inr j) c ≠ .inr i := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem herm_wG_of_ne {i j : Fin r} (hji : j ≠ i) (u : (Fin r ⊕ Fin r → K) × F) :
    herm T i (((wG T j : G0 T r) :
      ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) u) =
      (herm T i u).map T.bar := by
  have h1 : Equiv.swap (Sum.inl j) (Sum.inr j) (Sum.inl i : Fin r ⊕ Fin r) = Sum.inl i :=
    Equiv.swap_apply_of_ne_of_ne (by simpa using hji.symm) (by simp)
  have h2 : Equiv.swap (Sum.inl j) (Sum.inr j) (Sum.inr i : Fin r ⊕ Fin r) = Sum.inr i :=
    Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hji.symm)
  rw [wG_apply, herm_eq, herm_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h1, h2]

theorem wG_conj_rhoG {i j : Fin r} (hji : j ≠ i) (A : SpecialLinearGroup (Fin 2) F) :
    wG T j * rhoG T i A * (wG T j)⁻¹ = rhoG T i (barSL T A) := by
  rw [inv_eq_of_mul_eq_one_right (wG_mul_self T j)]
  refine Subtype.ext (LinearEquiv.ext fun v => eq_of_herm_eq T i ?_ fun c h1 h2 => ?_)
  · change herm T i (((wG T j : G0 T r) :
      ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) (rho T i A
        (((wG T j : G0 T r) :
          ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) v))) =
      herm T i (rho T i (barSL T A) v)
    rw [herm_wG_of_ne T hji, herm_rho, map_act, herm_wG_of_ne T hji, map_bar_bar, herm_rho,
      coe_barSL]
  · change (((wG T j : G0 T r) :
      ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) (rho T i A
        (((wG T j : G0 T r) :
          ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) v))).1 c =
      (rho T i (barSL T A) v).1 c
    rw [rho_apply_of_ne T i _ v h1 h2, wG_apply]
    change (rho T i A _).1 (Equiv.swap (Sum.inl j) (Sum.inr j) c) = v.1 c
    rw [rho_apply_of_ne T i _ _ (swap_apply_ne_inl hji h1) (swap_apply_ne_inr hji h2), wG_apply]
    change v.1 (Equiv.swap _ _ (Equiv.swap _ _ c)) = v.1 c
    rw [Equiv.swap_apply_self]

end CFSG.LocalAnalysis.ComponentInitial.NormTail
