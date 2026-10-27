module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAlpha

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

section Alpha

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem exists_alphaHom_of [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {F : Type} [Field F]
    (ιF : F →+* K) {x : G} {M : GL ι K} (hxM : Represents e x M) (hM2 : orderOf M = 2)
    (hE : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0)
    (hH : ∀ a : F, unipGL ((M : Matrix ι ι K) - 1) hE (ιF a) ∈ H)
    (hσ : ∀ N ∈ H, ∀ a : K, (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1) →
      ∃ d, ιF d = a) :
    ∃ φ : Multiplicative F →* G, Function.Injective φ ∧ φ.range = alphaGroup e x ∧
      ∀ a : F, φ (Multiplicative.ofAdd a) ^ 2 = 1 ∧
        Represents e (φ (Multiplicative.ofAdd a))
          (unipGL ((M : Matrix ι ι K) - 1) hE (ιF a)) := by
  classical
  set E : Matrix ι ι K := (M : Matrix ι ι K) - 1 with hEdef
  have hM1 : M ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hM2
    omega
  have hE0 : E ≠ 0 := sub_one_ne_zero hM1
  choose f hι2 hι using fun a : F =>
    exists_represents_sq_eq_one (e := e) hZ (hH a) (unipGL_sq hE (ιF a))
  have hι2' : ∀ a, f a ^ 2 ^ 1 = 1 := fun a => by rw [pow_one]; exact hι2 a
  have hι0 : f 0 = 1 := eq_of_represents hZ (hι 0)
    (by rw [map_zero, unipGL_zero]; exact represents_one) (hι2' 0) (k' := 0) (by simp)
  have hcomm : ∀ a b, f a * f b = f b * f a := fun a b =>
    commute_of_represents hZ (hι a) (hι b) (hι2 b) (by rw [unipGL_mul, unipGL_mul, add_comm])
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    have hrep : Represents e (f a * f b) (unipGL E hE (ιF (a + b))) := by
      rw [map_add, ← unipGL_mul]
      exact (hι a).mul (hι b)
    have hsq : (f a * f b) ^ 2 ^ 1 = 1 := by
      rw [pow_one, (show Commute (f a) (f b) from hcomm a b).mul_pow, hι2, hι2, one_mul]
    exact eq_of_represents hZ (hι (a + b)) hrep (hι2' _) hsq
  let φ : Multiplicative F →* G :=
    { toFun := fun d => f d.toAdd
      map_one' := hι0
      map_mul' := fun a b => hadd a.toAdd b.toAdd }
  have hinj : ∀ a, f a = 1 → a = 0 := by
    intro a ha
    have hrep : Represents e (1 : G) (unipGL E hE (ιF a)) := ha ▸ hι a
    obtain ⟨c, hc⟩ := represents_one.exists_scalar hrep
    have hc' : (1 : Matrix ι ι K) + ιF a • E = (c : K) • 1 := by
      have h := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hc
      simp only [coe_unipGL, one_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
      rw [h, Matrix.smul_one_eq_diagonal]
      rfl
    exact (map_eq_zero ιF).mp (eq_zero_of_unip_eq_scalar hE hE0 hc')
  refine ⟨φ, (injective_iff_map_eq_one φ).mpr fun d hd => ?_, ?_, fun a => ⟨hι2 a, hι a⟩⟩
  · have h0 := hinj d.toAdd hd
    exact h0
  · apply le_antisymm
    · rintro _ ⟨d, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨⟨1, hι2' d.toAdd⟩, M, unipGL E hE (ιF d.toAdd), hxM, hM2, hι d.toAdd,
        ιF d.toAdd, ?_⟩
      rw [coe_unipGL, add_sub_cancel_left]
    · rw [alphaGroup, closure_le]
      rintro y ⟨⟨k, hk⟩, M', N, hM', hM'2, hyN, a, ha⟩
      obtain rfl := hxM.eq_of_orderOf_eq_two hM' hM2 hM'2
      obtain ⟨d, rfl⟩ := hσ N hyN.2.1 a ha
      have hN : N = unipGL E hE (ιF d) := by
        apply Units.ext
        rw [coe_unipGL, ← ha, add_sub_cancel]
      rw [hN] at hyN
      exact ⟨Multiplicative.ofAdd d, eq_of_represents hZ (hι d) hyN (hι2' d) hk⟩

end Alpha

section Torus

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {σ : K →+* K}

theorem exists_unitary_conj_eq_smul [Finite K] [CharP K 2] (hσ : ∀ x, σ (σ x) = x)
    (htr : ∀ c, σ c = c → ∃ d, d + σ d = c) {N : Matrix ι ι K} (hN : N * N = 0)
    (hNh : adjM σ N = N) {c : K} (hcσ : σ c = c) (hc : c ≠ 0) :
    ∃ D : GL ι K, (D : Matrix ι ι K).det = 1 ∧ adjM σ (D : Matrix ι ι K) * D = 1 ∧
      (D : Matrix ι ι K) * N * ((D⁻¹ : GL ι K) : Matrix ι ι K) = c • N := by
  classical
  have hNadj : ∀ u v, hform σ (N *ᵥ u) v = hform σ u (N *ᵥ v) := fun u v => by
    rw [hform_mulVec, hNh]
  set U := LinearMap.range N.mulVecLin with hU
  set k := finrank K U with hk
  let bU := Module.finBasis K U
  set u : Fin k → ι → K := fun i => (bU i : ι → K) with hu
  have hmemU : ∀ w ∈ U, ∃ z, w = N *ᵥ z := by
    rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  have huU : ∀ i, u i ∈ U := fun i => (bU i).2
  have hNU : ∀ w ∈ U, N *ᵥ w = 0 := by
    intro w hw
    obtain ⟨z, rfl⟩ := hmemU w hw
    rw [Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  have hisoU : ∀ w ∈ U, ∀ w' ∈ U, hform σ w w' = 0 := by
    intro w hw w' hw'
    obtain ⟨z, rfl⟩ := hmemU w hw
    obtain ⟨z', rfl⟩ := hmemU w' hw'
    rw [hNadj, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec, hform_zero_right]
  have hli : LinearIndependent K u := bU.linearIndependent.map' U.subtype U.ker_subtype
  obtain ⟨u', hdual⟩ := exists_hform_dual hσ u hli
  obtain ⟨u'', hdual'', hiso'', -⟩ := exists_isotropic_dual hσ htr u u'
    (fun i j => hisoU _ (huU i) _ (huU j)) hdual
  set P := projP σ u u'' with hP
  set P' := projP σ u'' u with hP'
  have hPv : ∀ v, P *ᵥ v = ∑ i, hform σ (u'' i) v • u i := fun v => projP_mulVec u u'' v
  have hP'v : ∀ v, P' *ᵥ v = ∑ i, hform σ (u i) v • u'' i := fun v => projP_mulVec u'' u v
  have hu''u : ∀ i j, hform σ (u'' i) (u j) = if i = j then 1 else 0 := fun i j => by
    rw [hform_comm hσ, hdual'']
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have huu : ∀ i j, hform σ (u i) (u j) = 0 := fun i j => hisoU _ (huU i) _ (huU j)
  have hPu : ∀ j, P *ᵥ u j = u j := fun j => by
    rw [hPv]
    simp [hu''u]
  have hPu'' : ∀ j, P *ᵥ u'' j = 0 := fun j => by
    rw [hPv]
    simp [hiso'']
  have hP'u : ∀ j, P' *ᵥ u j = 0 := fun j => by
    rw [hP'v]
    simp [huu]
  have hP'u'' : ∀ j, P' *ᵥ u'' j = u'' j := fun j => by
    rw [hP'v]
    simp [hdual'']
  have hPP : P * P = P := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hPv v, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hPu]
  have hP'P' : P' * P' = P' := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hP'v v, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hP'u'']
  have hrepr : ∀ v, N *ᵥ v = ∑ j, bU.repr ⟨N *ᵥ v, ⟨v, rfl⟩⟩ j • u j := fun v => by
    have h1 := congrArg Subtype.val (bU.sum_repr ⟨N *ᵥ v, ⟨v, rfl⟩⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    exact h1.symm
  have hNu : ∀ i, N *ᵥ u i = 0 := fun i => hNU _ (huU i)
  have hNP : N * P = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hPv v, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul, hNu]
  have hPN : P * N = N := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hrepr v, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hPu]
  have hP'N : P' * N = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    have h1 : ∀ i, hform σ (u i) (N *ᵥ v) = 0 := fun i => hisoU _ (huU i) _ ⟨v, rfl⟩
    rw [← Matrix.mulVec_mulVec, hP'v]
    simp [h1]
  have hNP' : N * P' = N := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← sub_eq_zero, ← Matrix.mulVec_sub]
    refine eq_zero_of_hform_left (σ := σ) fun z => ?_
    rw [← hNadj, hrepr z, hform_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hform_smul_left, hform_sub_right, hP'v, hform_sum_right]
    simp [hform_smul_right, hdual'', Finset.sum_ite_eq]
  obtain ⟨α, hα⟩ := isSquare_of_charTwo' c
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hα
    exact hc hα
  have hασ : σ α = α := by
    have h1 : σ α * σ α = α * α := by rw [← map_mul, ← hα, hcσ]
    have h2 : (σ α - α) * (σ α - α) = 0 := by
      have : (σ α - α) * (σ α - α) = σ α * σ α - α * α - 2 * (α * (σ α - α)) := by ring
      rw [this, h1, sub_self, CharTwo.two_eq_zero, zero_mul, sub_zero]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)
  have hab : (α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1) = 0 := by
    field_simp
    ring
  have hab' : (α⁻¹ - 1) + (α - 1) + (α⁻¹ - 1) * (α - 1) = 0 := by
    rw [show (α⁻¹ - 1) + (α - 1) + (α⁻¹ - 1) * (α - 1) =
      (α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1) by ring]
    exact hab
  obtain ⟨X, hX⟩ : ∃ X : Matrix ι ι K, X = 1 + (α - 1) • P := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix ι ι K, Y = 1 + (α⁻¹ - 1) • P' := ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X' : Matrix ι ι K, X' = 1 + (α - 1) • P' := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y' : Matrix ι ι K, Y' = 1 + (α⁻¹ - 1) • P := ⟨_, rfl⟩
  have hYX' : Y * X' = 1 := by rw [hY, hX']; exact one_add_smul_mul_one_add_smul hP'P' hab'
  have hY'X : Y' * X = 1 := by rw [hY', hX]; exact one_add_smul_mul_one_add_smul hPP hab'
  have hXY' : X * Y' = 1 := by rw [hX, hY']; exact one_add_smul_mul_one_add_smul hPP hab
  have hX'Y : X' * Y = 1 := by rw [hX', hY]; exact one_add_smul_mul_one_add_smul hP'P' hab
  have hDD' : (X * Y) * (X' * Y') = 1 := by
    rw [mul_assoc, ← mul_assoc Y, hYX', one_mul, hXY']
  have hD'D : (X' * Y') * (X * Y) = 1 := by
    rw [mul_assoc, ← mul_assoc Y', hY'X, one_mul, hX'Y]
  let D : GL ι K := ⟨X * Y, X' * Y', hDD', hD'D⟩
  have hPP' : P * P' = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hP'v v, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul, hPu'']
  have hP'P : P' * P = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hPv v, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul, hP'u]
  have hadjD : adjM σ (X * Y) = X' * Y' := by
    rw [adjM_mul, hY, hX, adjM_add, adjM_add, adjM_one, adjM_smul, adjM_smul, hP, hP',
      adjM_projP hσ, adjM_projP hσ, map_sub, map_sub, map_one, map_inv₀, hασ, ← hP, ← hP', hX',
      hY']
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hPP', smul_zero, add_zero,
      add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hP'P, smul_zero, add_zero]
    abel
  refine ⟨D, ?_, ?_, ?_⟩
  ·
    change (X * Y).det = 1
    have hdetP : ∀ a : K, ((1 : Matrix ι ι K) + a • P).det = (1 + a) ^ k := by
      intro a
      let A : Matrix ι (Fin k) K := Matrix.of fun x i => u i x
      let B : Matrix (Fin k) ι K := Matrix.of fun i x => σ (u'' i x)
      have hAB : P = A * B := by
        ext x y
        simp only [hP, projP, Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply, A, B,
          Matrix.of_apply, Function.comp]
      have hBA : B * A = 1 := by
        ext i j
        have := hu''u i j
        simp only [hform, dotProduct, Function.comp] at this
        simp only [Matrix.mul_apply, A, B, Matrix.of_apply, this, Matrix.one_apply]
      rw [hAB, ← Matrix.mul_smul, Matrix.det_one_add_mul_comm, Matrix.smul_mul, hBA,
        show (1 : Matrix (Fin k) (Fin k) K) + a • 1 = (1 + a) • 1 by rw [add_smul, one_smul],
        Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    have hdetP' : ∀ a : K, ((1 : Matrix ι ι K) + a • P').det = (1 + a) ^ k := by
      intro a
      let A : Matrix ι (Fin k) K := Matrix.of fun x i => u'' i x
      let B : Matrix (Fin k) ι K := Matrix.of fun i x => σ (u i x)
      have hAB : P' = A * B := by
        ext x y
        simp only [hP', projP, Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply, A, B,
          Matrix.of_apply, Function.comp]
      have hBA : B * A = 1 := by
        ext i j
        have := hdual'' i j
        simp only [hform, dotProduct, Function.comp] at this
        simp only [Matrix.mul_apply, A, B, Matrix.of_apply, this, Matrix.one_apply]
      rw [hAB, ← Matrix.mul_smul, Matrix.det_one_add_mul_comm, Matrix.smul_mul, hBA,
        show (1 : Matrix (Fin k) (Fin k) K) + a • 1 = (1 + a) • 1 by rw [add_smul, one_smul],
        Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [Matrix.det_mul, hX, hY, hdetP, hdetP', add_sub_cancel, add_sub_cancel, ← mul_pow,
      mul_inv_cancel₀ hα0, one_pow]
  · exact (show adjM σ (X * Y) * (X * Y) = 1 by rw [hadjD]; exact hD'D)
  ·
    change (X * Y) * N * (X' * Y') = c • N
    have hmod : ∀ t : K, N + (t - 1) • N = t • N := fun t => by
      rw [sub_smul, one_smul, add_sub_cancel]
    have h1 : (X * Y) * N = α • N := by
      rw [mul_assoc, hY, add_mul, one_mul, Matrix.smul_mul, hP'N, smul_zero, add_zero, hX,
        add_mul, one_mul, Matrix.smul_mul, hPN, hmod]
    have h2 : N * (X' * Y') = α • N := by
      rw [← mul_assoc, hX', mul_add, mul_one, Matrix.mul_smul, hNP', hmod, hY', Matrix.smul_mul,
        mul_add, mul_one, Matrix.mul_smul, hNP, smul_zero, add_zero]
    rw [h1, Matrix.smul_mul, h2, smul_smul, ← hα]

end Torus

section Unitary

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem autAlpha_unitary : AutAlpha .unitary := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | unitary n m hn hm K hK e =>
    have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    have : CharP K 2 := hU.charP
    have : Finite K := hU.finite
    obtain ⟨ℓ, -, M, hpM, hM2, -⟩ := hp
    set σ := hU.bar with hσdef
    have hσ : ∀ x, σ (σ x) = x := hU.bar_bar
    have hσq : ∀ x, σ x = x ^ 2 ^ m := hU.bar_apply
    have htr : ∀ c, σ c = c → ∃ d, d + σ d = c := by
      intro c hc
      obtain ⟨d, hd⟩ := hU.traceLin_surjective ⟨c, (hU.mem_fixedField).mpr hc⟩
      exact ⟨d, congrArg Subtype.val hd⟩
    have hMu := adjM_mul_self_of_mem_statedSU hσ hσq hpM.2.1
    have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
      rw [← Units.val_mul, ← sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
    have hMadj : adjM σ (M : Matrix (Fin n) (Fin n) K) = M := by
      calc adjM σ (M : Matrix (Fin n) (Fin n) K) =
          adjM σ (M : Matrix (Fin n) (Fin n) K) * (M * M) := by rw [hMM, mul_one]
        _ = M := by rw [← mul_assoc, hMu, one_mul]
    have hNh : adjM σ ((M : Matrix (Fin n) (Fin n) K) - 1) =
        (M : Matrix (Fin n) (Fin n) K) - 1 := by
      rw [adjM_sub, hMadj, adjM_one]
    have hN := sub_one_mul_self_eq_zero hM2
    have hM1 : M ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hM2
      omega
    have hN0 := sub_one_ne_zero hM1
    set F := hU.fixedField with hF
    let ιF : F →+* K := F.subtype
    have hιF : ∀ a : F, σ (ιF a) = ιF a := fun a => (hU.mem_fixedField).mp a.2
    have hunip : ∀ a : F, unipGL ((M : Matrix (Fin n) (Fin n) K) - 1) hN (ιF a) ∈
        StatedSU n (2 ^ m) K := by
      intro a
      refine mem_statedSU_of hσq (det_unipGL hN _) ?_
      have h1 : adjM σ (unipGL _ hN (ιF a) : Matrix (Fin n) (Fin n) K) =
          unipGL _ hN (ιF a) := by
        rw [coe_unipGL, adjM_add, adjM_one, adjM_smul, hιF, hNh]
      rw [h1, ← Units.val_mul, ← sq, unipGL_sq, Units.val_one]
    have hσF : ∀ N ∈ StatedSU n (2 ^ m) K, ∀ a : K,
        (N : Matrix (Fin n) (Fin n) K) - 1 = a • ((M : Matrix (Fin n) (Fin n) K) - 1) →
          ∃ d : F, ιF d = a := by
      intro N hN' a ha
      have hNu := adjM_mul_self_of_mem_statedSU hσ hσq hN'
      have hNeq : (N : Matrix (Fin n) (Fin n) K) =
          1 + a • ((M : Matrix (Fin n) (Fin n) K) - 1) := by
        rw [← ha, add_sub_cancel]
      rw [hNeq, adjM_add, adjM_one, adjM_smul, hNh, add_mul, one_mul, mul_add, mul_one,
        smul_mul_smul_comm, hN, smul_zero, add_zero, add_assoc, ← add_smul, add_eq_left,
        smul_eq_zero] at hNu
      have hσa : σ a = a := by
        rcases hNu with h | h
        · rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
          exact h.symm
        · exact absurd h hN0
      exact ⟨⟨a, (hU.mem_fixedField).mpr hσa⟩, rfl⟩
    obtain ⟨φ, hinj, hrange, hφ⟩ := exists_alphaHom_of hZ ιF hpM hM2 hN hunip hσF
    have h := regularOn_autCyclic_alpha_of (ιF := ιF) hZ hM2 hinj hrange hφ fun l hl => by
      obtain ⟨d, hdet, hdu, hd⟩ :=
        exists_unitary_conj_eq_smul hσ htr hN hNh (hιF l) ((map_ne_zero ιF).mpr hl)
      exact ⟨d, mem_statedSU_of hσq hdet hdu, hd⟩
    show RegularOn A (alphaGroup e p) (nonidentity (alphaGroup e p)) ∧
      AutCyclic A (alphaGroup e p) (2 ^ m - 1)
    rwa [hF, hU.card_fixedField] at h
  | linear => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end Unitary

end CFSG.ComponentClassification.RankTwoClassical
