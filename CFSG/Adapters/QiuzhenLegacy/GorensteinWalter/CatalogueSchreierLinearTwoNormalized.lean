module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter Matrix
open scoped Pointwise

universe u

@[expose] def normalizedAut
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) : MulAut (PSL2 K) :=
  pglAction K (psl2MulAutNormalizerPGL K hKcard alpha) * alpha

theorem normalizedAut_fixes_triple
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) :
    psl2MulAutProjectiveLine K hKcard (normalizedAut K hKcard alpha)
        (psl2ProjectiveInfinity K) = psl2ProjectiveInfinity K ∧
    psl2MulAutProjectiveLine K hKcard (normalizedAut K hKcard alpha)
        (psl2ProjectiveZero K) = psl2ProjectiveZero K ∧
    psl2MulAutProjectiveLine K hKcard (normalizedAut K hKcard alpha)
        (psl2ProjectiveOne K) = psl2ProjectiveOne K := by
  have hspec :
      psl2MulAutNormalizerPGL K hKcard alpha •
          psl2MulAutProjectiveLine K hKcard alpha (psl2ProjectiveInfinity K) =
        psl2ProjectiveInfinity K ∧
      psl2MulAutNormalizerPGL K hKcard alpha •
          psl2MulAutProjectiveLine K hKcard alpha (psl2ProjectiveZero K) =
        psl2ProjectiveZero K ∧
      psl2MulAutNormalizerPGL K hKcard alpha •
          psl2MulAutProjectiveLine K hKcard alpha (psl2ProjectiveOne K) =
        psl2ProjectiveOne K :=
    (Classical.choose_spec (existsUnique_pgl2_normalizes_projective_triple K
      (psl2MulAutProjectiveLine K hKcard alpha))).1
  simpa only [normalizedAut, map_mul, Equiv.Perm.mul_apply,
    pglAction_projectiveLine] using hspec

@[expose] noncomputable def normalizedAffinePerm
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) : Equiv.Perm K := by
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard
      (normalizedAut K hKcard alpha)
  have hfix : tau (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K :=
    (normalizedAut_fixes_triple
      K hKcard alpha).1
  let tauAffine :
      {x : PSL2ProjectiveLine K // x ≠ psl2ProjectiveInfinity K} ≃
        {x : PSL2ProjectiveLine K // x ≠ psl2ProjectiveInfinity K} :=
    tau.subtypeEquiv (fun x => by
      constructor
      · intro hx htx
        apply hx
        apply tau.injective
        rw [htx, hfix]
      · intro htx hx
        subst x
        exact htx hfix)
  exact (psl2AffineEquiv K).trans
    (tauAffine.trans (psl2AffineEquiv K).symm)

private theorem normalizedAffinePerm_point
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) (x : K) :
    psl2AffinePoint K
        (normalizedAffinePerm K hKcard alpha x) =
      psl2MulAutProjectiveLine K hKcard
        (normalizedAut K hKcard alpha)
        (psl2AffinePoint K x) := by
  simp [normalizedAffinePerm]
  exact congrArg Subtype.val
    ((psl2AffineEquiv K).apply_symm_apply _)

@[simp]
theorem normalizedAffinePerm_zero
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) :
    normalizedAffinePerm K hKcard alpha 0 = 0 := by
  apply psl2AffinePoint_injective
  rw [normalizedAffinePerm_point, psl2AffinePoint_zero]
  exact (normalizedAut_fixes_triple
    K hKcard alpha).2.1

@[simp]
theorem normalizedAffinePerm_one
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) :
    normalizedAffinePerm K hKcard alpha 1 = 1 := by
  apply psl2AffinePoint_injective
  rw [normalizedAffinePerm_point]
  exact (normalizedAut_fixes_triple
    K hKcard alpha).2.2

private theorem normalizedAut_upper
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) (a : K) :
    normalizedAut K hKcard alpha
        (psl2QuotientMap K (sl2UpperUnipotent a)) =
      psl2QuotientMap K
        (sl2UpperUnipotent
          (normalizedAffinePerm K hKcard alpha a)) := by
  let beta : MulAut (PSL2 K) :=
    normalizedAut K hKcard alpha
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard beta
  let U : Sylow p (PSL2 K) := psl2UpperUnipotentSylow K hKcard
  have hfixInfinity : tau (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K :=
    (normalizedAut_fixes_triple
      K hKcard alpha).1
  have hfixZero : tau (psl2ProjectiveZero K) =
      psl2ProjectiveZero K :=
    (normalizedAut_fixes_triple
      K hKcard alpha).2.1
  have hUSylow : beta • U = U := by
    have h := congrArg (psl2ProjectiveLineEquivSylow K hKcard)
      hfixInfinity
    rw [psl2MulAutProjectiveLine_apply, Equiv.apply_symm_apply,
      psl2ProjectiveLineEquivSylow_infinity] at h
    simpa [U] using h
  have haU : psl2QuotientMap K (sl2UpperUnipotent a) ∈
      (U : Subgroup (PSL2 K)) := by
    rw [psl2UpperUnipotentSylow_coe]
    exact (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨a, rfl⟩
  have hbetaU :
      beta (psl2QuotientMap K (sl2UpperUnipotent a)) ∈
        (U : Subgroup (PSL2 K)) := by
    have hmem :
        beta (psl2QuotientMap K (sl2UpperUnipotent a)) ∈
          (beta • U : Sylow p (PSL2 K)) := by
      change beta (psl2QuotientMap K (sl2UpperUnipotent a)) ∈
        beta • (U : Subgroup (PSL2 K))
      change beta (psl2QuotientMap K (sl2UpperUnipotent a)) ∈
        (U : Subgroup (PSL2 K)).map (beta : PSL2 K →* PSL2 K)
      exact Subgroup.mem_map.mpr ⟨_, haU, rfl⟩
    rwa [hUSylow] at hmem
  rw [psl2UpperUnipotentSylow_coe] at hbetaU
  obtain ⟨b, hb⟩ :=
    (mem_psl2UpperUnipotentSubgroup_iff _).1 hbetaU
  have hsmul := psl2MulAutProjectiveLine_smul K hKcard beta
    (psl2QuotientMap K (sl2UpperUnipotent a))
    (psl2AffinePoint K 0)
  rw [psl2UpperUnipotent_smul_affine, zero_add] at hsmul
  rw [psl2AffinePoint_zero, hfixZero, hb] at hsmul
  rw [← psl2AffinePoint_zero,
    psl2UpperUnipotent_smul_affine, zero_add] at hsmul
  have hab :
      normalizedAffinePerm K hKcard alpha a = b := by
    apply psl2AffinePoint_injective
    rw [normalizedAffinePerm_point]
    exact hsmul
  rw [hb, hab]

theorem normalizedAffinePerm_add
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) (x a : K) :
    normalizedAffinePerm K hKcard alpha (x + a) =
      normalizedAffinePerm K hKcard alpha x +
        normalizedAffinePerm K hKcard alpha a := by
  let beta : MulAut (PSL2 K) :=
    normalizedAut K hKcard alpha
  have hsmul := psl2MulAutProjectiveLine_smul K hKcard beta
    (psl2QuotientMap K (sl2UpperUnipotent a))
    (psl2AffinePoint K x)
  rw [psl2UpperUnipotent_smul_affine] at hsmul
  rw [← normalizedAffinePerm_point K hKcard alpha (x + a),
    normalizedAut_upper K hKcard alpha a,
    ← normalizedAffinePerm_point K hKcard alpha x,
    psl2UpperUnipotent_smul_affine] at hsmul
  exact psl2AffinePoint_injective hsmul

@[expose] noncomputable def normalizedAffineAddEquiv
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) : K ≃+ K :=
  { normalizedAffinePerm K hKcard alpha with
    map_add' := normalizedAffinePerm_add K hKcard alpha }

private theorem normalizedAffinePerm_sq_mul
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) (t x : K) :
    normalizedAffinePerm K hKcard alpha (t ^ 2 * x) =
      normalizedAffinePerm K hKcard alpha (t ^ 2) *
        normalizedAffinePerm K hKcard alpha x := by
  by_cases ht : t = 0
  · subst t
    simp
  let beta : MulAut (PSL2 K) :=
    normalizedAut K hKcard alpha
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard beta
  let d : PSL2 K := psl2QuotientMap K
    (Matrix.SpecialLinearGroup.diag2 t ht)
  have hfixInfinity : tau (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K :=
    (normalizedAut_fixes_triple
      K hKcard alpha).1
  have hfixZero : tau (psl2ProjectiveZero K) =
      psl2ProjectiveZero K :=
    (normalizedAut_fixes_triple
      K hKcard alpha).2.1
  have hdInfinity : d • psl2ProjectiveInfinity K =
      psl2ProjectiveInfinity K := by
    change Matrix.SpecialLinearGroup.diag2 t ht •
      psl2ProjectiveInfinity K = psl2ProjectiveInfinity K
    rw [← MulAction.mem_stabilizer_iff,
      sl2_mem_stabilizer_infinity_iff]
    simp [Matrix.SpecialLinearGroup.diag2_coe']
  have hdZero : d • psl2ProjectiveZero K =
      psl2ProjectiveZero K := by
    change Matrix.SpecialLinearGroup.diag2 t ht •
      psl2ProjectiveZero K = psl2ProjectiveZero K
    rw [← MulAction.mem_stabilizer_iff,
      sl2_mem_stabilizer_zero_iff]
    simp [Matrix.SpecialLinearGroup.diag2_coe']
  have hbetaInfinity : beta d • psl2ProjectiveInfinity K =
      psl2ProjectiveInfinity K := by
    have h := psl2MulAutProjectiveLine_smul K hKcard beta d
      (psl2ProjectiveInfinity K)
    rw [hdInfinity, hfixInfinity] at h
    exact h.symm
  have hbetaZero : beta d • psl2ProjectiveZero K =
      psl2ProjectiveZero K := by
    have h := psl2MulAutProjectiveLine_smul K hKcard beta d
      (psl2ProjectiveZero K)
    rw [hdZero, hfixZero] at h
    exact h.symm
  obtain ⟨c, hc⟩ :=
    exists_psl2_smul_affine_eq_mul_of_fixes_infinity_zero
      (beta d) hbetaInfinity hbetaZero
  have hscale (y : K) :
      normalizedAffinePerm K hKcard alpha (t ^ 2 * y) =
        c * normalizedAffinePerm K hKcard alpha y := by
    have h := psl2MulAutProjectiveLine_smul K hKcard beta d
      (psl2AffinePoint K y)
    rw [psl2Diag2_smul_affine] at h
    rw [← normalizedAffinePerm_point K hKcard alpha
        (t ^ 2 * y),
      ← normalizedAffinePerm_point K hKcard alpha y,
      hc] at h
    exact psl2AffinePoint_injective h
  have hcEq : c =
      normalizedAffinePerm K hKcard alpha (t ^ 2) := by
    have h := hscale 1
    simpa using h.symm
  rw [hscale, hcEq]

theorem normalizedAffinePerm_mul
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) (x y : K) :
    normalizedAffinePerm K hKcard alpha (x * y) =
      normalizedAffinePerm K hKcard alpha x *
        normalizedAffinePerm K hKcard alpha y := by
  let : Fintype K := Fintype.ofFinite K
  by_cases hchar : ringChar K = 2
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two hchar x
    rw [ha]
    simpa [pow_two] using normalizedAffinePerm_sq_mul K hKcard alpha a y
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  let a : K := (y + 1) / 2
  let b : K := (y - 1) / 2
  have hy : y = a ^ 2 - b ^ 2 := by
    dsimp [a, b]
    field_simp [htwo]
    all_goals ring
  let sigmaAdd : K ≃+ K :=
    normalizedAffineAddEquiv K hKcard alpha
  calc
    normalizedAffinePerm K hKcard alpha (x * y) =
        normalizedAffinePerm K hKcard alpha
          ((a ^ 2 - b ^ 2) * x) := by rw [hy, mul_comm]
    _ = normalizedAffinePerm K hKcard alpha
          (a ^ 2 * x - b ^ 2 * x) := by
      congr 1
      ring
    _ = normalizedAffinePerm K hKcard alpha
          (a ^ 2 * x) -
        normalizedAffinePerm K hKcard alpha
          (b ^ 2 * x) := by
      exact map_sub sigmaAdd _ _
    _ = normalizedAffinePerm K hKcard alpha (a ^ 2) *
          normalizedAffinePerm K hKcard alpha x -
        normalizedAffinePerm K hKcard alpha (b ^ 2) *
          normalizedAffinePerm K hKcard alpha x := by
      rw [normalizedAffinePerm_sq_mul,
        normalizedAffinePerm_sq_mul]
    _ = (normalizedAffinePerm K hKcard alpha (a ^ 2) -
          normalizedAffinePerm K hKcard alpha (b ^ 2)) *
        normalizedAffinePerm K hKcard alpha x := by ring
    _ = normalizedAffinePerm K hKcard alpha
          (a ^ 2 - b ^ 2) *
        normalizedAffinePerm K hKcard alpha x := by
      congr 1
      exact (map_sub sigmaAdd (a ^ 2) (b ^ 2)).symm
    _ = normalizedAffinePerm K hKcard alpha y *
        normalizedAffinePerm K hKcard alpha x := by rw [← hy]
    _ = normalizedAffinePerm K hKcard alpha x *
        normalizedAffinePerm K hKcard alpha y := mul_comm _ _

@[expose] noncomputable def normalizedAffineRingEquiv
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) : K ≃+* K :=
  { normalizedAffineAddEquiv K hKcard alpha with
    map_mul' := normalizedAffinePerm_mul K hKcard alpha }

@[simp]
theorem normalizedAffineRingEquiv_apply
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) (x : K) :
    normalizedAffineRingEquiv K hKcard alpha x =
      normalizedAffinePerm K hKcard alpha x := rfl

theorem fieldAut_upper
    (K : Type u) [Field K] (sigma : K ≃+* K) (a : K) :
    psl2FieldAut K sigma
        (psl2QuotientMap K (sl2UpperUnipotent a)) =
      psl2QuotientMap K (sl2UpperUnipotent (sigma a)) := by
  rw [psl2FieldAut_apply]
  change psl2RingEquiv sigma
      (QuotientGroup.mk' (Subgroup.center _) (sl2UpperUnipotent a)) = _
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j
  · change sigma 1 = 1
    simp
  · change sigma a = sigma a
    rfl
  · change sigma 0 = 0
    simp
  · change sigma 1 = 1
    simp

theorem fieldAut_weyl
    (K : Type u) [Field K] (sigma : K ≃+* K) :
    psl2FieldAut K sigma (psl2SymplecticElement K) =
      psl2SymplecticElement K := by
  rw [psl2FieldAut_apply]
  rw [psl2SymplecticElement_eq_mk]
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j
  · change sigma 0 = 0
    simp
  · change sigma (-1) = -1
    simp
  · change sigma 1 = 1
    simp
  · change sigma 0 = 0
    simp

theorem weyl_smul_infinity
    (K : Type u) [Field K] :
    psl2SymplecticElement K • psl2ProjectiveInfinity K =
      psl2ProjectiveZero K := by
  let e0 : Fin 2 → K := ![1, 0]
  let e1 : Fin 2 → K := ![0, 1]
  rw [psl2SymplecticElement_eq_mk]
  change sl2SymplecticMatrix K • psl2ProjectiveInfinity K =
    psl2ProjectiveZero K
  rw [psl2ProjectiveInfinity, psl2ProjectiveZero,
    Projectivization.smul_mk]
  change Projectivization.mk K
      ((sl2SymplecticMatrix K).1 *ᵥ e0) _ =
    Projectivization.mk K e1 _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  change (1 : K) • e1 = (sl2SymplecticMatrix K).1 *ᵥ e0
  ext i
  fin_cases i <;>
    simp [sl2SymplecticMatrix, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail, e0, e1]

theorem fieldAut_projectiveLine_affine
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (sigma : K ≃+* K) (a : K) :
    psl2MulAutProjectiveLine K hKcard (psl2FieldAut K sigma)
        (psl2AffinePoint K a) =
      psl2AffinePoint K (sigma a) := by
  let phi : MulAut (PSL2 K) := psl2FieldAut K sigma
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard phi
  let U : Sylow p (PSL2 K) := psl2UpperUnipotentSylow K hKcard
  have hUSylow : phi • U = U := by
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def]
    rw [psl2UpperUnipotentSylow_coe]
    ext g
    change g ∈ (psl2UpperUnipotentSubgroup K).map
      (phi : PSL2 K →* PSL2 K) ↔ g ∈ psl2UpperUnipotentSubgroup K
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨b, rfl⟩ :=
        (mem_psl2UpperUnipotentSubgroup_iff h).1 hh
      change phi (psl2QuotientMap K (sl2UpperUnipotent b)) ∈
        psl2UpperUnipotentSubgroup K
      have hmap : phi (psl2QuotientMap K (sl2UpperUnipotent b)) =
          psl2QuotientMap K (sl2UpperUnipotent (sigma b)) := by
        simpa [phi] using fieldAut_upper K sigma b
      rw [hmap]
      exact (mem_psl2UpperUnipotentSubgroup_iff _).2
        ⟨sigma b, rfl⟩
    · intro hg
      obtain ⟨b, rfl⟩ :=
        (mem_psl2UpperUnipotentSubgroup_iff g).1 hg
      refine ⟨psl2QuotientMap K
          (sl2UpperUnipotent (sigma.symm b)), ?_, ?_⟩
      · exact (mem_psl2UpperUnipotentSubgroup_iff _).2
          ⟨sigma.symm b, rfl⟩
      · change phi (psl2QuotientMap K
            (sl2UpperUnipotent (sigma.symm b))) =
          psl2QuotientMap K (sl2UpperUnipotent b)
        have hmap := fieldAut_upper K sigma (sigma.symm b)
        simpa [phi] using hmap
  have hInfinity : tau (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K := by
    apply (psl2ProjectiveLineEquivSylow K hKcard).injective
    rw [psl2MulAutProjectiveLine_apply, Equiv.apply_symm_apply,
      psl2ProjectiveLineEquivSylow_infinity]
    simpa [phi, U] using hUSylow
  have hZero : tau (psl2ProjectiveZero K) =
      psl2ProjectiveZero K := by
    have h := psl2MulAutProjectiveLine_smul K hKcard phi
      (psl2SymplecticElement K) (psl2ProjectiveInfinity K)
    rw [weyl_smul_infinity,
      fieldAut_weyl, hInfinity,
      weyl_smul_infinity] at h
    exact h
  have h := psl2MulAutProjectiveLine_smul K hKcard phi
    (psl2QuotientMap K (sl2UpperUnipotent a))
    (psl2AffinePoint K 0)
  rw [psl2UpperUnipotent_smul_affine, zero_add] at h
  rw [psl2AffinePoint_zero, hZero,
    fieldAut_upper] at h
  rw [← psl2AffinePoint_zero,
    psl2UpperUnipotent_smul_affine, zero_add] at h
  exact h

theorem fieldAut_projectiveLine_infinity
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (sigma : K ≃+* K) :
    psl2MulAutProjectiveLine K hKcard (psl2FieldAut K sigma)
        (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K := by
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard (psl2FieldAut K sigma)
  by_contra hInfinity
  obtain ⟨b, hb, _⟩ := existsUnique_psl2AffinePoint_eq
    (tau (psl2ProjectiveInfinity K)) hInfinity
  obtain ⟨a, rfl⟩ := sigma.surjective b
  have hAffine := fieldAut_projectiveLine_affine
    K hKcard sigma a
  have hEq : tau (psl2AffinePoint K a) =
      tau (psl2ProjectiveInfinity K) := hAffine.trans hb
  exact psl2AffinePoint_ne_infinity a (tau.injective hEq)

theorem normalizedAut_eq_fieldAut
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) :
    normalizedAut K hKcard alpha =
      psl2FieldAut K
        (normalizedAffineRingEquiv K hKcard alpha) := by
  apply psl2MulAutProjectiveLine_injective K hKcard
  apply Equiv.ext
  intro z
  by_cases hz : z = psl2ProjectiveInfinity K
  · subst z
    exact (normalizedAut_fixes_triple
      K hKcard alpha).1.trans
        (fieldAut_projectiveLine_infinity K hKcard
          (normalizedAffineRingEquiv K hKcard alpha)).symm
  · obtain ⟨x, hx, _⟩ := existsUnique_psl2AffinePoint_eq z hz
    calc
      psl2MulAutProjectiveLine K hKcard
          (normalizedAut K hKcard alpha) z =
          psl2AffinePoint K
            (normalizedAffinePerm K hKcard alpha x) := by
        rw [← hx]
        exact (normalizedAffinePerm_point
          K hKcard alpha x).symm
      _ = psl2AffinePoint K
          (normalizedAffineRingEquiv K hKcard alpha x) := rfl
      _ = psl2MulAutProjectiveLine K hKcard
          (psl2FieldAut K
            (normalizedAffineRingEquiv K hKcard alpha)) z := by
        rw [← hx]
        exact (fieldAut_projectiveLine_affine K hKcard
          (normalizedAffineRingEquiv K hKcard alpha) x).symm


end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
