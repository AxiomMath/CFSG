module

public import CFSG.CharacterTheory.BrauerLinearThree.QThree

public section

namespace CFSG.Semidihedral.SimpleLayerFrontier

noncomputable section

open Matrix CFSG.Semidihedral

variable {F : Type} [Field F]

@[expose] def unitSquares (F : Type) [Field F] : Subgroup Fˣ :=
  (powMonoidHom 2 : Fˣ →* Fˣ).range

theorem mem_unitSquares_iff (c : Fˣ) : c ∈ unitSquares F ↔ ∃ d : Fˣ, d ^ 2 = c := by
  rfl

theorem not_isSquare_neg_one_field [Finite F] (hq : Nat.card F % 4 = 3) : ¬ IsSquare (-1 : F) := by
  have := Fintype.ofFinite F
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
  omega

theorem two_ne_zero_field [Finite F] (hq : Nat.card F % 4 = 3) : (2 : F) ≠ 0 := by
  intro h2
  apply not_isSquare_neg_one_field hq
  refine ⟨1, ?_⟩
  linear_combination -h2

theorem neg_one_ne_one_units [Finite F] (hq : Nat.card F % 4 = 3) : (-1 : Fˣ) ≠ 1 := by
  intro h
  have h' : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val h
  apply two_ne_zero_field hq
  simp only [Units.val_neg, Units.val_one] at h'
  linear_combination -h'

theorem neg_one_not_mem_unitSquares [Finite F] (hq : Nat.card F % 4 = 3) :
    (-1 : Fˣ) ∉ unitSquares F := by
  rintro ⟨d, hd⟩
  apply not_isSquare_neg_one_field hq
  refine ⟨(d : F), ?_⟩
  have := congrArg Units.val hd
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at this
  rw [← this, pow_two]

theorem eq_one_or_neg_one_of_sq (c : Fˣ) (hc : c ^ 2 = 1) : c = 1 ∨ c = -1 := by
  have h : ((c : F) - 1) * ((c : F) + 1) = 0 := by
    have := congrArg Units.val hc
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · left
    apply Units.ext
    simp only [Units.val_one]
    linear_combination h
  · right
    apply Units.ext
    simp only [Units.val_neg, Units.val_one]
    linear_combination h

theorem eq_one_of_mem_unitSquares_of_sq [Finite F] (hq : Nat.card F % 4 = 3) (c : Fˣ)
    (hcU : c ∈ unitSquares F) (hc : c ^ 2 = 1) : c = 1 := by
  rcases eq_one_or_neg_one_of_sq c hc with h | h
  · exact h
  · exact (neg_one_not_mem_unitSquares hq (h ▸ hcU)).elim

theorem sq_ne_neg_one_of_mem_unitSquares [Finite F] (hq : Nat.card F % 4 = 3) (c : Fˣ)
    (hcU : c ∈ unitSquares F) : c ^ 2 ≠ -1 := by
  obtain ⟨d, rfl⟩ := hcU
  intro h
  apply neg_one_not_mem_unitSquares hq
  exact ⟨d ^ 2, by simpa only [powMonoidHom_apply] using h⟩

theorem mem_unitSquares_or_neg [Finite F] (hq : Nat.card F % 4 = 3) (d : Fˣ) :
    d ∈ unitSquares F ∨ -d ∈ unitSquares F := by
  classical
  have := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply two_ne_zero_field hq
    have : CharP F 2 := ringChar.eq_iff.mp h
    exact CharP.cast_eq_zero F 2
  have hsq : ∀ x : Fˣ, IsSquare (x : F) → x ∈ unitSquares F := by
    intro x ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro h0
      exact x.ne_zero (by rw [hy, h0, mul_zero])
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    simp [hy, pow_two]
  by_cases hd : IsSquare (d : F)
  · exact Or.inl (hsq d hd)
  · right
    apply hsq
    have hχd : quadraticChar F (d : F) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hd
    have hχn : quadraticChar F (-1 : F) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr (not_isSquare_neg_one_field hq)
    have hne : ((-d : Fˣ) : F) ≠ 0 := (-d).ne_zero
    rw [← quadraticChar_one_iff_isSquare hne]
    have : ((-d : Fˣ) : F) = (-1 : F) * (d : F) := by simp
    rw [this, map_mul, hχd, hχn]
    norm_num

theorem card_unitSquares_mul_two [Finite F] (hq : Nat.card F % 4 = 3) :
    Nat.card (unitSquares F) * 2 = Nat.card F - 1 := by
  have hker : Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).ker = 2 := by
    have hroots : (powMonoidHom 2 : Fˣ →* Fˣ).ker = rootsOfUnity 2 F := by
      ext x
      rw [MonoidHom.mem_ker, mem_rootsOfUnity, powMonoidHom_apply]
    rw [hroots]
    have hchar : ringChar F ≠ 2 := by
      intro h
      apply two_ne_zero_field hq
      have : CharP F 2 := ringChar.eq_iff.mp h
      exact CharP.cast_eq_zero F 2
    exact (IsPrimitiveRoot.neg_one (ringChar F) hchar).card_rootsOfUnity
  have h := Subgroup.card_mul_index (powMonoidHom 2 : Fˣ →* Fˣ).ker
  rw [Subgroup.index_ker, hker, Nat.card_units] at h
  change Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range * 2 = _
  rw [← h, mul_comm]

theorem odd_card_unitSquares [Finite F] (hq : Nat.card F % 4 = 3) :
    Odd (Nat.card (unitSquares F)) := by
  have h := card_unitSquares_mul_two hq
  refine Nat.odd_iff.mpr ?_
  omega

theorem exists_sq_eq_neg_inv [Finite F] (hq : Nat.card F % 4 = 3) (a : Fˣ) (ha : ¬ IsSquare a) :
    ∃ l : Fˣ, l ^ 2 * (-a) = 1 := by
  rcases mem_unitSquares_or_neg hq a with h | h
  · exfalso
    obtain ⟨d, hd⟩ := h
    exact ha ⟨d, by rw [← hd, powMonoidHom_apply, pow_two]⟩
  · obtain ⟨d, hd⟩ := h
    refine ⟨d⁻¹, ?_⟩
    rw [← hd, powMonoidHom_apply, inv_pow, inv_mul_cancel]

@[expose] def scaledJ (a l : Fˣ) : MatrixCoverData.GL2 F :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) l * MatrixCoverData.J F a

theorem scaledJ_sq (a l : Fˣ) (hl : l ^ 2 * (-a) = 1) : scaledJ a l ^ 2 = 1 := by
  have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) l) (MatrixCoverData.J F a) :=
    Matrix.GeneralLinearGroup.scalar_commute l _
  rw [scaledJ, hc.mul_pow, MatrixCoverData.J_square, ← map_pow, ← map_mul, hl, map_one]

theorem scaledJ_det (a l : Fˣ) (hl : l ^ 2 * (-a) = 1) :
    Matrix.GeneralLinearGroup.det (scaledJ a l) = -1 := by
  rw [scaledJ, map_mul, Matrix.GeneralLinearGroup.det_scalar, MatrixCoverData.J_det,
    Fintype.card_fin]
  have : l ^ 2 * a = -(l ^ 2 * -a) := by rw [mul_neg, neg_neg]
  rw [this, hl]

theorem scaledJ_pow (a l : Fˣ) (k : ℕ) :
    scaledJ a l ^ k =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (l ^ k) * MatrixCoverData.J F a ^ k := by
  have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) l) (MatrixCoverData.J F a) :=
    Matrix.GeneralLinearGroup.scalar_commute l _
  rw [scaledJ, hc.mul_pow, map_pow]

theorem conj_scaledJ_pow (a l : Fˣ) (k : ℕ) (Y : MatrixCoverData.GL2 F) :
    scaledJ a l ^ k * Y * (scaledJ a l ^ k)⁻¹ =
      MatrixCoverData.J F a ^ k * Y * (MatrixCoverData.J F a ^ k)⁻¹ := by
  rw [scaledJ_pow]
  set c := Matrix.GeneralLinearGroup.scalar (Fin 2) (l ^ k)
  set X := MatrixCoverData.J F a ^ k
  calc c * X * Y * (c * X)⁻¹ = c * (X * Y * X⁻¹) * c⁻¹ := by group
    _ = (X * Y * X⁻¹) * c * c⁻¹ := by
      rw [Matrix.GeneralLinearGroup.scalar_commute (l ^ k) (X * Y * X⁻¹)]
    _ = X * Y * X⁻¹ := by group

@[expose] def scaledJHom (a l : Fˣ) (hl : l ^ 2 * (-a) = 1) :
    MatrixCoverData.C2 →* MatrixCoverData.GL2 F :=
  QuaternionAutomorphismLifting.coordinatePowerHom 2 (scaledJ a l) (scaledJ_sq a l hl)

theorem scaledJHom_apply (a l : Fˣ) (hl : l ^ 2 * (-a) = 1) (e : MatrixCoverData.C2) :
    scaledJHom a l hl e = scaledJ a l ^ MatrixCoverData.exponent e := rfl

@[expose] def modelEmbedding (a l : Fˣ) (hl : l ^ 2 * (-a) = 1) :
    MatrixCoverData.M F a →* MatrixCoverData.GL2 F :=
  SemidirectProduct.lift Matrix.SpecialLinearGroup.toGL (scaledJHom a l hl) (by
    intro e
    ext X : 1
    change Matrix.SpecialLinearGroup.toGL (MatrixCoverData.action F a e X) =
      scaledJHom a l hl e * Matrix.SpecialLinearGroup.toGL X * (scaledJHom a l hl e)⁻¹
    rw [MatrixCoverData.action_toGL, scaledJHom_apply, conj_scaledJ_pow])

theorem modelEmbedding_apply (a l : Fˣ) (hl : l ^ 2 * (-a) = 1) (x : MatrixCoverData.M F a) :
    modelEmbedding a l hl x =
      Matrix.SpecialLinearGroup.toGL x.left * scaledJ a l ^ MatrixCoverData.exponent x.right :=
  rfl

theorem det_modelEmbedding (a l : Fˣ) (hl : l ^ 2 * (-a) = 1) (x : MatrixCoverData.M F a) :
    Matrix.GeneralLinearGroup.det (modelEmbedding a l hl x) =
      (-1) ^ MatrixCoverData.exponent x.right := by
  rw [modelEmbedding_apply, map_mul, map_pow, scaledJ_det a l hl]
  have : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL x.left) = 1 := by
    apply Units.ext
    simp [Matrix.SpecialLinearGroup.toGL]
  rw [this, one_mul]

@[expose] def squaresProdModel (a l : Fˣ) (hl : l ^ 2 * (-a) = 1) :
    unitSquares F × MatrixCoverData.M F a →* MatrixCoverData.GL2 F :=
  MonoidHom.noncommCoprod
    ((Matrix.GeneralLinearGroup.scalar (Fin 2)).comp (unitSquares F).subtype)
    (modelEmbedding a l hl)
    (fun _ _ => Matrix.GeneralLinearGroup.scalar_commute _ _)

theorem squaresProdModel_apply (a l : Fˣ) (hl : l ^ 2 * (-a) = 1)
    (y : unitSquares F × MatrixCoverData.M F a) :
    squaresProdModel a l hl y =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (y.1 : Fˣ) * modelEmbedding a l hl y.2 := rfl

theorem exponent_eq_zero_or_one (e : MatrixCoverData.C2) :
    MatrixCoverData.exponent e = 0 ∨ MatrixCoverData.exponent e = 1 := by
  have := MatrixCoverData.exponent_lt_two e
  omega

theorem eq_one_of_exponent_eq_zero (e : MatrixCoverData.C2)
    (he : MatrixCoverData.exponent e = 0) : e = 1 := by
  have h : (Multiplicative.toAdd e).val = 0 := he
  rw [ZMod.val_eq_zero] at h
  exact h

theorem squaresProdModel_injective [Finite F] (hq : Nat.card F % 4 = 3) (a l : Fˣ)
    (hl : l ^ 2 * (-a) = 1) : Function.Injective (squaresProdModel a l hl) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨c, x⟩ hcx
  rw [squaresProdModel_apply] at hcx
  have hdet := congrArg Matrix.GeneralLinearGroup.det hcx
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, det_modelEmbedding, map_one,
    Fintype.card_fin] at hdet
  have hneg : (-1 : Fˣ) ≠ 1 := neg_one_ne_one_units hq
  rcases exponent_eq_zero_or_one x.right with h0 | h1
  · rw [h0, pow_zero, mul_one] at hdet
    have hc1 : (c : Fˣ) = 1 := eq_one_of_mem_unitSquares_of_sq hq c c.property hdet
    have hc : c = 1 := Subtype.ext hc1
    subst hc
    have hx1 : x.right = 1 := eq_one_of_exponent_eq_zero _ h0
    have hX : Matrix.SpecialLinearGroup.toGL x.left = 1 := by
      rw [modelEmbedding_apply, h0, pow_zero, mul_one] at hcx
      simpa using hcx
    have hleft : x.left = 1 := Matrix.SpecialLinearGroup.toGL_injective (by rw [hX, map_one])
    refine Prod.ext rfl ?_
    exact SemidirectProduct.ext hleft hx1
  · exfalso
    rw [h1, pow_one] at hdet
    apply sq_ne_neg_one_of_mem_unitSquares hq (c : Fˣ) c.property
    calc (c : Fˣ) ^ 2 = (c : Fˣ) ^ 2 * (-1) * (-1) := by
          rw [mul_assoc, neg_one_mul, neg_neg, mul_one]
      _ = -1 := by rw [hdet, one_mul]

theorem squaresProdModel_surjective [Finite F] (hq : Nat.card F % 4 = 3) (a l : Fˣ)
    (hl : l ^ 2 * (-a) = 1) : Function.Surjective (squaresProdModel a l hl) := by
  intro g
  set δ := Matrix.GeneralLinearGroup.det g with hδ
  have hsq : ∃ (c : Fˣ) (i : ℕ), c ∈ unitSquares F ∧ i < 2 ∧ δ = c ^ 2 * (-1) ^ i := by
    rcases mem_unitSquares_or_neg hq δ with h | h
    · obtain ⟨d, hd⟩ := h
      rcases mem_unitSquares_or_neg hq d with h' | h'
      · exact ⟨d, 0, h', by norm_num, by rw [← hd, powMonoidHom_apply, pow_zero, mul_one]⟩
      · exact ⟨-d, 0, h', by norm_num, by rw [← hd, powMonoidHom_apply, pow_zero, mul_one,
          neg_sq]⟩
    · obtain ⟨d, hd⟩ := h
      have hδ' : δ = d ^ 2 * (-1) := by
        rw [powMonoidHom_apply] at hd
        rw [hd, mul_neg_one, neg_neg]
      rcases mem_unitSquares_or_neg hq d with h' | h'
      · exact ⟨d, 1, h', by norm_num, by rw [hδ', pow_one]⟩
      · exact ⟨-d, 1, h', by norm_num, by rw [hδ', pow_one, neg_sq]⟩
  obtain ⟨c, i, hcU, hi, hδc⟩ := hsq
  set h : MatrixCoverData.GL2 F :=
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g * (scaledJ a l ^ i)⁻¹ with hh
  have hdeth : Matrix.GeneralLinearGroup.det h = 1 := by
    rw [hh, map_mul, map_mul, map_inv, map_inv, Matrix.GeneralLinearGroup.det_scalar, map_pow,
      scaledJ_det a l hl, Fintype.card_fin, ← hδ, hδc]
    group
  have hhmem : (h : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have := congrArg Units.val hdeth
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  let X : Matrix.SpecialLinearGroup (Fin 2) F := ⟨h, hhmem⟩
  have hX : Matrix.SpecialLinearGroup.toGL X = h := by
    apply Units.ext
    rfl
  let e : MatrixCoverData.C2 := Multiplicative.ofAdd (i : ZMod 2)
  have he : MatrixCoverData.exponent e = i := by
    change ((i : ZMod 2)).val = i
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  refine ⟨(⟨c, hcU⟩, ⟨X, e⟩), ?_⟩
  rw [squaresProdModel_apply, modelEmbedding_apply]
  change Matrix.GeneralLinearGroup.scalar (Fin 2) c *
    (Matrix.SpecialLinearGroup.toGL X * scaledJ a l ^ MatrixCoverData.exponent e) = g
  rw [hX, he, hh]
  group

@[expose] def squaresProdModelEquiv [Finite F] (hq : Nat.card F % 4 = 3) (a l : Fˣ)
    (hl : l ^ 2 * (-a) = 1) :
    unitSquares F × MatrixCoverData.M F a ≃* MatrixCoverData.GL2 F :=
  MulEquiv.ofBijective (squaresProdModel a l hl)
    ⟨squaresProdModel_injective hq a l hl, squaresProdModel_surjective hq a l hl⟩

theorem exists_surjective_hom_of_cyclic {A B : Type*} [Group A] [Group B] [Finite A]
    [IsCyclic A] [IsCyclic B] (h : Nat.card B ∣ Nat.card A) :
    ∃ χ : A →* B, Function.Surjective χ := by
  let eA := zmodCyclicMulEquiv (inferInstance : IsCyclic A)
  let eB := zmodCyclicMulEquiv (inferInstance : IsCyclic B)
  let cast : Multiplicative (ZMod (Nat.card A)) →* Multiplicative (ZMod (Nat.card B)) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod (Nat.card B))).toAddMonoidHom
  refine ⟨(eB.toMonoidHom.comp cast).comp eA.symm.toMonoidHom, ?_⟩
  intro b
  obtain ⟨z, hz⟩ := ZMod.castHom_surjective h (Multiplicative.toAdd (eB.symm b))
  refine ⟨eA (Multiplicative.ofAdd z), ?_⟩
  change eB (Multiplicative.ofAdd (ZMod.castHom h (ZMod (Nat.card B))
    (Multiplicative.toAdd (eA.symm (eA (Multiplicative.ofAdd z)))))) = b
  rw [MulEquiv.symm_apply_apply, toAdd_ofAdd, hz, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem exists_GL_quotient_equiv_prod [Finite F] (hq : Nat.card F % 4 = 3) (a : Fˣ)
    (ha : ¬ IsSquare a)
    (K : Type) [Group K] [Finite K] [IsCyclic K] (hK : Nat.card K ∣ (Nat.card F - 1) / 2) :
    ∃ (Z : Subgroup (GL (Fin 2) F)) (_ : Z.Normal),
      Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F ∧ Odd (Nat.card Z) ∧
      Nonempty (GL (Fin 2) F ⧸ Z ≃* K × MatrixCoverData.M F a) := by
  obtain ⟨l, hl⟩ := exists_sq_eq_neg_inv hq a ha
  let Ψ := squaresProdModelEquiv hq a l hl
  have hUcard : Nat.card (unitSquares F) = (Nat.card F - 1) / 2 := by
    have := card_unitSquares_mul_two hq
    omega
  have : IsCyclic (unitSquares F) := Subgroup.isCyclic _
  obtain ⟨χ, hχ⟩ := exists_surjective_hom_of_cyclic (A := unitSquares F) (B := K)
    (by rw [hUcard]; exact hK)
  let Θ : GL (Fin 2) F →* K × MatrixCoverData.M F a :=
    (χ.prodMap (MonoidHom.id _)).comp Ψ.symm.toMonoidHom
  have hΘ : Function.Surjective Θ := by
    intro y
    obtain ⟨c, hc⟩ := hχ y.1
    refine ⟨Ψ (c, y.2), ?_⟩
    change (χ (Ψ.symm (Ψ (c, y.2))).1, (Ψ.symm (Ψ (c, y.2))).2) = y
    rw [MulEquiv.symm_apply_apply, hc]
  have hfst : ∀ g ∈ Θ.ker, g = Matrix.GeneralLinearGroup.scalar (Fin 2) ((Ψ.symm g).1 : Fˣ) := by
    intro g hg
    have h2 : (Ψ.symm g).2 = 1 := congrArg Prod.snd hg
    calc g = Ψ (Ψ.symm g) := (MulEquiv.apply_symm_apply Ψ g).symm
      _ = Ψ ((Ψ.symm g).1, (Ψ.symm g).2) := rfl
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) ((Ψ.symm g).1 : Fˣ) := by
        rw [h2]
        change squaresProdModel a l hl ((Ψ.symm g).1, 1) = _
        rw [squaresProdModel_apply, map_one, mul_one]
  refine ⟨Θ.ker, inferInstance, ?_, ?_, ⟨QuotientGroup.quotientKerEquivOfSurjective Θ hΘ⟩⟩
  · intro g hg
    rw [hfst g hg]
    exact ⟨_, rfl⟩
  · let ι : Θ.ker →* unitSquares F :=
      { toFun := fun g => (Ψ.symm g).1
        map_one' := by simp
        map_mul' := fun g h => by simp }
    have hι : Function.Injective ι := by
      intro g h hgh
      apply Subtype.ext
      rw [hfst g g.property, hfst h h.property]
      exact congrArg (fun c : unitSquares F => Matrix.GeneralLinearGroup.scalar (Fin 2) (c : Fˣ))
        hgh
    exact Odd.of_dvd_nat (odd_card_unitSquares hq) (Subgroup.card_dvd_of_injective ι hι)

theorem stated_classical_model_psl_three_of_centralizer_prod
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : p ^ f % 4 = 3 ∧ 3 < p ^ f)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f) (a : Fˣ) (ha : ¬ IsSquare a)
    (K : Type) [Group K] [Finite K] [IsCyclic K] (hK : Nat.card K ∣ (p ^ f - 1) / 2)
    (x : G) (hx : orderOf x = 2)
    (e : Subgroup.centralizer ({x} : Set G) ≃* K × MatrixCoverData.M F a) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  have hq4 : Nat.card F % 4 = 3 := by rw [hF]; exact hq.1
  obtain ⟨Z, hZn, hZ, hZodd, ⟨eZ⟩⟩ :=
    exists_GL_quotient_equiv_prod hq4 a ha K (by rw [hF]; exact hK)
  exact CFSG.BrauerLinearThree.brauer_linear_three_involution_centralizer_q3mod4 p f hp hp2 hf hq
    G hnonab F hF Z hZ hZodd x hx (e.trans eZ.symm)

end

end CFSG.Semidihedral.SimpleLayerFrontier
