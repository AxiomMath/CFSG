module

public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierBrauer

public section

namespace CFSG.Wreathed.SameFieldLinearGL

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension

variable {F : Type} [Field F]

theorem scalar_mem_center (c : Fˣ) :
    GeneralLinearGroup.scalar (Fin 2) c ∈ Subgroup.center (GL (Fin 2) F) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

theorem scalar_mul_comm (c : Fˣ) (A : GL (Fin 2) F) :
    GeneralLinearGroup.scalar (Fin 2) c * A = A * GeneralLinearGroup.scalar (Fin 2) c :=
  (Subgroup.mem_center_iff.mp (scalar_mem_center c) A).symm

@[expose] noncomputable def scaledJ (b μ : Fˣ) : GL (Fin 2) F :=
  GeneralLinearGroup.scalar (Fin 2) μ * nonsquareMatrix F b

theorem scaledJ_sq (b μ : Fˣ) :
    scaledJ b μ ^ 2 = GeneralLinearGroup.scalar (Fin 2) (μ ^ 2 * -b) := by
  rw [scaledJ, pow_two, mul_assoc, ← mul_assoc (nonsquareMatrix F b),
    ← scalar_mul_comm μ (nonsquareMatrix F b), mul_assoc, ← pow_two, nonsquareMatrix_square,
    ← mul_assoc, ← map_mul, ← map_mul, pow_two]

theorem scaledJ_pow_two_mul (b μ : Fˣ) (k : ℕ) :
    scaledJ b μ ^ (2 * k) = GeneralLinearGroup.scalar (Fin 2) ((μ ^ 2 * -b) ^ k) := by
  rw [pow_mul, scaledJ_sq, map_pow]

theorem det_scaledJ (b μ : Fˣ) :
    GeneralLinearGroup.det (scaledJ b μ) = μ ^ 2 * b := by
  ext
  simp [scaledJ, nonsquareMatrix, Matrix.det_fin_two_of, GeneralLinearGroup.scalar]

theorem conj_scaledJ (b μ : Fˣ) (X : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL (beta F b X) =
      scaledJ b μ * SpecialLinearGroup.toGL X * (scaledJ b μ)⁻¹ := by
  rw [beta_toGL, scaledJ]
  set J := nonsquareMatrix F b
  set c := GeneralLinearGroup.scalar (Fin 2) μ
  set Y := SpecialLinearGroup.toGL X
  have hc : ∀ A : GL (Fin 2) F, c * A = A * c := scalar_mul_comm μ
  calc J * Y * J⁻¹ = J * Y * J⁻¹ * (c * c⁻¹) := by rw [mul_inv_cancel, mul_one]
    _ = J * Y * (c * J⁻¹) * c⁻¹ := by rw [hc J⁻¹]; group
    _ = c * (J * Y) * (c * c⁻¹) * (J⁻¹ * c⁻¹) := by rw [hc (J * Y)]; group
    _ = c * J * Y * (c * J)⁻¹ := by rw [mul_inv_cancel, mul_one, _root_.mul_inv_rev]; group

theorem toGL_beta_pow (b μ : Fˣ) (k : ℕ) (X : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL ((beta F b ^ k) X) =
      scaledJ b μ ^ k * SpecialLinearGroup.toGL X * (scaledJ b μ ^ k)⁻¹ := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, conj_scaledJ b μ, pow_succ]
    group

@[expose] noncomputable def cyclicHom (g : GL (Fin 2) F) (m : ℕ) (hm : 0 < m)
    (hg : g ^ (2 * m) = 1) : Multiplicative (ZMod (2 * m)) →* GL (Fin 2) F := by
  let : NeZero (2 * m) := ⟨by omega⟩
  exact {
    toFun := fun j => g ^ j.toAdd.val
    map_one' := by simp
    map_mul' := fun j k => by
      simp only [toAdd_mul, ZMod.val_add]
      rw [← pow_eq_pow_mod _ hg, pow_add] }

theorem cyclicHom_apply (g : GL (Fin 2) F) (m : ℕ) (hm : 0 < m) (hg : g ^ (2 * m) = 1)
    (j : Multiplicative (ZMod (2 * m))) : cyclicHom g m hm hg j = g ^ j.toAdd.val := rfl

theorem scaledJ_pow_two_mul_eq_one (b μ : Fˣ) (m : ℕ) (heven : Even m)
    (hμ : (μ ^ 2 * -b) ^ (m / 2) = -1) : scaledJ b μ ^ (2 * m) = 1 := by
  obtain ⟨r, rfl⟩ := heven
  have hr : (r + r) / 2 = r := by omega
  rw [hr] at hμ
  rw [show 2 * (r + r) = 2 * (2 * r) by ring, scaledJ_pow_two_mul, pow_mul, ← pow_mul,
    mul_comm 2 r, pow_mul, hμ]
  simp

theorem scaledJ_pow_eq_neg_one (b μ : Fˣ) (m : ℕ) (heven : Even m)
    (hμ : (μ ^ 2 * -b) ^ (m / 2) = -1) :
    scaledJ b μ ^ m = GeneralLinearGroup.scalar (Fin 2) (-1) := by
  obtain ⟨r, rfl⟩ := heven
  have hr : (r + r) / 2 = r := by omega
  rw [hr] at hμ
  rw [show r + r = 2 * r by ring, scaledJ_pow_two_mul, hμ]

@[expose] noncomputable def pairHom (b μ : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (hμ : (μ ^ 2 * -b) ^ (m / 2) = -1) : PairGroup F b m hm →* GL (Fin 2) F :=
  SemidirectProduct.lift SpecialLinearGroup.toGL
    (cyclicHom (scaledJ b μ) m hm (scaledJ_pow_two_mul_eq_one b μ m heven hμ)) (fun j => by
      ext X : 1
      change SpecialLinearGroup.toGL ((beta F b ^ j.toAdd.val) X) = _
      rw [toGL_beta_pow b μ]
      rfl)

theorem pairHom_pair (b μ : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (hμ : (μ ^ 2 * -b) ^ (m / 2) = -1) (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    pairHom b μ m hm heven hμ (pair F b m hm X j) =
      SpecialLinearGroup.toGL X * scaledJ b μ ^ j.val := rfl

theorem toGL_minusIdentity :
    SpecialLinearGroup.toGL (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      GeneralLinearGroup.scalar (Fin 2) (-1) := by
  rw [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar]

theorem diagonalKernel_le_ker (b μ : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (hμ : (μ ^ 2 * -b) ^ (m / 2) = -1) :
    diagonalKernel F b m hm heven ≤ (pairHom b μ m hm heven hμ).ker := by
  rw [diagonalKernel, Subgroup.zpowers_le, MonoidHom.mem_ker, diagonalInvolution, pairHom_pair,
    toGL_minusIdentity]
  have : NeZero (2 * m) := ⟨by omega⟩
  have hval : ((m : ℕ) : ZMod (2 * m)).val = m := ZMod.val_cast_of_lt (by omega)
  rw [hval, scaledJ_pow_eq_neg_one b μ m heven hμ, ← map_mul]
  simp

@[expose] noncomputable def centralEmbedding (b μ : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (hμ : (μ ^ 2 * -b) ^ (m / 2) = -1) : CentralExtension F b m hm heven →* GL (Fin 2) F :=
  QuotientGroup.lift _ (pairHom b μ m hm heven hμ) (diagonalKernel_le_ker b μ m hm heven hμ)

theorem centralEmbedding_quotientClass (b μ : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (hμ : (μ ^ 2 * -b) ^ (m / 2) = -1) (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    centralEmbedding b μ m hm heven hμ (quotientClass F b m hm heven X j) =
      SpecialLinearGroup.toGL X * scaledJ b μ ^ j.val := rfl

theorem orderOf_det_scaledJ (b μ : Fˣ) (n : ℕ) (hn : 2 ≤ n)
    (hμ : (μ ^ 2 * -b) ^ (2 ^ n / 2) = -1) (hneg : (-1 : Fˣ) ≠ 1) :
    orderOf (μ ^ 2 * b) = 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; omega
  rw [hk] at hμ
  have heven : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
  have h1 : (μ ^ 2 * b) ^ 2 ^ k = -1 := by
    rw [show μ ^ 2 * b = -(μ ^ 2 * -b) by rw [mul_neg, neg_neg], heven.neg_pow, hμ]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_pow (by rw [h1]; exact hneg) ?_
  rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul, h1]
  simp

theorem centralEmbedding_injective (b μ : Fˣ) (n : ℕ) (hn : 2 ≤ n)
    (hμ : (μ ^ 2 * -b) ^ (2 ^ n / 2) = -1) (hneg : (-1 : Fˣ) ≠ 1) :
    Function.Injective (centralEmbedding b μ (2 ^ n) (by positivity)
      ((Nat.even_pow' (by omega)).mpr even_two) hμ) := by
  set m := 2 ^ n with hmdef
  have hm : 0 < m := by positivity
  have heven : Even m := (Nat.even_pow' (by omega)).mpr even_two
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [injective_iff_map_eq_one]
  intro w hw
  induction w using QuotientGroup.induction_on with
  | H x =>
  have hx : x = pair F b m hm x.left x.right.toAdd := rfl
  rw [hx] at hw ⊢
  set X := x.left
  set j := x.right.toAdd
  change SpecialLinearGroup.toGL X * scaledJ b μ ^ j.val = 1 at hw
  have hdet := congrArg GeneralLinearGroup.det hw
  rw [map_mul, map_pow, det_scaledJ, map_one] at hdet
  have hX1 : GeneralLinearGroup.det (SpecialLinearGroup.toGL X) = 1 := by
    ext
    simp [SpecialLinearGroup.toGL]
  rw [hX1, one_mul] at hdet
  have hdvd : m ∣ j.val := by
    have h := orderOf_dvd_of_pow_eq_one hdet
    rwa [orderOf_det_scaledJ b μ n hn hμ hneg] at h
  have hlt : j.val < 2 * m := ZMod.val_lt j
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c = 0 ∨ c = 1 := by
    have : m * c < m * 2 := by rw [← hc]; omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  rcases hc2 with rfl | rfl
  ·
    have hj : j = 0 := (ZMod.val_eq_zero j).mp (by rw [hc]; ring)
    rw [hj] at hw ⊢
    rw [ZMod.val_zero, pow_zero, mul_one] at hw
    have hX : X = 1 := SpecialLinearGroup.toGL_injective (by rw [hw, map_one])
    rw [hX]
    rfl
  ·
    have hj : j = (m : ZMod (2 * m)) := by
      apply ZMod.val_injective
      rw [ZMod.val_cast_of_lt (by omega), hc, mul_one]
    rw [hj, ZMod.val_cast_of_lt (by omega), scaledJ_pow_eq_neg_one b μ m heven
      (by rw [hmdef]; exact hμ)] at hw
    have hX : X = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_minusIdentity]
      calc SpecialLinearGroup.toGL X = SpecialLinearGroup.toGL X *
            GeneralLinearGroup.scalar (Fin 2) (-1) * GeneralLinearGroup.scalar (Fin 2) (-1) := by
              rw [mul_assoc, ← map_mul]; simp
        _ = GeneralLinearGroup.scalar (Fin 2) (-1) := by rw [hw, one_mul]
    rw [hX, hj]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

theorem exists_GL_quotient_equiv_prod_of_decomposition {W : Type} [Group W] (O : Subgroup Fˣ)
    [Finite O] [IsCyclic O] (hO : Odd (Nat.card O)) (Ψ : O × W ≃* GL (Fin 2) F)
    (hΨ : ∀ c : O, Ψ (c, 1) = GeneralLinearGroup.scalar (Fin 2) (c : Fˣ))
    (K : Type) [Group K] [IsCyclic K] (hK : Nat.card K ∣ Nat.card O) :
    ∃ (Z : Subgroup (GL (Fin 2) F)) (_ : Z.Normal),
      Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F ∧ Odd (Nat.card Z) ∧
      Nonempty (GL (Fin 2) F ⧸ Z ≃* K × W) := by
  obtain ⟨χ, hχ⟩ := CFSG.Semidihedral.SimpleLayerFrontier.exists_surjective_hom_of_cyclic
    (A := O) (B := K) hK
  let Θ : GL (Fin 2) F →* K × W := (χ.prodMap (MonoidHom.id _)).comp Ψ.symm.toMonoidHom
  have hΘ : Function.Surjective Θ := by
    intro y
    obtain ⟨c, hc⟩ := hχ y.1
    refine ⟨Ψ (c, y.2), ?_⟩
    change (χ (Ψ.symm (Ψ (c, y.2))).1, (Ψ.symm (Ψ (c, y.2))).2) = y
    rw [MulEquiv.symm_apply_apply, hc]
  have hfst : ∀ g ∈ Θ.ker, g = GeneralLinearGroup.scalar (Fin 2) ((Ψ.symm g).1 : Fˣ) := by
    intro g hg
    have h2 : (Ψ.symm g).2 = 1 := congrArg Prod.snd hg
    calc g = Ψ (Ψ.symm g) := (MulEquiv.apply_symm_apply Ψ g).symm
      _ = Ψ ((Ψ.symm g).1, (Ψ.symm g).2) := rfl
      _ = GeneralLinearGroup.scalar (Fin 2) ((Ψ.symm g).1 : Fˣ) := by rw [h2, hΨ]
  refine ⟨Θ.ker, inferInstance, ?_, ?_, ⟨QuotientGroup.quotientKerEquivOfSurjective Θ hΘ⟩⟩
  · intro g hg
    rw [hfst g hg]
    exact ⟨_, rfl⟩
  · let ι : Θ.ker →* O :=
      { toFun := fun g => (Ψ.symm g).1
        map_one' := by simp
        map_mul' := fun g h => by simp }
    have hι : Function.Injective ι := by
      intro g h hgh
      apply Subtype.ext
      rw [hfst g g.property, hfst h h.property]
      exact congrArg (fun c : O => GeneralLinearGroup.scalar (Fin 2) (c : Fˣ)) hgh
    exact Odd.of_dvd_nat hO (Subgroup.card_dvd_of_injective ι hι)

@[expose] noncomputable def scalarProd (b μ : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (hμ : (μ ^ 2 * -b) ^ (m / 2) = -1) (O : Subgroup Fˣ) :
    O × CentralExtension F b m hm heven →* GL (Fin 2) F where
  toFun x := GeneralLinearGroup.scalar (Fin 2) (x.1 : Fˣ) * centralEmbedding b μ m hm heven hμ x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (centralEmbedding b μ m hm heven hμ x.2),
      ← scalar_mul_comm (y.1 : Fˣ) (centralEmbedding b μ m hm heven hμ x.2)]
    group

theorem det_centralEmbedding_pow (b μ : Fˣ) (n : ℕ) (hn : 2 ≤ n)
    (hμ : (μ ^ 2 * -b) ^ (2 ^ n / 2) = -1) (hneg : (-1 : Fˣ) ≠ 1)
    (w : CentralExtension F b (2 ^ n) (by positivity) ((Nat.even_pow' (by omega)).mpr even_two)) :
    GeneralLinearGroup.det (centralEmbedding b μ (2 ^ n) (by positivity)
      ((Nat.even_pow' (by omega)).mpr even_two) hμ w) ^ 2 ^ n = 1 := by
  induction w using QuotientGroup.induction_on with
  | H x =>
  have hx : x = pair F b (2 ^ n) (by positivity) x.left x.right.toAdd := rfl
  rw [hx]
  change GeneralLinearGroup.det (SpecialLinearGroup.toGL x.left *
    scaledJ b μ ^ x.right.toAdd.val) ^ 2 ^ n = 1
  have hX1 : GeneralLinearGroup.det (SpecialLinearGroup.toGL x.left) = 1 := by
    ext
    simp [SpecialLinearGroup.toGL]
  have h1 : (μ ^ 2 * b) ^ 2 ^ n = 1 := by
    have := pow_orderOf_eq_one (μ ^ 2 * b)
    rwa [orderOf_det_scaledJ b μ n hn hμ hneg] at this
  rw [map_mul, hX1, one_mul, map_pow, det_scaledJ, ← pow_mul, mul_comm x.right.toAdd.val,
    pow_mul, h1, one_pow]

theorem scalarProd_injective (b μ : Fˣ) (n : ℕ) (hn : 2 ≤ n)
    (hμ : (μ ^ 2 * -b) ^ (2 ^ n / 2) = -1) (hneg : (-1 : Fˣ) ≠ 1) (O : Subgroup Fˣ)
    (hO : ∀ c ∈ O, c ^ Nat.card O = 1) (hOodd : Odd (Nat.card O)) :
    Function.Injective (scalarProd b μ (2 ^ n) (by positivity)
      ((Nat.even_pow' (by omega)).mpr even_two) hμ O) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨c, w⟩ h
  change GeneralLinearGroup.scalar (Fin 2) (c : Fˣ) *
    centralEmbedding b μ (2 ^ n) _ _ hμ w = 1 at h
  have hdet := congrArg GeneralLinearGroup.det h
  rw [map_mul, map_one] at hdet
  have hscal : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (c : Fˣ)) =
      (c : Fˣ) ^ 2 := by
    ext
    simp [GeneralLinearGroup.scalar]
  rw [hscal] at hdet
  set d := GeneralLinearGroup.det (centralEmbedding b μ (2 ^ n) (by positivity)
    ((Nat.even_pow' (by omega)).mpr even_two) hμ w)
  have hd2 : d ^ 2 ^ n = 1 := det_centralEmbedding_pow b μ n hn hμ hneg w
  have hck : (c : Fˣ) ^ Nat.card O = 1 := hO c c.2
  have hdk : d ^ Nat.card O = 1 := by
    have : d = ((c : Fˣ) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    rw [this, inv_pow, ← pow_mul, mul_comm, pow_mul, hck, one_pow, inv_one]
  have hcop : Nat.gcd (Nat.card O) (2 ^ n) = 1 :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hOodd)
  have hd : d = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hdk, hd2⟩
    rwa [hcop, pow_one] at this
  rw [hd, mul_one] at hdet
  have hc1 : (c : Fˣ) = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hck, hdet⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hOodd), pow_one] at this
  have hc : c = 1 := Subtype.ext hc1
  subst hc
  rw [OneMemClass.coe_one, map_one, one_mul] at h
  have hw : w = 1 := centralEmbedding_injective b μ n hn hμ hneg (by rw [h, map_one])
  rw [hw]
  rfl

section Finite

variable [Finite F]

theorem exists_mu (n k : ℕ) (hn : 2 ≤ n) (hk : Odd k) (hcard : Nat.card Fˣ = 2 ^ n * k)
    (b : Fˣ) (hb : ¬ IsSquare b) : ∃ μ : Fˣ, (μ ^ 2 * -b) ^ (2 ^ n / 2) = -1 := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf γ = 2 ^ n * k := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨e, he⟩ : ∃ e : ℕ, γ ^ e = b := mem_powers_iff_mem_zpowers.mpr (hγ b)
  have heodd : Odd e := by
    by_contra hev
    obtain ⟨t, rfl⟩ := Nat.not_odd_iff_even.mp hev
    exact hb ⟨γ ^ t, by rw [← he, pow_add]⟩
  obtain ⟨h, hh⟩ : ∃ h, 2 ^ n = 2 * h := ⟨2 ^ (n - 1), by
    rw [← pow_succ']; congr 1; omega⟩
  have hheven : Even h := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    refine ⟨2 ^ j, ?_⟩
    have : 2 ^ (j + 2) = 2 * (2 ^ j + 2 ^ j) := by ring
    omega
  have hhalf : 2 ^ n / 2 = h := by omega
  have hkpos : 0 < k := hk.pos
  have hhpos : 0 < h := by
    have := Nat.one_le_two_pow (n := n)
    omega
  have hneg : γ ^ (h * k) = -1 := by
    rcases CFSG.Semidihedral.SimpleLayerFrontier.eq_one_or_neg_one_of_sq (γ ^ (h * k)) (by
        rw [← pow_mul, show h * k * 2 = 2 ^ n * k by rw [hh]; ring, ← hord,
          pow_orderOf_eq_one]) with h1 | h1
    · exfalso
      refine pow_ne_one_of_lt_orderOf (Nat.mul_ne_zero (by omega) (by omega)) ?_ h1
      rw [hord, hh]
      have := Nat.mul_pos hhpos hkpos
      nlinarith
    · exact h1
  have hA : e + h * k ≤ k * (e + 2 ^ n) := by
    have h1 : e ≤ k * e := Nat.le_mul_of_pos_left e hkpos
    have h2 : h * k ≤ k * 2 ^ n := by rw [hh]; nlinarith
    nlinarith
  obtain ⟨x, hx⟩ : ∃ x, 2 * x + h * k + e = 2 * (k * (e + 2 ^ n)) + k := by
    obtain ⟨e', rfl⟩ := heodd
    obtain ⟨k', rfl⟩ := hk
    obtain ⟨h', rfl⟩ := hheven
    refine ⟨(2 * ((2 * k' + 1) * (2 * e' + 1 + 2 ^ n)) + (2 * k' + 1) - (h' + h') * (2 * k' + 1)
      - (2 * e' + 1)) / 2, ?_⟩
    have hA' := hA
    have : (h' + h') * (2 * k' + 1) = 2 * (h' * (2 * k' + 1)) := by ring
    omega
  refine ⟨γ ^ x, ?_⟩
  have hb' : -b = γ ^ (h * k + e) := by rw [pow_add, hneg, he, neg_one_mul]
  have hbase : (γ ^ x) ^ 2 * -b = γ ^ (2 * (k * (e + 2 ^ n)) + k) := by
    rw [hb', ← pow_mul, ← pow_add, mul_comm x 2, ← add_assoc, hx]
  rw [hhalf, hbase, ← pow_mul]
  have h1 : (2 * (k * (e + 2 ^ n)) + k) * h = (2 ^ n * k) * (e + 2 ^ n) + h * k := by
    rw [hh]; ring
  rw [h1, pow_add, pow_mul, ← hord, pow_orderOf_eq_one, one_pow, one_mul, hneg]

theorem exists_scalarProd_equiv (n k : ℕ) (hn : 2 ≤ n) (hk : Odd k)
    (hcard : Nat.card Fˣ = 2 ^ n * k) (b μ : Fˣ) (hμ : (μ ^ 2 * -b) ^ (2 ^ n / 2) = -1)
    (hneg : (-1 : Fˣ) ≠ 1) :
    ∃ O : Subgroup Fˣ, Nat.card O = k ∧ IsCyclic O ∧
      Function.Bijective (scalarProd b μ (2 ^ n) (by positivity)
        ((Nat.even_pow' (by omega)).mpr even_two) hμ O) := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf γ = 2 ^ n * k := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hγ
  let O : Subgroup Fˣ := Subgroup.zpowers (γ ^ 2 ^ n)
  have hOcard : Nat.card O = k := by
    rw [Nat.card_zpowers, orderOf_pow' _ (by positivity), hord,
      Nat.gcd_eq_right (dvd_mul_right _ _)]
    exact Nat.mul_div_cancel_left k (by positivity)
  refine ⟨O, hOcard, inferInstance, ?_⟩
  have hO : ∀ c ∈ O, c ^ Nat.card O = 1 := fun c hc => by
    have : (⟨c, hc⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
    exact congrArg Subtype.val this
  have hinj := scalarProd_injective b μ n hn hμ hneg O hO (by rw [hOcard]; exact hk)
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [Nat.card_prod, hOcard, CFSG.Wreathed.CentralSL2.card_centralExtension,
    ← Matrix.card_SL_mul_card_units, hcard]
  ring

theorem exists_GL_quotient_equiv_prod_centralExtension (n k : ℕ) (hn : 2 ≤ n) (hk : Odd k)
    (hcard : Nat.card Fˣ = 2 ^ n * k) (b : Fˣ) (hb : ¬ IsSquare b) (hneg : (-1 : Fˣ) ≠ 1)
    (K : Type) [Group K] [IsCyclic K] (hK : Nat.card K ∣ k) :
    ∃ (Z : Subgroup (GL (Fin 2) F)) (_ : Z.Normal),
      Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F ∧ Odd (Nat.card Z) ∧
      Nonempty (GL (Fin 2) F ⧸ Z ≃* K × CentralExtension F b (2 ^ n) (by positivity)
        ((Nat.even_pow' (by omega)).mpr even_two)) := by
  obtain ⟨μ, hμ⟩ := exists_mu n k hn hk hcard b hb
  obtain ⟨O, hOcard, hOcyc, hbij⟩ := exists_scalarProd_equiv n k hn hk hcard b μ hμ hneg
  let Ψ := MulEquiv.ofBijective _ hbij
  have hΨ : ∀ c : O, Ψ (c, 1) = GeneralLinearGroup.scalar (Fin 2) (c : Fˣ) := fun c => by
    change GeneralLinearGroup.scalar (Fin 2) (c : Fˣ) * centralEmbedding b μ (2 ^ n) _ _ hμ 1 = _
    rw [map_one, mul_one]
  exact exists_GL_quotient_equiv_prod_of_decomposition O (by rw [hOcard]; exact hk) Ψ hΨ K
    (by rw [hOcard]; exact hK)

end Finite

end CFSG.Wreathed.SameFieldLinearGL
