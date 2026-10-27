module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI
public import CFSG.Open.PGLModelDefs
public import CFSG.Open.Catalog
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order

public section

open Matrix

namespace CFSG.Adapters.RankTwoModelTransports


@[expose] noncomputable def specialLinearGroupCongr (n : Type*) [Fintype n] [DecidableEq n]
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SpecialLinearGroup n R ≃* SpecialLinearGroup n S where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  right_inv A := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  map_mul' A B := map_mul _ A B

@[expose] noncomputable def projectiveSpecialLinearGroupCongr (n : Type*) [Fintype n]
    [DecidableEq n]
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    ProjectiveSpecialLinearGroup n R ≃* ProjectiveSpecialLinearGroup n S :=
  QuotientGroup.congr _ _ (specialLinearGroupCongr n e)
    (Subgroup.map_center_eq (specialLinearGroupCongr n e))

theorem nonempty_mulEquiv_psl_galoisField (G : Type) [Group G] (n p f : ℕ) [Fact p.Prime]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL n p f) :
    Nonempty (G ≃* ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf : f ≠ 0 := by
    rintro rfl
    exact absurd hadm.2.1 (by omega)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField p f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card p f hf]
  exact ⟨e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (projectiveSpecialLinearGroupCongr (Fin n) (FiniteField.ringEquivOfCardEq hcard)))⟩



section Projective

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def statedProjEquivMapMk {K : Type} [Field K] (H : Subgroup (GL ι K)) :
    CFSG.Assembly.LowTwoRank.StatedProj H ≃* (H.map (ProjGenLinGroup.mk : GL ι K →* _)) :=
  (CFSG.Open.StatedAPI.mapMkEquivStatedProj H).symm

@[expose] noncomputable def statedProjEquivProjImage {K : Type} [Field K] (H : Subgroup (GL ι K))
    {P : Subgroup (ProjGenLinGroup ι K)} (hP : CFSG.PGLModel.projImage H = P) :
    CFSG.Assembly.LowTwoRank.StatedProj H ≃* P :=
  (statedProjEquivMapMk H).trans (MulEquiv.subgroupCongr hP)

@[expose] noncomputable def statedProjCongr {K L : Type} [Field K] [Field L]
    (Φ : GL ι K ≃* GL ι L) {H : Subgroup (GL ι K)} {H' : Subgroup (GL ι L)}
    (hH : H.map Φ.toMonoidHom = H')
    (hZ : (CFSG.Assembly.LowTwoRank.StatedScalars ι K).map Φ.toMonoidHom =
      CFSG.Assembly.LowTwoRank.StatedScalars ι L) :
    CFSG.Assembly.LowTwoRank.StatedProj H ≃* CFSG.Assembly.LowTwoRank.StatedProj H' := by
  let E : H ≃* H' := (H.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
    (MulEquiv.subgroupCongr hH)
  refine QuotientGroup.congr _ _ E ?_
  ext x
  obtain ⟨h, rfl⟩ := E.surjective x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨h', hh', hEq⟩
    have hh : h' = h := E.injective hEq
    subst hh
    have : Φ h' ∈ (CFSG.Assembly.LowTwoRank.StatedScalars ι K).map Φ.toMonoidHom :=
      ⟨h', hh', rfl⟩
    rw [hZ] at this
    exact this
  · intro hx
    refine ⟨h, ?_, rfl⟩
    have hx' : Φ (h : GL ι K) ∈ CFSG.Assembly.LowTwoRank.StatedScalars ι L := hx
    rw [← hZ] at hx'
    obtain ⟨g, hg, hgh⟩ := hx'
    rwa [Φ.injective hgh] at hg



end Projective

section FieldTransport

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def glCongr {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    GL ι K ≃* GL ι L :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := ι) e).toMulEquiv

theorem glCongr_coe {K L : Type} [Field K] [Field L] (e : K ≃+* L) (A : GL ι K) :
    ((glCongr e A : GL ι L) : Matrix ι ι L) = (A : Matrix ι ι K).map e := rfl

theorem glCongr_symm_coe {K L : Type} [Field K] [Field L] (e : K ≃+* L) (B : GL ι L) :
    (((glCongr e).symm B : GL ι K) : Matrix ι ι K) = (B : Matrix ι ι L).map e.symm := rfl

theorem glCongr_statedScalars {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    (CFSG.Assembly.LowTwoRank.StatedScalars ι K).map (glCongr (ι := ι) e).toMonoidHom =
      CFSG.Assembly.LowTwoRank.StatedScalars ι L := by
  ext B
  simp only [Subgroup.mem_map, CFSG.Assembly.LowTwoRank.StatedScalars, MonoidHom.mem_range,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
    refine ⟨Units.map e.toRingHom.toMonoidHom c, Units.ext ?_⟩
    rw [glCongr_coe, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  · rintro ⟨d, rfl⟩
    refine ⟨_, ⟨Units.map e.symm.toRingHom.toMonoidHom d, rfl⟩, Units.ext ?_⟩
    rw [glCongr_coe, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp




end FieldTransport

theorem det_map_ringEquiv {n : Type} [Fintype n] [DecidableEq n] {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) (A : Matrix n n K) : (A.map e).det = e A.det :=
  (RingHom.map_det e.toRingHom A).symm

theorem hermitian_map_ringEquiv {n : Type} [Fintype n] [DecidableEq n] {K L : Type} [Field K]
    [Field L] (e : K ≃+* L) (q : ℕ) (A : Matrix n n K) :
    ((A.map e).map (· ^ q))ᵀ * A.map e = (((A.map (· ^ q))ᵀ * A).map e) := by
  rw [Matrix.map_mul, Matrix.transpose_map]
  congr 2
  ext i j
  simp [map_pow]

theorem glCongr_statedSU {K L : Type} [Field K] [Field L] (e : K ≃+* L) (n q : ℕ) :
    (CFSG.Assembly.LowTwoRank.StatedSU n q K).map (glCongr (ι := Fin n) e).toMonoidHom =
      CFSG.Assembly.LowTwoRank.StatedSU n q L := by
  unfold CFSG.Assembly.LowTwoRank.StatedSU
  rw [MonoidHom.map_closure]
  congr 1
  ext B
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨A, ⟨hdet, hU⟩, rfl⟩
    rw [glCongr_coe, det_map_ringEquiv, hdet, map_one, hermitian_map_ringEquiv, hU,
      Matrix.map_one _ (map_zero e) (map_one e)]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hdet, hU⟩
    refine ⟨(glCongr e).symm B, ⟨?_, ?_⟩, MulEquiv.apply_symm_apply _ _⟩
    · rw [glCongr_symm_coe, det_map_ringEquiv, hdet, map_one]
    · rw [glCongr_symm_coe, hermitian_map_ringEquiv, hU,
        Matrix.map_one _ (map_zero e.symm) (map_one e.symm)]


theorem odd_sq_arith (q r : ℕ) (hr : q = 2 * r + 1) :
    r * (q + 1) = (q ^ 2 - 1) / 2 ∧ (q ^ 2 - 1) / 2 * 2 = q ^ 2 - 1 := by
  subst hr
  have h1 : (2 * r + 1) ^ 2 = 2 * (r * (2 * r + 1 + 1)) + 1 := by ring
  constructor <;> omega

theorem exists_pow_succ_eq_neg_one (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hk : k ≠ 0) :
    ∃ a : GaloisField p (2 * k), a ^ (p ^ k + 1) = -1 := by
  classical
  let L := GaloisField p (2 * k)
  set q := p ^ k with hq
  have hq1 : 1 < q := Nat.one_lt_pow hk (Fact.out : p.Prime).one_lt
  have hcard : Nat.card L = q ^ 2 := by
    rw [GaloisField.card p (2 * k) (by omega), hq, ← pow_mul, mul_comm]
  let _ : Fintype L := Fintype.ofFinite L
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  have hgo : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have hqodd : Odd q := (((Fact.out : p.Prime).eq_two_or_odd').resolve_left hp).pow
  obtain ⟨r, hr⟩ := hqodd
  refine ⟨((g ^ r : Lˣ) : L), ?_⟩
  have hw : (g ^ r) ^ (q + 1) = g ^ ((q ^ 2 - 1) / 2) := by
    rw [← pow_mul, (odd_sq_arith q r hr).1]
  have hsq : (g ^ ((q ^ 2 - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, (odd_sq_arith q r hr).2, ← hgo, pow_orderOf_eq_one]
  have hne : g ^ ((q ^ 2 - 1) / 2) ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hgo] at hdvd
    have h2 := (odd_sq_arith q r hr).2
    have hq2 : 1 < q ^ 2 := by nlinarith
    have hpos : 0 < (q ^ 2 - 1) / 2 := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  have hm1 : ((g ^ ((q ^ 2 - 1) / 2) : Lˣ) : L) = -1 := by
    have h2 : ((g ^ ((q ^ 2 - 1) / 2) : Lˣ) : L) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact absurd (Units.ext h) hne
    · exact h
  rw [← Units.val_pow_eq_pow_val, hw, hm1]


section SLSpTransport

open CFSG.Assembly.LowTwoRank

variable {K L : Type} [Field K] [Field L] (φ : K ≃+* L)

theorem glCongr_statedSL (n : ℕ) :
    (StatedSL n K).map (glCongr (ι := Fin n) φ).toMonoidHom = StatedSL n L := by
  unfold StatedSL
  rw [MonoidHom.map_closure]
  congr 1
  ext B
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨A, hdet, rfl⟩
    rw [glCongr_coe, det_map_ringEquiv, hdet, map_one]
  · intro hdet
    refine ⟨(glCongr φ).symm B, ?_, MulEquiv.apply_symm_apply _ _⟩
    have h := det_map_ringEquiv φ (((glCongr φ).symm B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [← glCongr_coe, MulEquiv.apply_symm_apply, hdet] at h
    exact φ.injective (by rw [← h, map_one])

theorem glCongr_statedSp (n : ℕ) :
    (StatedSp n K).map (glCongr (ι := Fin n ⊕ Fin n) φ).toMonoidHom = StatedSp n L := by
  have hJ : (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
      (-1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K)).map φ =
      Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) L) (1 : Matrix (Fin n) (Fin n) L)
        (-1 : Matrix (Fin n) (Fin n) L) (0 : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.fromBlocks_map]
    simp [Matrix.map_zero, Matrix.map_one, Matrix.map_neg]
  have hiff : ∀ A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
      (A.map φ)ᵀ * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) L) (1 : Matrix (Fin n) (Fin n) L)
          (-1 : Matrix (Fin n) (Fin n) L) (0 : Matrix (Fin n) (Fin n) L) * A.map φ =
          Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) L) (1 : Matrix (Fin n) (Fin n) L)
            (-1 : Matrix (Fin n) (Fin n) L) (0 : Matrix (Fin n) (Fin n) L) ↔
        Aᵀ * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
            (-1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) * A =
          Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
            (-1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) := by
    intro A
    rw [← hJ, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    constructor
    · intro h
      exact Matrix.map_injective φ.injective h
    · intro h
      rw [h]
  unfold StatedSp
  rw [MonoidHom.map_closure]
  congr 1
  ext B
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [glCongr_coe]
    exact (hiff _).2 hA
  · intro hB
    refine ⟨(glCongr φ).symm B, ?_, MulEquiv.apply_symm_apply _ _⟩
    have hB' : (((glCongr φ) ((glCongr φ).symm B) : GL (Fin n ⊕ Fin n) L) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) =
        (((glCongr φ).symm B : GL (Fin n ⊕ Fin n) K) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map φ := glCongr_coe φ _
    rw [MulEquiv.apply_symm_apply] at hB'
    rw [hB'] at hB
    exact (hiff _).1 hB

end SLSpTransport

section Hermitian

variable {L : Type} [Field L]

abbrev M3 (L : Type) [Field L] := Matrix (Fin 3) (Fin 3) L

@[expose] def hcσ (σ : L →+* L) (A : M3 L) : M3 L := (A.map σ)ᵀ

theorem hcσ_mul (σ : L →+* L) (A B : M3 L) : hcσ σ (A * B) = hcσ σ B * hcσ σ A := by
  unfold hcσ
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem hcσ_one (σ : L →+* L) : hcσ σ (1 : M3 L) = 1 := by
  unfold hcσ
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem hcσ_inv_mul (σ : L →+* L) (P : GL (Fin 3) L) :
    hcσ σ ((P⁻¹ : GL (Fin 3) L) : M3 L) * hcσ σ (P : M3 L) = 1 := by
  rw [← hcσ_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, hcσ_one]

theorem val_mul_inv (P : GL (Fin 3) L) : (P : M3 L) * ((P⁻¹ : GL (Fin 3) L) : M3 L) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conj_unitary (σ : L →+* L) (J : M3 L) (P A : GL (Fin 3) L)
    (hP : hcσ σ (P : M3 L) * J * (P : M3 L) = 1)
    (hA : hcσ σ (A : M3 L) * (A : M3 L) = 1) :
    hcσ σ ((P * A * P⁻¹ : GL (Fin 3) L) : M3 L) * J *
      ((P * A * P⁻¹ : GL (Fin 3) L) : M3 L) = J := by
  set Pm : M3 L := (P : M3 L)
  set Qm : M3 L := ((P⁻¹ : GL (Fin 3) L) : M3 L)
  set Am : M3 L := (A : M3 L)
  have hJ : hcσ σ Qm * Qm = J := by
    calc hcσ σ Qm * Qm = hcσ σ Qm * (hcσ σ Pm * J * Pm) * Qm := by rw [hP, Matrix.mul_one]
      _ = (hcσ σ Qm * hcσ σ Pm) * J * (Pm * Qm) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hcσ_inv_mul, val_mul_inv, Matrix.one_mul, Matrix.mul_one]
  have hcoe : ((P * A * P⁻¹ : GL (Fin 3) L) : M3 L) = Pm * Am * Qm := by
    simp only [Units.val_mul, Pm, Am, Qm]
  rw [hcoe, hcσ_mul, hcσ_mul]
  calc hcσ σ Qm * (hcσ σ Am * hcσ σ Pm) * J * (Pm * Am * Qm)
      = hcσ σ Qm * hcσ σ Am * (hcσ σ Pm * J * Pm) * Am * Qm := by simp only [Matrix.mul_assoc]
    _ = hcσ σ Qm * (hcσ σ Am * Am) * Qm := by rw [hP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hA, Matrix.mul_one, hJ]

theorem conj_unitary_inv (σ : L →+* L) (J : M3 L) (P B : GL (Fin 3) L)
    (hP : hcσ σ (P : M3 L) * J * (P : M3 L) = 1)
    (hB : hcσ σ (B : M3 L) * J * (B : M3 L) = J) :
    hcσ σ ((P⁻¹ * B * P : GL (Fin 3) L) : M3 L) * ((P⁻¹ * B * P : GL (Fin 3) L) : M3 L) = 1 := by
  set Pm : M3 L := (P : M3 L)
  set Qm : M3 L := ((P⁻¹ : GL (Fin 3) L) : M3 L)
  set Bm : M3 L := (B : M3 L)
  have hJ : hcσ σ Qm * Qm = J := by
    calc hcσ σ Qm * Qm = hcσ σ Qm * (hcσ σ Pm * J * Pm) * Qm := by rw [hP, Matrix.mul_one]
      _ = (hcσ σ Qm * hcσ σ Pm) * J * (Pm * Qm) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hcσ_inv_mul, val_mul_inv, Matrix.one_mul, Matrix.mul_one]
  have hcoe : ((P⁻¹ * B * P : GL (Fin 3) L) : M3 L) = Qm * Bm * Pm := by
    simp only [Units.val_mul, Pm, Bm, Qm]
  rw [hcoe, hcσ_mul, hcσ_mul]
  calc hcσ σ Pm * (hcσ σ Bm * hcσ σ Qm) * (Qm * Bm * Pm)
      = hcσ σ Pm * hcσ σ Bm * (hcσ σ Qm * Qm) * Bm * Pm := by simp only [Matrix.mul_assoc]
    _ = hcσ σ Pm * (hcσ σ Bm * J * Bm) * Pm := by rw [hJ]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hB, hP]



@[expose] def antidiag3 (L : Type) [Field L] : M3 L := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

@[expose] def changeMatrix (a : L) : M3 L := !![1, 0, a; 0, 1, 0; 2⁻¹, 0, -(a * 2⁻¹)]

theorem changeMatrix_unitary (σ : L →+* L) (a : L) (h2 : (2 : L) ≠ 0)
    (ha : σ a * a = -1) :
    hcσ σ (changeMatrix a) * antidiag3 L * changeMatrix a = 1 := by
  have hσ2 : σ (2⁻¹ : L) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hcσ, changeMatrix, antidiag3, Matrix.mul_apply, Fin.sum_univ_three, hσ2] <;>
    first
    | (field_simp; ring1)
    | (field_simp; linear_combination (-1 : L) * ha)
    | (field_simp; linear_combination (-2 : L) * ha)


end Hermitian

section PSU

theorem statedScalars_map_conj {L : Type} [Field L] (P : GL (Fin 3) L) :
    (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) L).map (MulAut.conj P).toMonoidHom =
      CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) L := by
  have hcent : ∀ c : Lˣ, P * GeneralLinearGroup.scalar (Fin 3) c * P⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) c := by
    intro c
    have hc : GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) L) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    rw [Subgroup.mem_center_iff.mp hc P, mul_inv_cancel_right]
  ext B
  simp only [Subgroup.mem_map, CFSG.Assembly.LowTwoRank.StatedScalars, MonoidHom.mem_range,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (hcent c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, hcent c⟩

theorem nonempty_mulEquiv_psu3 (G : Type) [Group G] (p f : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f) :
    Nonempty (G ≃* CFSG.Open.PSU3 p f) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf : f ≠ 0 := by
    have := hadm.2.1
    omega
  let L := GaloisField p (2 * f)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 3) φ) (glCongr_statedSU φ 3 (p ^ f))
    (glCongr_statedScalars φ)
  let σ : L →+* L := iterateFrobenius L p f
  have hσ : ∀ x : L, σ x = x ^ (p ^ f) := fun x => iterateFrobenius_def p f x
  obtain ⟨a, ha⟩ := exists_pow_succ_eq_neg_one p f hp2 hf
  have haσ : σ a * a = -1 := by rw [hσ, ← pow_succ, ha]
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hchar : ringChar L = p := ringChar.eq L p
    have h2' : ((2 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [ringChar.spec, hchar] at h2'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h2')
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at ha
    exact one_ne_zero (neg_eq_zero.mp ha.symm)
  have hdet : (changeMatrix a).det ≠ 0 := by
    have hd : (changeMatrix a).det = -a := by
      simp [Matrix.det_fin_three, changeMatrix]
      field_simp
      norm_num
    rw [hd]
    exact neg_ne_zero.mpr ha0
  let P : GL (Fin 3) L := GeneralLinearGroup.mkOfDetNeZero (changeMatrix a) hdet
  have hP : hcσ σ (P : M3 L) * antidiag3 L * (P : M3 L) = 1 :=
    changeMatrix_unitary σ a h2 haσ
  let SJ : Set (GL (Fin 3) L) := {A |
    (Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) L) j i ^ (p ^ f)) *
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] * (A : Matrix (Fin 3) (Fin 3) L) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    GeneralLinearGroup.det A = 1}
  have hof : ∀ A : GL (Fin 3) L,
      (Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) L) j i ^ (p ^ f)) = hcσ σ (A : M3 L) := by
    intro A
    ext i j
    simp [hcσ, hσ]
  have hSU : ∀ A : GL (Fin 3) L,
      ((A : M3 L).map (· ^ (p ^ f)))ᵀ * (A : M3 L) = hcσ σ (A : M3 L) * (A : M3 L) := by
    intro A
    congr 1
  have hdetconj : ∀ X Y : GL (Fin 3) L,
      GeneralLinearGroup.det (X * Y * X⁻¹) = GeneralLinearGroup.det Y := by
    intro X Y
    simp only [map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  have hdet1 : ∀ A : GL (Fin 3) L,
      (A : M3 L).det = 1 ↔ GeneralLinearGroup.det A = 1 := by
    intro A
    rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hmap : (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) L).map (MulAut.conj P).toMonoidHom =
      Subgroup.closure SJ := by
    unfold CFSG.Assembly.LowTwoRank.StatedSU
    rw [MonoidHom.map_closure]
    congr 1
    ext B
    simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SJ]
    constructor
    · rintro ⟨A, ⟨hdetA, hUA⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hof]
        exact conj_unitary σ (antidiag3 L) P A hP (by rw [← hSU]; exact hUA)
      · rw [hdetconj]
        exact (hdet1 A).mp hdetA
    · rintro ⟨hUB, hdetB⟩
      refine ⟨P⁻¹ * B * P, ⟨?_, ?_⟩, by group⟩
      · rw [hdet1]
        have := hdetconj P⁻¹ B
        rw [inv_inv] at this
        rw [this, hdetB]
      · rw [hSU]
        exact conj_unitary_inv σ (antidiag3 L) P B hP (by rw [← hof]; exact hUB)
  let e2 := statedProjCongr (MulAut.conj P) hmap (statedScalars_map_conj P)
  let e3 := statedProjEquivMapMk (Subgroup.closure SJ)
  exact ⟨e.trans (e1.trans (e2.trans e3))⟩

end PSU

section M11

@[expose] def m11StdA : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

@[expose] def m11StdB : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]

@[expose] def m11CatC : Equiv.Perm (Fin 11) := List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

@[expose] def m11CatD : Equiv.Perm (Fin 11) :=
  List.formPerm [2, 6, 10, 7] * List.formPerm [3, 9, 4, 5]

@[expose] def m11Conj : Equiv.Perm (Fin 11) := List.formPerm [1, 6, 10, 4, 2, 8, 9, 7, 5]

theorem m11Conj_stdA : m11Conj * m11StdA * m11Conj⁻¹ = m11CatD * m11CatD := by decide +kernel

theorem m11Conj_stdB :
    m11Conj * m11StdB * m11Conj⁻¹ = m11CatC * m11CatC * m11CatD⁻¹ * m11CatC * m11CatD := by
  decide +kernel

theorem m11Conj_catC : m11Conj⁻¹ * m11CatC * m11Conj =
    m11StdA * m11StdB * m11StdA * m11StdB⁻¹ * m11StdA * m11StdB⁻¹ * m11StdA * m11StdB⁻¹ *
      m11StdA * m11StdB * m11StdB * m11StdA * m11StdB⁻¹ * m11StdA * m11StdB * m11StdA := by
  decide +kernel

theorem m11Conj_catD : m11Conj⁻¹ * m11CatD * m11Conj =
    m11StdB⁻¹ * m11StdA * m11StdB * m11StdA * m11StdB * m11StdA * m11StdB⁻¹ * m11StdA *
      m11StdB * m11StdB * m11StdA * m11StdB := by
  decide +kernel

theorem nativeM11_eq_closure :
    CFSG.Blueprint.NativeSporadic.M11 = Subgroup.closure {m11StdA, m11StdB} := rfl

theorem catalogueM11_eq_closure : CFSG.Open.M11 = Subgroup.closure {m11CatC, m11CatD} := rfl

theorem nativeM11_map_conj :
    CFSG.Blueprint.NativeSporadic.M11.map (MulAut.conj m11Conj).toMonoidHom = CFSG.Open.M11 := by
  rw [nativeM11_eq_closure, catalogueM11_eq_closure]
  set H := Subgroup.closure ({m11CatC, m11CatD} : Set (Equiv.Perm (Fin 11)))
  set K := Subgroup.closure ({m11StdA, m11StdB} : Set (Equiv.Perm (Fin 11)))
  have hc : m11CatC ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hd : m11CatD ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have ha : m11StdA ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m11StdB ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · change m11Conj * m11StdA * m11Conj⁻¹ ∈ H
      rw [m11Conj_stdA]
      exact H.mul_mem hd hd
    · change m11Conj * m11StdB * m11Conj⁻¹ ∈ H
      rw [m11Conj_stdB]
      exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hc hc) (H.inv_mem hd)) hc) hd
  · rw [Subgroup.closure_le]
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · refine ⟨m11Conj⁻¹ * m11CatC * m11Conj, ?_, ?_⟩
      · rw [m11Conj_catC]
        exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
          (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem ha
          hb) ha) (K.inv_mem hb)) ha) (K.inv_mem hb)) ha) (K.inv_mem hb)) ha) hb) hb) ha)
          (K.inv_mem hb)) ha) hb) ha)
      · change m11Conj * (m11Conj⁻¹ * m11CatC * m11Conj) * m11Conj⁻¹ = m11CatC
        group
    · refine ⟨m11Conj⁻¹ * m11CatD * m11Conj, ?_, ?_⟩
      · rw [m11Conj_catD]
        exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
          (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hb) ha) hb) ha) hb) ha)
          (K.inv_mem hb)) ha) hb) hb) ha) hb)
      · change m11Conj * (m11Conj⁻¹ * m11CatD * m11Conj) * m11Conj⁻¹ = m11CatD
        group

noncomputable def statedM11EquivM11 : CFSG.Open.StatedM11 ≃* CFSG.Open.M11 :=
  (MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11).trans
    ((CFSG.Blueprint.NativeSporadic.M11.equivMapOfInjective
        (MulAut.conj m11Conj).toMonoidHom (MulAut.conj m11Conj).injective).trans
      (MulEquiv.subgroupCongr nativeM11_map_conj))

end M11

section Catalogue

theorem semidihedral_catalogue_of_stated (G : Type) [Group G]
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
          CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
          CFSG.Open.StatedClassicalModel G .PSU 3 p f) ∨
      Nonempty (G ≃* CFSG.Open.StatedM11)) :
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* CFSG.Open.PSU3 p k)) ∨
    Nonempty (G ≃* CFSG.Open.M11) := by
  rcases h with ⟨p, f, hp, -, hf, hq, hm⟩ | ⟨p, f, hp, hp2, hf, hq, hm⟩ | ⟨⟨e⟩⟩
  · let _ : Fact p.Prime := ⟨hp⟩
    exact Or.inl ⟨p, f, ⟨hp⟩, hf, hq, nonempty_mulEquiv_psl_galoisField G 3 p f hm⟩
  · let _ : Fact p.Prime := ⟨hp⟩
    exact Or.inr (Or.inl ⟨p, f, ⟨hp⟩, hf, hq, nonempty_mulEquiv_psu3 G p f hp2 hm⟩)
  · exact Or.inr (Or.inr ⟨e.trans statedM11EquivM11⟩)

theorem wreathed_catalogue_of_stated (G : Type) [Group G]
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
          CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
          CFSG.Open.StatedClassicalModel G .PSU 3 p f)) :
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* CFSG.Open.PSU3 p k)) := by
  rcases h with ⟨p, f, hp, -, hf, hq, hm⟩ | ⟨p, f, hp, hp2, hf, hq, hm⟩
  · let _ : Fact p.Prime := ⟨hp⟩
    exact Or.inl ⟨p, f, ⟨hp⟩, hf, hq, nonempty_mulEquiv_psl_galoisField G 3 p f hm⟩
  · let _ : Fact p.Prime := ⟨hp⟩
    exact Or.inr ⟨p, f, ⟨hp⟩, hf, hq, nonempty_mulEquiv_psu3 G p f hp2 hm⟩

end Catalogue

end CFSG.Adapters.RankTwoModelTransports
