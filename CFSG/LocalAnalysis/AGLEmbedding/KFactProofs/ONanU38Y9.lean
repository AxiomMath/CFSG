module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Scalar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Weak

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

@[expose] def zeta : GF64 := GF64.ofNat' 22

theorem zeta_pow_nine : zeta ^ 9 = 1 := by decide +kernel

theorem zeta_pow_three_cube : (zeta ^ 3) ^ 3 = 1 := by decide +kernel

theorem zeta_ne_zero : zeta ≠ 0 := by decide +kernel

theorem orderOf_zeta : orderOf zeta = 9 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨zeta_pow_nine, fun m hm hm0 => ?_⟩
  revert m
  decide +kernel

theorem det_cases : ∀ d : GF64, d ^ 3 = 1 → ∃ k < 3, d = zeta ^ (3 * k) := by
  decide +kernel

theorem smul_one_eq_scalar (c : GF64) : (c • 1 : Matrix (Fin 3) (Fin 3) GF64) =
    Matrix.scalar (Fin 3) c := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

@[expose] noncomputable def omegaSU : SU := scalarSU (zeta ^ 3) zeta_pow_three_cube

theorem coe_omegaSU_pow (m : ℕ) :
    (((omegaSU ^ m : SU) : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) =
      (zeta ^ (3 * m)) • 1 := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have : ((omegaSU : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) = (zeta ^ 3) • 1 :=
    coe_scalarGL (zeta ^ 3) zeta_pow_three_cube
  rw [this, smul_one_eq_scalar, ← map_pow, ← pow_mul, smul_one_eq_scalar]

theorem pow_cancel {a b : ℕ} (hab : b ≤ a) {d : GF64} (h : d ^ a = d ^ b) (hd : d ≠ 0) :
    d ^ (a - b) = 1 := by
  have h2 : d ^ (a - b) * d ^ b = 1 * d ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hab, h, one_mul]
  exact mul_right_cancel₀ (pow_ne_zero b hd) h2

structure Model9 (X : Type*) [Group X] where
  ι : SU →* X
  z : X
  ι_inj : Function.Injective ι
  z_comm : ∀ g : SU, z * ι g = ι g * z
  z_nine : z ^ 9 = 1
  z_cube : z ^ 3 = ι omegaSU
  z_mem : ∀ k : ℕ, z ^ k ∈ ι.range → 3 ∣ k

namespace Model9

variable {X : Type*} [Group X] (M : Model9 X)

theorem z_pow_comm (k : ℕ) (g : SU) : M.z ^ k * M.ι g = M.ι g * M.z ^ k :=
  (Commute.pow_left (M.z_comm g) k).eq

theorem ind {a b : ℕ} (hab : b ≤ a) {g h : SU}
    (hm : zeta ^ a • ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) =
      zeta ^ b • ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64)) :
    M.ι g * M.z ^ a = M.ι h * M.z ^ b := by
  have hdet := congrArg Matrix.det hm
  rw [Matrix.det_smul, Matrix.det_smul, ((mem_SU_iff'.1 g.2).1), ((mem_SU_iff'.1 h.2).1)] at hdet
  simp only [Fintype.card_fin, mul_one] at hdet
  have h1 : zeta ^ (3 * a) = zeta ^ (3 * b) := by
    rw [mul_comm 3 a, mul_comm 3 b, pow_mul, pow_mul]
    exact hdet
  have h2 := pow_cancel (by omega : 3 * b ≤ 3 * a) h1 zeta_ne_zero
  have h3 : 9 ∣ 3 * a - 3 * b := orderOf_zeta ▸ orderOf_dvd_of_pow_eq_one h2
  obtain ⟨m, hm3⟩ : ∃ m, a = b + 3 * m := ⟨(a - b) / 3, by omega⟩
  subst hm3
  have hcancel : (omegaSU ^ m * g : SU) = h := by
    have h5 : zeta ^ b • (zeta ^ (3 * m) • ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64))
        = zeta ^ b • ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) := by
      rw [smul_smul, ← pow_add]
      exact hm
    have h6 := smul_right_injective _ (pow_ne_zero b zeta_ne_zero) h5
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_omegaSU_pow, smul_mul_assoc, one_mul]
    exact h6
  have hz : M.z ^ (3 * m) = M.ι (omegaSU ^ m) := by
    rw [pow_mul, M.z_cube, map_pow]
  rw [← hcancel, map_mul, ← hz, M.z_pow_comm, mul_assoc, ← pow_add, add_comm]

end Model9

@[expose] def isUnitaryArr (A : Array GF64) : Bool :=
  A.size == 9 && mulArr3 (conjTrArr3 A) A == oneArr3

@[expose] def valid9 (p : Pr3) : Bool :=
  p.2 == 0 && isUnitaryArr p.1 && decide (detArr3 p.1 ^ 3 = 1)

theorem zeta_inv_bar (k : ℕ) : barC (zeta ^ k)⁻¹ * (zeta ^ k)⁻¹ = 1 := by
  rw [map_inv₀, barC_eq_pow, ← mul_inv, ← pow_mul, ← pow_add, show k * 8 + k = 9 * k by ring,
    pow_mul, zeta_pow_nine, one_pow, inv_one]

theorem exists_decomp9 {p : Pr3} (h : valid9 p = true) :
    p.1.size = 9 ∧ p.2 = 0 ∧ ∃ (g : SU) (k : ℕ),
      toMat3 p.1 = zeta ^ k • ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) := by
  simp only [valid9, isUnitaryArr, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hj, hsz, hmul⟩, hdet⟩ := h
  refine ⟨hsz, hj, ?_⟩
  obtain ⟨k, -, hk⟩ := det_cases _ hdet
  have hU' : ((toMat3 p.1).map barC)ᵀ * toMat3 p.1 = 1 := by
    have := congrArg toMat3 hmul
    rwa [toMat3_mulArr3, toMat3_conjTrArr3, toMat3_oneArr3] at this
  set c := (zeta ^ k)⁻¹ with hc
  have hck : zeta ^ k ≠ 0 := pow_ne_zero k zeta_ne_zero
  have hB : isSUArr (smulArr3 c p.1) = true := by
    simp only [isSUArr, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨by rw [size_smulArr3, hsz], ?_⟩, ?_⟩
    · rw [← det_toMat3, toMat3_smulArr3, Matrix.det_smul, det_toMat3]
      simp only [Fintype.card_fin]
      rw [hk, hc, inv_pow, ← pow_mul, mul_comm k 3, inv_mul_cancel₀ (pow_ne_zero _ zeta_ne_zero)]
    · apply eq_of_toMat_eq3 (size_mulArr3 _ _) size_oneArr3
      rw [toMat3_mulArr3, toMat3_conjTrArr3, toMat3_smulArr3, toMat3_oneArr3]
      have : ((c • toMat3 p.1).map barC)ᵀ = barC c • ((toMat3 p.1).map barC)ᵀ := by
        refine Matrix.ext fun i j => ?_
        simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply]
      rw [this, smul_mul_smul_comm, hU', zeta_inv_bar]
      simp
  obtain ⟨g, hg⟩ := exists_su_of_isSUArr hB
  refine ⟨g, k, ?_⟩
  rw [hg, toMat3_smulArr3, smul_smul, hc, mul_inv_cancel₀ hck, one_smul]

namespace Model9

variable {X : Type*} [Group X] (M : Model9 X)

@[expose] def Rep (p : Pr3) (y : X) : Prop :=
  p.1.size = 9 ∧ p.2 = 0 ∧ ∃ (g : SU) (k : ℕ),
    toMat3 p.1 = zeta ^ k • ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) ∧
      y = M.ι g * M.z ^ k

theorem rep_one : M.Rep oneP3 1 :=
  ⟨size_oneArr3, rfl, 1, 0, by simp [oneP3, toMat3_oneArr3], by simp⟩

theorem rep_mul {p q : Pr3} {y y' : X} (hp : M.Rep p y) (hq : M.Rep q y') :
    M.Rep (mulP3 p q) (y * y') := by
  obtain ⟨hps, hpj, g, k, hg, rfl⟩ := hp
  obtain ⟨hqs, hqj, h, l, hh, rfl⟩ := hq
  refine ⟨by simp [mulP3, size_mulArr3], by simp [mulP3, hpj, hqj], g * h, k + l, ?_, ?_⟩
  · simp only [mulP3, toMat3_mulArr3, hpj, sigPow, hg, hh, Subgroup.coe_mul, Units.val_mul]
    rw [smul_mul_smul_comm, ← pow_add]
  · rw [map_mul, mul_assoc, ← mul_assoc (M.z ^ k), M.z_pow_comm, mul_assoc, ← pow_add]
    group

theorem rep_inv {p : Pr3} {y : X} (hp : M.Rep p y) : M.Rep (invP3 p) y⁻¹ := by
  obtain ⟨hps, hpj, g, k, hg, rfl⟩ := hp
  have hinv : (((g⁻¹ : SU) : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) =
      (((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).map barC)ᵀ := by
    obtain ⟨-, hmul⟩ := mem_SU_iff'.1 g.2
    exact Units.inv_eq_of_mul_eq_one_left hmul
  have hinvp : invP3 p = (conjTrArr3 p.1, 0) := by
    simp [invP3, hpj, sigPow]
  rw [hinvp]
  refine ⟨size_conjTrArr3 _, rfl, g⁻¹, 8 * k, ?_, ?_⟩
  · rw [toMat3_conjTrArr3, hg, hinv]
    have : ((zeta ^ k • ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64)).map barC)ᵀ =
        barC (zeta ^ k) • (((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).map barC)ᵀ := by
      refine Matrix.ext fun i j => ?_
      simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply]
    rw [this, barC_eq_pow, ← pow_mul, mul_comm 8 k]
  · have hz : (M.z ^ k)⁻¹ = M.z ^ (8 * k) := by
      rw [inv_eq_of_mul_eq_one_right (b := M.z ^ (8 * k))]
      rw [← pow_add, show k + 8 * k = 9 * k by ring, pow_mul, M.z_nine, one_pow]
    rw [mul_inv_rev, hz, ← map_inv, ← M.z_pow_comm]

theorem rep_ext {p q : Pr3} {y y' : X} (hp : M.Rep p y) (hq : M.Rep q y')
    (h : eqMod [GF64.ofNat' 1] p q = true) : y = y' := by
  obtain ⟨hps, hpj, g, k, hg, rfl⟩ := hp
  obtain ⟨hqs, hqj, h', l, hh, rfl⟩ := hq
  simp only [eqMod, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.mem_singleton,
    exists_eq_left] at h
  obtain ⟨-, hpq⟩ := h
  have hmat : toMat3 p.1 = toMat3 q.1 := by
    rw [hpq, toMat3_smulArr3]
    have : GF64.ofNat' 1 = (1 : GF64) := rfl
    rw [this, one_smul]
  rw [hg, hh] at hmat
  rcases le_total l k with hlk | hkl
  · exact M.ind hlk hmat
  · exact (M.ind hkl hmat.symm).symm

theorem rep_inj {p : Pr3} (hp : M.Rep p 1) : eqMod [GF64.ofNat' 1] p oneP3 = true := by
  obtain ⟨hps, hpj, g, k, hg, h1⟩ := hp
  have hk : 3 ∣ k := by
    apply M.z_mem
    refine ⟨g⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right h1.symm).symm
  obtain ⟨m, rfl⟩ := hk
  have hz : M.z ^ (3 * m) = M.ι (omegaSU ^ m) := by
    rw [pow_mul, M.z_cube, map_pow]
  have hgm : g * omegaSU ^ m = 1 := by
    apply M.ι_inj
    rw [map_mul, ← hz, map_one]
    exact h1.symm
  have hmat : toMat3 p.1 = toMat3 oneArr3 := by
    have h2 := congrArg (fun a : SU => ((a : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64)) hgm
    simp only [Subgroup.coe_mul, Units.val_mul, coe_omegaSU_pow, Subgroup.coe_one,
      Units.val_one] at h2
    rw [hg, toMat3_oneArr3, ← h2, Matrix.mul_smul, Matrix.mul_one]
  have hp1 : p.1 = oneArr3 := eq_of_toMat_eq3 hps size_oneArr3 hmat
  simp only [eqMod, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.mem_singleton,
    exists_eq_left, oneP3]
  refine ⟨hpj, ?_⟩
  rw [hp1]
  apply (eq_of_toMat_eq3 size_oneArr3 (by rw [size_smulArr3]; exact size_oneArr3) _)
  rw [toMat3_smulArr3]
  have : GF64.ofNat' 1 = (1 : GF64) := rfl
  rw [this, one_smul]

theorem rep_exists {p : Pr3} (h : valid9 p = true) : ∃ y, M.Rep p y := by
  obtain ⟨hs, hj, g, k, hg⟩ := exists_decomp9 h
  exact ⟨M.ι g * M.z ^ k, hs, hj, g, k, hg, rfl⟩

end Model9

@[expose] noncomputable def Model9.repSys {X : Type*} [Group X] (M : Model9 X) : RepSys X where
  Rep := M.Rep
  sc := [GF64.ofNat' 1]
  valid := valid9
  rep_exists := fun {_} h => M.rep_exists h
  rep_one := M.rep_one
  rep_mul := fun {_ _ _ _} hp hq => M.rep_mul hp hq
  rep_inv := fun {_ _} hp => M.rep_inv hp
  rep_ext := fun {_ _ _ _} hp hq h => M.rep_ext hp hq h
  rep_inj := fun {_} hp => M.rep_inj hp

end CFSG.AGLEmbedding.ChevOuter.U38
