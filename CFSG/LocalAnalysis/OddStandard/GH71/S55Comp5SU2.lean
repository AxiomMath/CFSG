module

public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.OddStandard.GH71.S55.C5U

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem blockGL_mem_statedSU {m k i : ℕ} (hk : i + k ≤ m) {A : GL (Fin k) K}
    (hA : A ∈ StatedSU k (p ^ f) K) : blockGL m i hk A ∈ StatedSU m (p ^ f) K := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  rw [← SUid_eq_statedSU h.card_eq_sq] at hA ⊢
  exact blockGL_mem_SUid _ hk hA

@[expose] noncomputable def blkSU {m k : ℕ} (i : ℕ) (hk : i + k ≤ m) :
    StatedSU k (p ^ f) K →* StatedSU m (p ^ f) K :=
  ((blockGL m i hk).comp (StatedSU k (p ^ f) K).subtype).codRestrict _
    fun A => blockGL_mem_statedSU h hk A.2

theorem coe_blkSU {m k i : ℕ} (hk : i + k ≤ m) (A : StatedSU k (p ^ f) K) :
    ((blkSU h i hk A : StatedSU m (p ^ f) K) : GL (Fin m) K) = blockGL m i hk (A : GL (Fin k) K) :=
  rfl

theorem blkSU_injective {m k i : ℕ} (hk : i + k ≤ m) : Function.Injective (blkSU h i hk) :=
  fun _ _ hAB => Subtype.ext (Units.ext (blockMat_injective hk
    (congrArg (fun g : StatedSU m (p ^ f) K => ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
      hAB)))

theorem eq_one_of_blockGL_mem_scalars {m k i : ℕ} (hk : i + k ≤ m) (hlt : k < m)
    {A : GL (Fin k) K} (hA : blockGL m i hk A ∈ StatedScalars (Fin m) K) : A = 1 := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hA
  obtain ⟨a, ha⟩ : ∃ a : Fin m, ¬ (i ≤ a.val ∧ a.val < i + k) := by
    by_cases hi : 0 < i
    · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
    · exact ⟨⟨m - 1, by omega⟩, by simp only; omega⟩
  have hcM : Matrix.scalar (Fin m) (c : K) = blockMat m i (A : Matrix (Fin k) (Fin k) K) :=
    congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) hc
  have hc1 : (c : K) = 1 := by
    have e := congrFun (congrFun hcM a) a
    rw [blockMat_apply_of_not_mem_left _ ha] at e
    simpa using e
  have hM : blockMat m i (A : Matrix (Fin k) (Fin k) K) =
      blockMat m i (1 : Matrix (Fin k) (Fin k) K) := by
    rw [blockMat_one, ← hcM, hc1, map_one]
  exact Units.ext (blockMat_injective hk hM)

theorem proj_blkSU_injective {m k i : ℕ} (hk : i + k ≤ m) (hlt : k < m) :
    Function.Injective ((projH (StatedSU m (p ^ f) K)).comp (blkSU h i hk)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [MonoidHom.comp_apply] at hA
  have hmem := (QuotientGroup.eq_one_iff _).mp hA
  rw [Subgroup.mem_subgroupOf] at hmem
  exact Subtype.ext (eq_one_of_blockGL_mem_scalars hk hlt hmem)

theorem statedGU_eq_uU (k : ℕ) : CFSG.Quasithin.StatedGU k (p ^ f) K = uU h k := by
  have hbar : (fun c : K => c ^ p ^ f) = ⇑h.bar := funext fun c => (h.bar_apply c).symm
  have hset : {A : GL (Fin k) K | ((A : Matrix (Fin k) (Fin k) K).map (· ^ p ^ f))ᵀ *
      (A : Matrix (Fin k) (Fin k) K) = 1} = (uU h k : Set (GL (Fin k) K)) := by
    ext A
    rw [SetLike.mem_coe, mem_uU, hbar]
    rfl
  rw [CFSG.Quasithin.StatedGU, hset, Subgroup.closure_eq]

@[expose] noncomputable def detInv1 (k : ℕ) : GL (Fin k) K →* GL (Fin 1) K :=
  (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (invMonoidHom.comp Matrix.GeneralLinearGroup.det)

theorem blockGL_commute {k l : ℕ} (X : GL (Fin k) K) (Y : GL (Fin l) K) :
    Commute (blockGL (k + l) 0 (by omega) X) (blockGL (k + l) k (by omega) Y) :=
  Units.ext (blockMat_comm (Or.inl (by omega)) _ _)

@[expose] noncomputable def blkGL (k : ℕ) : GL (Fin k) K →* GL (Fin (k + 1)) K where
  toFun B := blockGL (k + 1) 0 (by omega) B * blockGL (k + 1) k (by omega) (detInv1 k B)
  map_one' := by simp
  map_mul' B C := by
    rw [map_mul, map_mul, map_mul]
    have hc := (blockGL_commute (K := K) (l := 1) C (detInv1 k B)).eq
    simp only [mul_assoc]
    rw [← mul_assoc (blockGL (k + 1) 0 _ C), hc, mul_assoc]

theorem coe_blkGL {k : ℕ} (B : GL (Fin k) K) :
    blkGL k B = blockGL (k + 1) 0 (by omega) B * blockGL (k + 1) k (by omega) (detInv1 k B) :=
  rfl

include h in
theorem bar_det_mul_det {k : ℕ} {B : GL (Fin k) K} (hB : B ∈ uU h k) :
    h.bar (B : Matrix (Fin k) (Fin k) K).det * (B : Matrix (Fin k) (Fin k) K).det = 1 := by
  have e := congrArg Matrix.det ((mem_uU h).1 hB)
  rwa [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one] at e

include h in
theorem blockGL_mem_uU {m k i : ℕ} (hk : i + k ≤ m) {B : GL (Fin k) K} (hB : B ∈ uU h k) :
    blockGL m i hk B ∈ uU h m := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hσ : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) K),
      conjTr (unitaryInvolution K p f) M = (M.map h.bar)ᵀ := fun M => by
    unfold conjTr
    congr 1
  rw [mem_uU, CFSG.ClassicalInvolution.Phan.coe_blockGL, ← hσ, conjTr_blockMat, hσ,
    ← blockMat_mul hk, (mem_uU h).1 hB, blockMat_one]

include h in
theorem detInv1_mem_uU {k : ℕ} {B : GL (Fin k) K} (hB : B ∈ uU h k) : detInv1 k B ∈ uU h 1 := by
  have hb := bar_det_mul_det h hB
  rw [mem_uU]
  ext a b
  fin_cases a; fin_cases b
  simp [detInv1, Matrix.GeneralLinearGroup.coe_scalar, map_inv₀, ← mul_inv, hb]

include h in
theorem blkGL_mem_statedSU {k : ℕ} {B : GL (Fin k) K} (hB : B ∈ uU h k) :
    blkGL k B ∈ StatedSU (k + 1) (p ^ f) K := by
  refine (mem_unitarySU_iff h).2 ⟨?_, (mem_uU h).1 ((uU h (k + 1)).mul_mem
    (blockGL_mem_uU h _ hB) (blockGL_mem_uU h _ (detInv1_mem_uU h hB)))⟩
  have hd : (B : Matrix (Fin k) (Fin k) K).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit |>.ne_zero
  rw [coe_blkGL, Units.val_mul, CFSG.ClassicalInvolution.Phan.coe_blockGL,
    CFSG.ClassicalInvolution.Phan.coe_blockGL, det_mul,
    det_blockMat (by omega : 0 + k ≤ k + 1), det_blockMat (by omega : k + 1 ≤ k + 1)]
  simp [detInv1, Matrix.GeneralLinearGroup.coe_scalar, hd]

@[expose] noncomputable def blkGU (k : ℕ) : uU h k →* StatedSU (k + 1) (p ^ f) K :=
  ((blkGL k).comp (uU h k).subtype).codRestrict _ fun B => blkGL_mem_statedSU h B.2

theorem eq_one_of_blockMat_eq {m k l j : ℕ} (hk : 0 + k ≤ m) (hj : k ≤ j)
    {X : Matrix (Fin k) (Fin k) K} {Y : Matrix (Fin l) (Fin l) K}
    (e : blockMat m 0 X = blockMat m j Y) : X = 1 := by
  ext x y
  have e1 := congrFun (congrFun e (blockIdx 0 hk x)) (blockIdx 0 hk y)
  rw [blockMat_apply_blockIdx,
    blockMat_apply_of_not_mem_left _ (by simp only [blockIdx_val]; omega)] at e1
  rw [e1, one_apply, one_apply]
  simp [Fin.ext_iff]

theorem blkGU_injective (k : ℕ) : Function.Injective (blkGU h k) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have e : blkGL k (B : GL (Fin k) K) = 1 := congrArg Subtype.val hB
  rw [coe_blkGL, mul_eq_one_iff_eq_inv, ← map_inv] at e
  exact Subtype.ext (Units.ext (eq_one_of_blockMat_eq (by omega) le_rfl
    (congrArg (fun g : GL (Fin (k + 1)) K => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) K)) e)))

theorem conj_blockGL_mul {k l : ℕ} (X C : GL (Fin k) K) (Y : GL (Fin l) K) :
    blockGL (k + l) 0 (by omega) X * blockGL (k + l) k (by omega) Y *
        blockGL (k + l) 0 (by omega) C *
        (blockGL (k + l) 0 (by omega) X * blockGL (k + l) k (by omega) Y)⁻¹ =
      blockGL (k + l) 0 (by omega) (X * C * X⁻¹) := by
  have hc := (blockGL_commute C Y).eq
  rw [map_mul, map_mul, map_inv]
  calc _ = blockGL (k + l) 0 (by omega) X * (blockGL (k + l) k (by omega) Y *
        blockGL (k + l) 0 (by omega) C) * (blockGL (k + l) k (by omega) Y)⁻¹ *
        (blockGL (k + l) 0 (by omega) X)⁻¹ := by group
    _ = _ := by rw [← hc]; group

theorem range_blkGU_le_normalizer (k : ℕ) :
    (blkGU h k).range ≤ normalizer ((blkSU h 0 (by omega : 0 + k ≤ k + 1)).range :
      Set (StatedSU (k + 1) (p ^ f) K)) := by
  have key : ∀ (B : uU h k) (C : StatedSU k (p ^ f) K),
      blkGU h k B * blkSU h 0 (by omega) C * (blkGU h k B)⁻¹ =
        blkSU h 0 (by omega) ⟨_, uConjSU_mem h B C⟩ := fun B C =>
    Subtype.ext (conj_blockGL_mul (l := 1) (B : GL (Fin k) K) (C : GL (Fin k) K) _)
  rintro _ ⟨B, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨_, (key B C).symm⟩
  · rintro ⟨C, hC⟩
    have e : x = blkGU h k B⁻¹ * blkSU h 0 (by omega) C * (blkGU h k B⁻¹)⁻¹ := by
      rw [hC, map_inv, inv_inv]
      group
    rw [e, key]
    exact ⟨_, rfl⟩

end CFSG.OddStandard.GH71.S55.C5U
