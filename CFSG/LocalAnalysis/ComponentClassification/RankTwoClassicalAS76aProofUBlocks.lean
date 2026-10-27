module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviAut
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Blocks

variable {K : Type} [Field K] {k : ℕ}

@[expose] noncomputable def blkGL : GL (Fin 2) K × GL (Fin k) K →* GL (Fin (2 + k)) K where
  toFun x := ⟨blk (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin k) (Fin k) K),
    blk ((x.1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ((x.2⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K),
    by rw [blk_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, mul_inv_cancel,
      Units.val_one, Units.val_one, blk_one],
    by rw [blk_mul, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, inv_mul_cancel,
      Units.val_one, Units.val_one, blk_one]⟩
  map_one' := Units.ext blk_one
  map_mul' x y := Units.ext (by
    change blk ((x.1 * y.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ((x.2 * y.2 : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = blk _ _ * blk _ _
    rw [Units.val_mul, Units.val_mul, blk_mul])

theorem coe_blkGL (x : GL (Fin 2) K × GL (Fin k) K) :
    ((blkGL x : GL (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin k) (Fin k) K) :=
  rfl

theorem blk_map_fun (g : K → K) (hg : g 0 = 0) (X : Matrix (Fin 2) (Fin 2) K)
    (S : Matrix (Fin k) (Fin k) K) : (blk X S).map g = blk (X.map g) (S.map g) := by
  simp only [blk, coe_reindexAlgEquiv, reindex_apply, ← submatrix_map, fromBlocks_map,
    Matrix.map_zero _ hg]

theorem blk_mem_genSU {q : ℕ} (hq : q ≠ 0) {X : Matrix (Fin 2) (Fin 2) K}
    {S : Matrix (Fin k) (Fin k) K} (hX : X.det = 1 ∧ (X.map (· ^ q))ᵀ * X = 1)
    (hS : S.det = 1 ∧ (S.map (· ^ q))ᵀ * S = 1) :
    (blk X S).det = 1 ∧ ((blk X S).map (· ^ q))ᵀ * blk X S = 1 := by
  refine ⟨by rw [det_blk, hX.1, hS.1, one_mul], ?_⟩
  rw [blk_map_fun _ (zero_pow hq), transpose_blk, blk_mul, hX.2, hS.2, blk_one]

theorem one_mem_genSU {n q : ℕ} (hq : q ≠ 0) :
    (1 : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((1 : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * 1 = 1 := by
  refine ⟨det_one, ?_⟩
  rw [Matrix.map_one _ (by simp [hq]) (by simp), transpose_one, Matrix.mul_one]

theorem statedSU_le_comap_inl {q : ℕ} (hq : q ≠ 0) :
    StatedSU 2 q K ≤ (StatedSU (2 + k) q K).comap (blkGL.comp (MonoidHom.inl _ _)) := by
  unfold StatedSU
  rw [Subgroup.closure_le]
  intro X hX
  exact Subgroup.subset_closure (blk_mem_genSU hq hX (one_mem_genSU hq))

theorem statedSU_le_comap_inr {q : ℕ} (hq : q ≠ 0) :
    StatedSU k q K ≤ (StatedSU (2 + k) q K).comap (blkGL.comp (MonoidHom.inr _ _)) := by
  unfold StatedSU
  rw [Subgroup.closure_le]
  intro S hS
  exact Subgroup.subset_closure (blk_mem_genSU hq (one_mem_genSU hq) hS)

variable (K k) in
@[expose] noncomputable def uW (f : ℕ) : StatedSU 2 (2 ^ f) K →* StatedSU (2 + k) (2 ^ f) K :=
  ((blkGL.comp (MonoidHom.inl _ _)).comp (StatedSU 2 (2 ^ f) K).subtype).codRestrict _ fun X =>
    statedSU_le_comap_inl (pow_ne_zero f two_ne_zero) X.2

variable (K k) in
@[expose] noncomputable def uL (f : ℕ) : StatedSU k (2 ^ f) K →* StatedSU (2 + k) (2 ^ f) K :=
  ((blkGL.comp (MonoidHom.inr _ _)).comp (StatedSU k (2 ^ f) K).subtype).codRestrict _ fun S =>
    statedSU_le_comap_inr (pow_ne_zero f two_ne_zero) S.2

variable {f : ℕ}

theorem coe_uW (X : StatedSU 2 (2 ^ f) K) :
    (((uW K k f X : StatedSU (2 + k) (2 ^ f) K) : GL (Fin (2 + k)) K) :
      Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 :=
  rfl

theorem coe_uL (S : StatedSU k (2 ^ f) K) :
    (((uL K k f S : StatedSU (2 + k) (2 ^ f) K) : GL (Fin (2 + k)) K) :
      Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk 1 ((S : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) :=
  rfl

theorem uW_commute_uL (X : StatedSU 2 (2 ^ f) K) (S : StatedSU k (2 ^ f) K) :
    uW K k f X * uL K k f S = uL K k f S * uW K k f X := by
  apply Subtype.ext
  apply Units.ext
  change blk ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 *
      blk 1 ((S : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
    blk 1 ((S : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *
      blk ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1
  rw [blk_mul, blk_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

end Blocks

section Converse

variable {K : Type} [Field K] {k f : ℕ} (h : UnitaryFieldData 2 f K)
include h

theorem blk_unitary_of_mem {g : GL (Fin (2 + k)) K} {X : Matrix (Fin 2) (Fin 2) K}
    {S : Matrix (Fin k) (Fin k) K} (hg : g.val = blk X S)
    (hmem : g ∈ StatedSU (2 + k) (2 ^ f) K) :
    X.det * S.det = 1 ∧ (X.map h.bar)ᵀ * X = 1 ∧ (S.map h.bar)ᵀ * S = 1 := by
  obtain ⟨hdet, hu⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp hmem
  rw [hg] at hdet hu
  rw [det_blk] at hdet
  rw [blk_map_fun _ (map_zero h.bar), transpose_blk, blk_mul, ← blk_one] at hu
  exact ⟨hdet, blk_injective hu⟩

theorem mem_range_uW_of {g : StatedSU (2 + k) (2 ^ f) K} {X : Matrix (Fin 2) (Fin 2) K}
    (hg : ((g : GL (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk X 1) :
    g ∈ (uW K k f).range := by
  obtain ⟨hdet, hX, -⟩ := blk_unitary_of_mem h hg g.2
  rw [det_one, mul_one] at hdet
  set X' : GL (Fin 2) K := GeneralLinearGroup.mkOfDetNeZero X (by rw [hdet]; exact one_ne_zero)
  have hX' : X' ∈ StatedSU 2 (2 ^ f) K :=
    (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mpr ⟨hdet, hX⟩
  exact ⟨⟨X', hX'⟩, Subtype.ext (Units.ext hg.symm)⟩

theorem mem_range_uL_of {g : StatedSU (2 + k) (2 ^ f) K} {S : Matrix (Fin k) (Fin k) K}
    (hg : ((g : GL (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk 1 S) :
    g ∈ (uL K k f).range := by
  obtain ⟨hdet, -, hS⟩ := blk_unitary_of_mem h hg g.2
  rw [det_one, one_mul] at hdet
  set S' : GL (Fin k) K := GeneralLinearGroup.mkOfDetNeZero S (by rw [hdet]; exact one_ne_zero)
  have hS' : S' ∈ StatedSU k (2 ^ f) K :=
    (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mpr ⟨hdet, hS⟩
  exact ⟨⟨S', hS'⟩, Subtype.ext (Units.ext hg.symm)⟩

end Converse

section Proj

variable {K : Type} [Field K] {f : ℕ}

variable (K) in
@[expose] noncomputable def uProj (n f : ℕ) :
    StatedSU n (2 ^ f) K →* StatedProj (StatedSU n (2 ^ f) K) :=
  QuotientGroup.mk' _

theorem uProj_surjective (n : ℕ) : Function.Surjective (uProj K n f) :=
  QuotientGroup.mk'_surjective _

theorem uProj_eq_uProj_iff {n : ℕ} {g g' : StatedSU n (2 ^ f) K} :
    uProj K n f g = uProj K n f g' ↔
      ∃ c : Kˣ, (g' : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c * g := by
  rw [uProj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf,
    StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have e : (g' : GL (Fin n) K) = g * GeneralLinearGroup.scalar (Fin n) c := by
      rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (g : GL (Fin n) K)).eq]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hc,
      ← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (g : GL (Fin n) K)).eq, ← mul_assoc,
      inv_mul_cancel, one_mul]

theorem eq_of_uProj_eq_of_mul_self [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    {g g' : StatedSU n (2 ^ f) K} (hgg : uProj K n f g = uProj K n f g') (hg : g * g = 1)
    (hg' : g' * g' = 1) : g = g' := by
  obtain ⟨c, hc⟩ := uProj_eq_uProj_iff.mp hgg
  have h1 : GeneralLinearGroup.scalar (Fin n) (c * c) = 1 := by
    have e1 : (g' : GL (Fin n) K) * g' = 1 := by rw [← Subgroup.coe_mul, hg', Subgroup.coe_one]
    have e2 : (g : GL (Fin n) K) * g = 1 := by rw [← Subgroup.coe_mul, hg, Subgroup.coe_one]
    have hcomm := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (g : GL (Fin n) K)).eq
    set sc := GeneralLinearGroup.scalar (Fin n) c
    calc GeneralLinearGroup.scalar (Fin n) (c * c) = sc * (sc * ((g : GL (Fin n) K) * g)) := by
          rw [e2, mul_one, map_mul]
      _ = sc * ((g : GL (Fin n) K) * (sc * g)) := by
          rw [← mul_assoc (g : GL (Fin n) K) sc, hcomm, mul_assoc]
      _ = (sc * g) * (sc * g) := by simp only [mul_assoc]
      _ = 1 := by rw [← hc, e1]
  have h2 : (c : K) * c = 1 := by
    have := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h1
    simpa [GeneralLinearGroup.coe_scalar] using this
  have hc1 : (c : K) = 1 := eq_of_mul_self_eq (h2.trans (mul_one 1).symm)
  have hc1' : c = 1 := Units.ext hc1
  apply Subtype.ext
  rw [hc, hc1', map_one, one_mul]

end Proj

section Bar

variable {K : Type} [Field K] {k f : ℕ}

variable (K k f) in
@[expose] noncomputable def uBarW : Subgroup (StatedProj (StatedSU (2 + k) (2 ^ f) K)) :=
  ((uProj K (2 + k) f).comp (uW K k f)).range

variable (K k f) in
@[expose] noncomputable def uBarL : Subgroup (StatedProj (StatedSU (2 + k) (2 ^ f) K)) :=
  ((uProj K (2 + k) f).comp (uL K k f)).range

theorem uBarW_commute_uBarL {x y : StatedProj (StatedSU (2 + k) (2 ^ f) K)}
    (hx : x ∈ uBarW K k f) (hy : y ∈ uBarL K k f) : x * y = y * x := by
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := hy
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, uW_commute_uL]

theorem uProj_uW_injective (hk : 1 ≤ k) :
    Function.Injective ((uProj K (2 + k) f).comp (uW K k f)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro X hX
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, uProj, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hX
  obtain ⟨c, hc⟩ := hX
  have hm := congrArg Units.val hc
  rw [GeneralLinearGroup.coe_scalar, coe_uW, scalar_eq_blk] at hm
  have h1 := blk_injective hm
  have hc1 : (c : K) = 1 := by
    have := congrFun (congrFun h1.2 ⟨0, hk⟩) ⟨0, hk⟩
    simpa using this
  rw [hc1, one_smul] at h1
  exact mem_bot.mpr (Subtype.ext (Units.ext h1.1.symm))

theorem uProj_uL_injective : Function.Injective ((uProj K (2 + k) f).comp (uL K k f)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro S hS
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, uProj, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hS
  obtain ⟨c, hc⟩ := hS
  have hm := congrArg Units.val hc
  rw [GeneralLinearGroup.coe_scalar, coe_uL, scalar_eq_blk] at hm
  have h1 := blk_injective hm
  have hc1 : (c : K) = 1 := by
    have := congrFun (congrFun h1.1 0) 0
    simpa using this
  simp only [hc1, one_smul] at h1
  exact mem_bot.mpr (Subtype.ext (Units.ext h1.2.symm))

variable (K k f) in
@[expose] noncomputable def uBarWEquiv (hk : 1 ≤ k) : StatedSU 2 (2 ^ f) K ≃* uBarW K k f :=
  MonoidHom.ofInjective (uProj_uW_injective hk)

variable (K k f) in
@[expose] noncomputable def uBarLEquiv : StatedSU k (2 ^ f) K ≃* uBarL K k f :=
  MonoidHom.ofInjective uProj_uL_injective

end Bar

end CFSG.ComponentClassification.RankTwoClassical
