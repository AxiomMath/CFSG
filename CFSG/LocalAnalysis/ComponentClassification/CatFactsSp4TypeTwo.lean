module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Gauss

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open scoped commutatorElement

variable {K : Type} [Field K]

theorem conj_mem_spScalars_of_commute {T A : StatedSp 2 K}
    (h : proj 2 K A * proj 2 K T = proj 2 K T * proj 2 K A) :
    A * T * A⁻¹ * T⁻¹ ∈ spScalars 2 K := by
  rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

theorem mem_center_of_mem_spScalars {z : StatedSp 2 K} (hz : z ∈ spScalars 2 K) :
    z ∈ center (StatedSp 2 K) := by
  rw [mem_center_iff]
  intro g
  apply sp_ext
  rcases (mem_spScalars_iff z).mp hz with h | h <;>
    simp only [Subgroup.coe_mul, Units.val_mul, h, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul]

theorem twist_mem_center (T : StatedSp 2 K)
    (X : (centralizer {proj 2 K T}).comap (proj 2 K)) :
    (X : StatedSp 2 K) * T * (X : StatedSp 2 K)⁻¹ * T⁻¹ ∈ center (StatedSp 2 K) :=
  mem_center_of_mem_spScalars (conj_mem_spScalars_of_commute
    (mem_centralizer_singleton_iff.mp (mem_comap.mp X.2)))

@[expose] def twist (T : StatedSp 2 K) :
    (centralizer {proj 2 K T}).comap (proj 2 K) →* center (StatedSp 2 K) where
  toFun X := ⟨_, twist_mem_center T X⟩
  map_one' := Subtype.ext (by simp)
  map_mul' X Y := by
    apply Subtype.ext
    have h1 := mem_center_iff.mp (twist_mem_center T Y) (X : StatedSp 2 K)
    have h2 := mem_center_iff.mp (twist_mem_center T Y)
      ((X : StatedSp 2 K) * T * (X : StatedSp 2 K)⁻¹ * T⁻¹)
    change ((X : StatedSp 2 K) * Y) * T * ((X : StatedSp 2 K) * Y)⁻¹ * T⁻¹ =
      ((X : StatedSp 2 K) * T * (X : StatedSp 2 K)⁻¹ * T⁻¹) *
        ((Y : StatedSp 2 K) * T * (Y : StatedSp 2 K)⁻¹ * T⁻¹)
    calc ((X : StatedSp 2 K) * Y) * T * ((X : StatedSp 2 K) * Y)⁻¹ * T⁻¹ =
        ((X : StatedSp 2 K) * ((Y : StatedSp 2 K) * T * (Y : StatedSp 2 K)⁻¹ * T⁻¹)) *
          T * (X : StatedSp 2 K)⁻¹ * T⁻¹ := by group
      _ = (((Y : StatedSp 2 K) * T * (Y : StatedSp 2 K)⁻¹ * T⁻¹) * (X : StatedSp 2 K)) *
          T * (X : StatedSp 2 K)⁻¹ * T⁻¹ := by rw [h1]
      _ = ((Y : StatedSp 2 K) * T * (Y : StatedSp 2 K)⁻¹ * T⁻¹) *
          ((X : StatedSp 2 K) * T * (X : StatedSp 2 K)⁻¹ * T⁻¹) := by group
      _ = _ := h2.symm

theorem commutator_centralizer_proj_le (T : StatedSp 2 K) :
    ⁅centralizer {proj 2 K T}, centralizer {proj 2 K T}⁆ ≤ (centralizer {T}).map (proj 2 K) := by
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨A, rfl⟩ := proj_surjective x
  obtain ⟨B, rfl⟩ := proj_surjective y
  let A' : (centralizer {proj 2 K T}).comap (proj 2 K) := ⟨A, mem_comap.mpr hx⟩
  let B' : (centralizer {proj 2 K T}).comap (proj 2 K) := ⟨B, mem_comap.mpr hy⟩
  have h1 : twist T ⁅A', B'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (mem_center_iff.mp (twist T B').2 _)
  have h2 : ⁅A, B⁆ * T * ⁅A, B⁆⁻¹ * T⁻¹ = 1 := congrArg Subtype.val h1
  refine ⟨⁅A, B⁆, ?_, by rw [map_commutatorElement]⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  have h3 : ⁅A, B⁆ * T * ⁅A, B⁆⁻¹ = T := by
    rw [← mul_inv_eq_one]
    exact h2
  calc ⁅A, B⁆ * T = (⁅A, B⁆ * T * ⁅A, B⁆⁻¹) * ⁅A, B⁆ := by group
    _ = T * ⁅A, B⁆ := by rw [h3]

theorem perfect_le_map_centralizer (T : StatedSp 2 K) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hM : M ≤ centralizer {proj 2 K T}) (hperf : ⁅M, M⁆ = M) :
    M ≤ (centralizer {T}).map (proj 2 K) := by
  rw [← hperf]
  exact (commutator_mono hM hM).trans (commutator_centralizer_proj_le T)

theorem J₁_transpose_mul_self : (J₁ : Matrix (Fin 2) (Fin 2) K)ᵀ * J₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem kron_one_J₁_symplectic :
    (kron 1 (J₁ : Matrix (Fin 2) (Fin 2) K))ᵀ * formJ 2 K * kron 1 J₁ = formJ 2 K :=
  (kron_symplectic_iff _ _).mpr (by rw [det_one, one_smul, J₁_transpose_mul_self])

variable (K) in
@[expose] def T2 : StatedSp 2 K :=
  toSp (kron 1 J₁) kron_one_J₁_symplectic

theorem coe_T2 : (((T2 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron 1 J₁ := rfl

theorem kron_symplectic_of_det_eq_one {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det = 1) :
    (kron g 1)ᵀ * formJ 2 K * kron g 1 = formJ 2 K :=
  (kron_symplectic_iff _ _).mpr (by rw [hg, one_smul, transpose_one, Matrix.mul_one])

variable (K) in
@[expose] def diagSL : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K where
  toFun g := toSp (kron (g : Matrix (Fin 2) (Fin 2) K) 1) (kron_symplectic_of_det_eq_one g.2)
  map_one' := sp_ext (by simp [kron_one_one])
  map_mul' g h := sp_ext (by simp [kron_mul])

theorem coe_diagSL (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((diagSL K g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron (g : Matrix (Fin 2) (Fin 2) K) 1 := rfl

theorem mem_centralizer_T2_iff {x : StatedSp 2 K} :
    x ∈ centralizer {T2 K} ↔
      ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * kron 1 J₁ =
        kron 1 J₁ * ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
    simp only [Subgroup.coe_mul, Units.val_mul, coe_T2] at this
    exact this
  · intro h
    apply sp_ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_T2]
    exact h

theorem diagSL_mem_centralizer (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    diagSL K g ∈ centralizer {T2 K} := by
  rw [mem_centralizer_T2_iff, coe_diagSL, kron_mul, kron_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul]

@[expose] def blocksE (x : centralizer {T2 K}) : Matrix (Fin 2) (Fin 2) (Gauss K) :=
  (exists_gaussBlock_of_commute (mem_centralizer_T2_iff.mp x.2)).choose

theorem gaussBlock_blocksE (x : centralizer {T2 K}) :
    gaussBlock (blocksE x) = (((x : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
  (exists_gaussBlock_of_commute (mem_centralizer_T2_iff.mp x.2)).choose_spec

theorem blocksE_mul (x y : centralizer {T2 K}) : blocksE (x * y) = blocksE x * blocksE y :=
  gaussBlock_injective (by
    rw [gaussBlock_mul, gaussBlock_blocksE, gaussBlock_blocksE, gaussBlock_blocksE]
    rfl)

theorem blocksE_one : blocksE (1 : centralizer {T2 K}) = 1 :=
  gaussBlock_injective (by rw [gaussBlock_blocksE, gaussBlock_one]; rfl)

@[expose] def detE : centralizer {T2 K} →* Gauss K where
  toFun x := (blocksE x).det
  map_one' := by rw [blocksE_one, det_one]
  map_mul' x y := by rw [blocksE_mul, det_mul]

theorem mem_range_diagSL_of_detE (h2 : (2 : K) ≠ 0) (x : centralizer {T2 K})
    (h : detE x = 1) : (x : StatedSp 2 K) ∈ (diagSL K).range := by
  have hsym : (blocksE x)ᴴ * J₁E * blocksE x = J₁E := by
    rw [← gaussBlock_symplectic_iff, gaussBlock_blocksE]
    exact symplectic_of_mem _
  obtain ⟨g, hg, hZ⟩ := exists_map_of_det_eq_one h2 hsym h
  refine ⟨⟨g, hg⟩, sp_ext ((coe_diagSL _).trans ?_)⟩
  rw [← gaussBlock_blocksE x, hZ, gaussBlock_map]

theorem commutator_centralizer_T2_le (h2 : (2 : K) ≠ 0) :
    ⁅centralizer {T2 K}, centralizer {T2 K}⁆ ≤ (diagSL K).range := by
  rw [commutator_le]
  intro a ha b hb
  have h1 : detE ⁅(⟨a, ha⟩ : centralizer {T2 K}), ⟨b, hb⟩⁆ = 1 := by
    have h := map_commutatorElement (detE (K := K)).toHomUnits ⟨a, ha⟩ ⟨b, hb⟩
    have h' : ⁅(detE (K := K)).toHomUnits ⟨a, ha⟩, (detE (K := K)).toHomUnits ⟨b, hb⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    exact congrArg Units.val (h.trans h')
  exact mem_range_diagSL_of_detE h2 _ h1

variable (K) in
@[expose] def u2 : StatedProj (StatedSp 2 K) := proj 2 K (T2 K)

variable (K) in
@[expose] def Lsub : Subgroup (StatedProj (StatedSp 2 K)) := (diagSL K).range.map (proj 2 K)

theorem Lsub_le_centralizer : Lsub K ≤ centralizer {u2 K} := by
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  rw [mem_centralizer_singleton_iff, u2, ← map_mul, ← map_mul,
    mem_centralizer_singleton_iff.mp (diagSL_mem_centralizer g)]

theorem perfect_le_L (h2 : (2 : K) ≠ 0) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hM : M ≤ centralizer {u2 K}) (hperf : ⁅M, M⁆ = M) : M ≤ Lsub K := by
  have h1 := perfect_le_map_centralizer (T2 K) hM hperf
  rw [← hperf]
  calc ⁅M, M⁆ ≤ ⁅(centralizer {T2 K}).map (proj 2 K), (centralizer {T2 K}).map (proj 2 K)⁆ :=
        commutator_mono h1 h1
    _ = ⁅centralizer {T2 K}, centralizer {T2 K}⁆.map (proj 2 K) := (map_commutator _ _ _).symm
    _ ≤ Lsub K := map_mono (commutator_centralizer_T2_le h2)

end CFSG.ComponentClassification.CatFactsSp4
