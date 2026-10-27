module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSubspaceCount
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotent
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix

public section

namespace CFSG.AGLEmbedding.LeviBlock

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}

structure OrthCuts (r : ℕ) {s : ℕ} (d : Fin (s + 1) → ℕ) : Prop where
  mono : StrictMono d
  zero : d 0 = 0
  last : d (Fin.last s) ≤ r

variable (r) in
@[expose] noncomputable def orthParab (qA : QuadraticForm K A) {s : ℕ} (d : Fin (s + 1) → ℕ) :
    Subgroup ↥(orthElementaryGroup (quadTail r qA)) :=
  (⨅ i, MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
    (tailFlag K A r (d i))).subgroupOf (orthElementaryGroup (quadTail r qA))

variable {qA : QuadraticForm K A} {s : ℕ} {d : Fin (s + 1) → ℕ}

theorem mem_orthParab {x : ↥(orthElementaryGroup (quadTail r qA))} :
    x ∈ orthParab r qA d ↔ ∀ i, (tailFlag K A r (d i)).map
      ((x : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
        ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = tailFlag K A r (d i) := by
  simp only [orthParab, Subgroup.mem_subgroupOf, Subgroup.mem_iInf,
    Submodule.mem_stabilizer_submodule_iff_map_eq]
  rfl

theorem mapsTo_of_mem_orthParab {x : ↥(orthElementaryGroup (quadTail r qA))}
    (hx : x ∈ orthParab r qA d) (i : Fin (s + 1)) :
    ∀ v ∈ tailFlag K A r (d i),
      (x : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) v ∈
        tailFlag K A r (d i) := by
  intro v hv
  rw [← mem_orthParab.1 hx i]
  exact Submodule.mem_map_of_mem hv

@[expose] def orthCoefMat (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
    Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => (g (hypVec K A (.inl j))).1 (.inl i)

theorem orthCoefMat_apply (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
    (i j : Fin r) : orthCoefMat g i j = (g (hypVec K A (.inl j))).1 (.inl i) :=
  rfl

theorem orthCoefMat_one :
    orthCoefMat (1 : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = 1 := by
  ext i j
  simp [orthCoefMat_apply, hypVec, Pi.single_apply, Matrix.one_apply]

theorem orth_eq_sum_of_mem_tailFlag_top {v : (Fin r ⊕ Fin r → K) × A}
    (hv : v ∈ tailFlag K A r r) : v = ∑ p : Fin r, v.1 (.inl p) • hypVec K A (.inl p) := by
  obtain ⟨h1, h2⟩ := mem_tailFlag_top_iff.1 hv
  refine Prod.ext (funext fun c => ?_) ?_
  · rw [Prod.fst_sum, Finset.sum_apply]
    rcases c with i | i
    · rw [Finset.sum_eq_single i (fun p _ hp => by simp [hypVec, hp]) (by simp)]
      simp [hypVec]
    · simp [hypVec, h1 i]
  · simp [Prod.snd_sum, hypVec, h2]

theorem orthCoefMat_mul_apply (g h : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
    (i : Fin r) {j : Fin r} (hj : h (hypVec K A (.inl j)) ∈ tailFlag K A r r) :
    orthCoefMat (g * h) i j = (orthCoefMat g * orthCoefMat h) i j := by
  rw [orthCoefMat_apply, LinearEquiv.mul_apply, orth_eq_sum_of_mem_tailFlag_top hj, map_sum,
    Prod.fst_sum, Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem orth_fst_inl_eq_zero_of_mem_tailFlag {a : ℕ} {v : (Fin r ⊕ Fin r → K) × A}
    (hv : v ∈ tailFlag K A r a) {u : Fin r} (hu : a ≤ u) : v.1 (.inl u) = 0 :=
  (mem_flag.1 (mem_tailFlag_iff.1 hv).1).2 u hu

theorem orthHypVec_mem_tailFlag {a : ℕ} {j : Fin r} (hj : (j : ℕ) < a) :
    hypVec K A (.inl j) ∈ tailFlag K A r a :=
  Submodule.subset_span ⟨j, hj, rfl⟩

theorem orthTailFlag_mono {a b : ℕ} (hab : a ≤ b) : tailFlag K A r a ≤ tailFlag K A r b :=
  Submodule.span_mono (Set.image_mono fun j (hj : (j : ℕ) < a) => show (j : ℕ) < b by omega)

theorem orthCoefMat_eq_zero_of_mapsTo
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} {a : ℕ}
    (hg : ∀ v ∈ tailFlag K A r a, g v ∈ tailFlag K A r a) {u w : Fin r}
    (hw : (w : ℕ) < a) (hu : a ≤ u) : orthCoefMat g u w = 0 :=
  orth_fst_inl_eq_zero_of_mem_tailFlag (hg _ (orthHypVec_mem_tailFlag hw)) hu

variable (hd : OrthCuts r d)
include hd

@[expose] def orthBlockIdx (l : Fin s) (i : Fin (d l.succ - d l.castSucc)) : Fin r :=
  ⟨d l.castSucc + i, by
    have h1 := hd.mono.monotone (Fin.le_last l.succ)
    have h2 := hd.mono (Fin.castSucc_lt_succ (i := l))
    have := i.isLt
    have := hd.last
    omega⟩

theorem orthBlockIdx_val (l : Fin s) (i : Fin (d l.succ - d l.castSucc)) :
    (orthBlockIdx hd l i : ℕ) = d l.castSucc + i :=
  rfl

theorem orthBlockIdx_injective (l : Fin s) : Function.Injective (orthBlockIdx hd l) :=
  fun i j h => Fin.ext (by have := congrArg Fin.val h; simp only [orthBlockIdx_val] at this; omega)

theorem mem_range_orthBlockIdx (l : Fin s) (x : Fin r) :
    x ∈ Set.range (orthBlockIdx hd l) ↔ d l.castSucc ≤ x ∧ (x : ℕ) < d l.succ := by
  have h2 := hd.mono (Fin.castSucc_lt_succ (i := l))
  constructor
  · rintro ⟨i, rfl⟩
    rw [orthBlockIdx_val]
    have := i.isLt
    omega
  · rintro ⟨h1, h3⟩
    exact ⟨⟨x - d l.castSucc, by omega⟩, Fin.ext (by rw [orthBlockIdx_val]; simp only; omega)⟩

@[expose] def orthBlockMat (l : Fin s)
    (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
    Matrix (Fin (d l.succ - d l.castSucc)) (Fin (d l.succ - d l.castSucc)) K :=
  (orthCoefMat g).submatrix (orthBlockIdx hd l) (orthBlockIdx hd l)

theorem orthBlockMat_one (l : Fin s) :
    orthBlockMat hd l (1 : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = 1 := by
  rw [orthBlockMat, orthCoefMat_one]
  exact submatrix_one _ (orthBlockIdx_injective hd l)

theorem orthBlockMat_mul (l : Fin s)
    {g h : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : ∀ v ∈ tailFlag K A r (d l.castSucc), g v ∈ tailFlag K A r (d l.castSucc))
    (hh : ∀ v ∈ tailFlag K A r (d l.succ), h v ∈ tailFlag K A r (d l.succ)) :
    orthBlockMat hd l (g * h) = orthBlockMat hd l g * orthBlockMat hd l h := by
  have hle : d l.succ ≤ r := (hd.mono.monotone (Fin.le_last l.succ)).trans hd.last
  have hcol : (orthCoefMat (g * h)).submatrix (orthBlockIdx hd l) (orthBlockIdx hd l) =
      (orthCoefMat g * orthCoefMat h).submatrix (orthBlockIdx hd l) (orthBlockIdx hd l) := by
    ext i j
    simp only [submatrix_apply]
    refine orthCoefMat_mul_apply g h _ (orthTailFlag_mono hle (hh _ (orthHypVec_mem_tailFlag ?_)))
    have := (mem_range_orthBlockIdx hd l (orthBlockIdx hd l j)).1 ⟨j, rfl⟩
    exact this.2
  rw [orthBlockMat, hcol, submatrix_mul_of_cuts (orthBlockIdx_injective hd l)
    (pos := fun x : Fin r => (x : ℕ)) (mem_range_orthBlockIdx hd l)
    (fun u w hw hu => orthCoefMat_eq_zero_of_mapsTo hg hw hu)
    (fun u w hw hu => orthCoefMat_eq_zero_of_mapsTo hh hw hu)]
  rfl

theorem sub_mem_tailFlag_of_orthBlockMat_eq_one (l : Fin s)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : ∀ v ∈ tailFlag K A r (d l.castSucc), g v ∈ tailFlag K A r (d l.castSucc))
    (hg' : ∀ v ∈ tailFlag K A r (d l.succ), g v ∈ tailFlag K A r (d l.succ))
    (h1 : orthBlockMat hd l g = 1) {x : (Fin r ⊕ Fin r → K) × A}
    (hx : x ∈ tailFlag K A r (d l.succ)) : g x - x ∈ tailFlag K A r (d l.castSucc) := by
  have hle : d l.succ ≤ r := (hd.mono.monotone (Fin.le_last l.succ)).trans hd.last
  have hab : d l.castSucc ≤ d l.succ := (hd.mono (Fin.castSucc_lt_succ (i := l))).le
  have hxr : x ∈ tailFlag K A r r := orthTailFlag_mono hle hx
  have hy : g x - x ∈ tailFlag K A r (d l.succ) := Submodule.sub_mem _ (hg' x hx) hx
  obtain ⟨hy1, hy2⟩ := mem_tailFlag_iff.1 hy
  refine mem_tailFlag_iff.2 ⟨mem_flag.2 ⟨(mem_flag.1 hy1).1, fun u hu => ?_⟩, hy2⟩
  by_cases hub : d l.succ ≤ (u : ℕ)
  · exact (mem_flag.1 hy1).2 u hub
  push Not at hub
  have hcoef : ∀ p : Fin r, x.1 (.inl p) * orthCoefMat g u p =
      x.1 (.inl p) * (1 : Matrix (Fin r) (Fin r) K) u p := by
    intro p
    by_cases hpa : (p : ℕ) < d l.castSucc
    · rw [orthCoefMat_eq_zero_of_mapsTo hg hpa hu, Matrix.one_apply_ne
        (fun h => by rw [h] at hu; omega)]
    by_cases hpb : (p : ℕ) < d l.succ
    · obtain ⟨i, rfl⟩ := (mem_range_orthBlockIdx hd l u).2 ⟨hu, hub⟩
      obtain ⟨j, rfl⟩ := (mem_range_orthBlockIdx hd l p).2 ⟨not_lt.1 hpa, hpb⟩
      have := congrFun (congrFun h1 i) j
      rw [orthBlockMat, submatrix_apply] at this
      simp only [this, Matrix.one_apply, (orthBlockIdx_injective hd l).eq_iff]
    · rw [orth_fst_inl_eq_zero_of_mem_tailFlag hx (not_lt.1 hpb), zero_mul, zero_mul]
  have hgx : (g x).1 (.inl u) = x.1 (.inl u) := by
    conv_lhs => rw [orth_eq_sum_of_mem_tailFlag_top hxr]
    rw [map_sum, Prod.fst_sum, Finset.sum_apply]
    simp only [map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    have : ∀ p : Fin r, x.1 (.inl p) * (g (hypVec K A (.inl p))).1 (.inl u) =
        x.1 (.inl p) * orthCoefMat g u p := fun p => rfl
    simp only [this, hcoef, Matrix.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [Prod.fst_sub, Pi.sub_apply, hgx, sub_self]

variable (qA) in
@[expose] noncomputable def orthBlockHom (l : Fin s) :
    ↥(orthParab r qA d) →* GL (Fin (d l.succ - d l.castSucc)) K :=
  MonoidHom.toHomUnits
    { toFun := fun x => orthBlockMat hd l ((x : ↥(orthElementaryGroup (quadTail r qA))) :
        ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
      map_one' := orthBlockMat_one hd l
      map_mul' := fun x y => orthBlockMat_mul hd l
        (mapsTo_of_mem_orthParab x.2 l.castSucc) (mapsTo_of_mem_orthParab y.2 l.succ) }

theorem coe_orthBlockHom (l : Fin s) (x : ↥(orthParab r qA d)) :
    ((orthBlockHom qA hd l x : GL (Fin (d l.succ - d l.castSucc)) K) :
      Matrix (Fin (d l.succ - d l.castSucc)) (Fin (d l.succ - d l.castSucc)) K) =
      orthBlockMat hd l ((x : ↥(orthElementaryGroup (quadTail r qA))) :
        ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  rfl

theorem sub_mem_tailFlag_of_orthBlockHom_eq_one (l : Fin s) {x : ↥(orthParab r qA d)}
    (h1 : orthBlockHom qA hd l x = 1) {v : (Fin r ⊕ Fin r → K) × A}
    (hv : v ∈ tailFlag K A r (d l.succ)) :
    ((x : ↥(orthElementaryGroup (quadTail r qA))) :
      ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) v - v ∈
        tailFlag K A r (d l.castSucc) :=
  sub_mem_tailFlag_of_orthBlockMat_eq_one hd l (mapsTo_of_mem_orthParab x.2 l.castSucc)
    (mapsTo_of_mem_orthParab x.2 l.succ) (by rw [← coe_orthBlockHom, h1, Units.val_one]) hv

end CFSG.AGLEmbedding.LeviBlock
