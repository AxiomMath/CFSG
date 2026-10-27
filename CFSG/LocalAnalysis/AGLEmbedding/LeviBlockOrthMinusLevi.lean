module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusRes
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel

public section

namespace CFSG.AGLEmbedding.LeviBlock

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r s : ℕ}
  {d : Fin (s + 1) → ℕ} (hd : OrthCuts r d)

@[expose] noncomputable def orthExtendGL (l : Fin s) :
    GL (Fin (d l.succ - d l.castSucc)) K →* GL (Fin r) K :=
  Units.map
    { toFun := extendMat (orthBlockIdx_injective hd l)
      map_one' := extendMat_one _
      map_mul' := extendMat_mul _ }

theorem coe_orthExtendGL (l : Fin s) (B : GL (Fin (d l.succ - d l.castSucc)) K) :
    ((orthExtendGL hd l B : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      extendMat (orthBlockIdx_injective hd l) (B : Matrix _ _ K) :=
  rfl

theorem orthBlockIdx_ne {l l' : Fin s} (h : l' ≠ l) (i : Fin (d l'.succ - d l'.castSucc))
    (j : Fin (d l.succ - d l.castSucc)) : orthBlockIdx hd l' i ≠ orthBlockIdx hd l j := by
  intro e
  have hi := (mem_range_orthBlockIdx hd l' (orthBlockIdx hd l' i)).1 ⟨i, rfl⟩
  have hj := (mem_range_orthBlockIdx hd l (orthBlockIdx hd l j)).1 ⟨j, rfl⟩
  rw [e] at hi
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have := hd.mono.monotone (Fin.succ_le_castSucc_iff.2 hlt)
    omega
  · have := hd.mono.monotone (Fin.succ_le_castSucc_iff.2 hlt)
    omega

theorem extendMat_orthBlock_eq_zero (l : Fin s) (M : Matrix (Fin (d l.succ - d l.castSucc))
    (Fin (d l.succ - d l.castSucc)) K) (i : Fin (s + 1)) {p q : Fin r} (hp : (p : ℕ) < d i)
    (hq : d i ≤ q) : extendMat (orthBlockIdx_injective hd l) M q p = 0 := by
  by_cases h : q ∈ Set.range (orthBlockIdx hd l) ∧ p ∈ Set.range (orthBlockIdx hd l)
  · exfalso
    obtain ⟨hq1, hq2⟩ := (mem_range_orthBlockIdx hd l q).1 h.1
    obtain ⟨hp1, hp2⟩ := (mem_range_orthBlockIdx hd l p).1 h.2
    have h1 : l.castSucc < i := hd.mono.lt_iff_lt.1 (by omega)
    have h2 : i < l.succ := hd.mono.lt_iff_lt.1 (by omega)
    exact absurd (Fin.castSucc_lt_iff_succ_le.1 h1) (not_le.2 h2)
  · rw [not_and_or] at h
    rw [extendMat_apply_of_not_mem _ M h, Matrix.one_apply_ne (fun e => by subst e; omega)]

theorem extendMat_orthBlock_apply_of_le (l : Fin s) (M : Matrix (Fin (d l.succ - d l.castSucc))
    (Fin (d l.succ - d l.castSucc)) K) {p q : Fin r} (hq : d l.succ ≤ q) :
    extendMat (orthBlockIdx_injective hd l) M q p = (1 : Matrix (Fin r) (Fin r) K) q p :=
  extendMat_apply_of_not_mem _ M (Or.inl fun hm => by
    have := ((mem_range_orthBlockIdx hd l q).1 hm).2
    omega)

variable (A) in
@[expose] noncomputable def orthLeviGL (l : Fin s) :
    GL (Fin (d l.succ - d l.castSucc)) K →*
      ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) where
  toFun B := dMap (orthExtendGL hd l B) (1 : A ≃ₗ[K] A)
  map_one' := by rw [map_one, dMap_one_one]
  map_mul' B C := by rw [map_mul, dMap_mul_dMap, mul_one]

theorem orthLeviGL_apply (l : Fin s) (B : GL (Fin (d l.succ - d l.castSucc)) K) :
    orthLeviGL A hd l B = dMap (orthExtendGL hd l B) (1 : A ≃ₗ[K] A) :=
  rfl

theorem orthCoefMat_dMap (D : GL (Fin r) K) :
    orthCoefMat (dMap D (1 : A ≃ₗ[K] A)) = (D : Matrix (Fin r) (Fin r) K) := by
  ext i j
  rw [orthCoefMat_apply, dMap_apply]
  simp [hypVec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem orthBlockMat_orthLeviGL_self (l : Fin s) (B : GL (Fin (d l.succ - d l.castSucc)) K) :
    orthBlockMat hd l (orthLeviGL A hd l B) = (B : Matrix _ _ K) := by
  rw [orthBlockMat, orthLeviGL_apply, orthCoefMat_dMap, coe_orthExtendGL, submatrix_extendMat]

theorem orthBlockMat_orthLeviGL_of_ne {l l' : Fin s} (h : l' ≠ l)
    (B : GL (Fin (d l.succ - d l.castSucc)) K) :
    orthBlockMat hd l' (orthLeviGL A hd l B) = 1 := by
  rw [orthBlockMat, orthLeviGL_apply, orthCoefMat_dMap, coe_orthExtendGL]
  exact submatrix_extendMat_of_disjoint _ (orthBlockIdx_injective hd l') (orthBlockIdx_ne hd h) _

theorem orthLeviGL_mapsTo (l : Fin s) (B : GL (Fin (d l.succ - d l.castSucc)) K)
    (i : Fin (s + 1)) {v : (Fin r ⊕ Fin r → K) × A} (hv : v ∈ tailFlag K A r (d i)) :
    orthLeviGL A hd l B v ∈ tailFlag K A r (d i) := by
  obtain ⟨hv1, hv2⟩ := mem_tailFlag_iff.1 hv
  obtain ⟨hf, he⟩ := mem_flag.1 hv1
  have hf' : v.1 ∘ Sum.inr = 0 := funext hf
  refine mem_tailFlag_iff.2 ⟨mem_flag.2 ⟨fun j => ?_, fun q hq => ?_⟩, ?_⟩
  · rw [orthLeviGL_apply, dMap_apply]
    simp [hf']
  · rw [orthLeviGL_apply, dMap_apply]
    simp only [Sum.elim_inl, Matrix.mulVec, dotProduct, Function.comp_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : (p : ℕ) < d i
    · rw [coe_orthExtendGL, extendMat_orthBlock_eq_zero hd l _ i hp hq, zero_mul]
    · rw [he p (not_lt.1 hp), mul_zero]
  · rw [orthLeviGL_apply, dMap_apply]
    exact hv2

theorem map_tailFlag_orthLeviGL (l : Fin s) (B : GL (Fin (d l.succ - d l.castSucc)) K)
    (i : Fin (s + 1)) :
    (tailFlag K A r (d i)).map ((orthLeviGL A hd l B : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = tailFlag K A r (d i) := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact orthLeviGL_mapsTo hd l B i hv
  · refine ⟨orthLeviGL A hd l B⁻¹ v, orthLeviGL_mapsTo hd l B⁻¹ i hv, ?_⟩
    change (orthLeviGL A hd l B * orthLeviGL A hd l B⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one, id]

theorem orthResMat_orthLeviGL (l : Fin s) (B : GL (Fin (d l.succ - d l.castSucc)) K) :
    orthResMat hd.last (orthLeviGL A hd l B) = 1 := by
  have hlt : d l.succ ≤ d (Fin.last s) := hd.mono.monotone (Fin.le_last _)
  have key : ∀ (M : Matrix (Fin (d l.succ - d l.castSucc)) (Fin (d l.succ - d l.castSucc)) K)
      (x : Fin r → K) (hx : ∀ p : Fin r, (p : ℕ) < d (Fin.last s) → x p = 0) (q : Fin r)
      (hq : d (Fin.last s) ≤ q), (extendMat (orthBlockIdx_injective hd l) M *ᵥ x) q = x q := by
    intro M x hx q hq
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single q]
    · rw [extendMat_orthBlock_apply_of_le hd l M (by omega), Matrix.one_apply_eq, one_mul]
    · intro p _ hpq
      by_cases hp : (p : ℕ) < d (Fin.last s)
      · rw [hx p hp, mul_zero]
      · rw [extendMat_orthBlock_apply_of_le hd l M (by omega), Matrix.one_apply_ne hpq.symm,
          zero_mul]
    · simp
  have keyT : ∀ (M : Matrix (Fin (d l.succ - d l.castSucc)) (Fin (d l.succ - d l.castSucc)) K)
      (x : Fin r → K) (hx : ∀ p : Fin r, (p : ℕ) < d (Fin.last s) → x p = 0) (q : Fin r)
      (hq : d (Fin.last s) ≤ q), ((extendMat (orthBlockIdx_injective hd l) M)ᵀ *ᵥ x) q = x q := by
    intro M x hx q hq
    rw [extendMat_transpose]
    exact key Mᵀ x hx q hq
  have hlow : ∀ (x : (Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × A)
      (c : Fin r → Fin r ⊕ Fin r) (hc : ∀ p, c p = .inl p ∨ c p = .inr p) (p : Fin r),
      (p : ℕ) < d (Fin.last s) → (orthResIncl K A hd.last x).1 (c p) = 0 := by
    intro x c hc p hp
    obtain ⟨y, rfl⟩ := (splitIdx hd.last).surjective p
    rcases y with i | i
    · rcases hc (splitIdx hd.last (.inl i)) with h | h <;> rw [h] <;>
        simp [orthResIncl_apply, joinHi]
    · rw [splitIdx_inr] at hp
      omega
  have hinv : ((orthExtendGL hd l B)⁻¹ : GL (Fin r) K) = orthExtendGL hd l B⁻¹ :=
    (map_inv _ B).symm
  refine LinearMap.ext fun u => Prod.ext (funext fun c => ?_) ?_
  · rw [orthResMat_apply, orthLeviGL_apply, orthResProj_apply, dMap_apply, Module.End.one_apply]
    rcases c with j | j
    · simp only [hiPart, Sum.elim_inl, Function.comp_def]
      rw [coe_orthExtendGL, key _ _ (hlow u _ (fun p => Or.inl rfl)) _
        (by rw [splitIdx_inr]; omega)]
      simp [orthResIncl_apply, joinHi]
    · simp only [hiPart, Sum.elim_inr, Function.comp_def]
      rw [hinv, coe_orthExtendGL, keyT _ _ (hlow u _ (fun p => Or.inr rfl)) _
        (by rw [splitIdx_inr]; omega)]
      simp [orthResIncl_apply, joinHi]
  · rfl

theorem orthLeviGL_mem_orthElementaryGroup [CharP K 2] {qA : QuadraticForm K A} (hr : 3 ≤ r)
    (l : Fin s) {B : GL (Fin (d l.succ - d l.castSucc)) K}
    (hB : (B : Matrix (Fin (d l.succ - d l.castSucc)) (Fin (d l.succ - d l.castSucc)) K).det = 1) :
    orthLeviGL A hd l B ∈ orthElementaryGroup (quadTail r qA) :=
  NonsplitOrthogonalCover.dMap_one_mem_orthElementaryGroup hr
    (by rw [coe_orthExtendGL, det_extendMat, hB])

variable (qA : QuadraticForm K A)

@[expose] noncomputable def orthLeviSL [CharP K 2] (hr : 3 ≤ r) (l : Fin s) :
    SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* ↥(orthParab r qA d) where
  toFun B := ⟨⟨orthLeviGL A hd l (SpecialLinearGroup.toGL B),
    orthLeviGL_mem_orthElementaryGroup hd hr l B.2⟩,
    mem_orthParab.2 fun i => map_tailFlag_orthLeviGL hd l _ i⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' B C := Subtype.ext (Subtype.ext (by simp))

theorem coe_orthLeviSL [CharP K 2] (hr : 3 ≤ r) (l : Fin s)
    (B : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K) :
    (((orthLeviSL hd qA hr l B : ↥(orthParab r qA d)) : ↥(orthElementaryGroup (quadTail r qA))) :
      ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
      orthLeviGL A hd l (SpecialLinearGroup.toGL B) :=
  rfl

theorem orthBlockHom_orthLeviSL_self [CharP K 2] (hr : 3 ≤ r) (l : Fin s)
    (B : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K) :
    orthBlockHom qA hd l (orthLeviSL hd qA hr l B) = SpecialLinearGroup.toGL B :=
  Units.ext (orthBlockMat_orthLeviGL_self hd l _)

theorem orthBlockHom_orthLeviSL_of_ne [CharP K 2] (hr : 3 ≤ r) {l l' : Fin s} (h : l' ≠ l)
    (B : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K) :
    orthBlockHom qA hd l' (orthLeviSL hd qA hr l B) = 1 :=
  Units.ext (orthBlockMat_orthLeviGL_of_ne hd h _)

theorem orthResHom_orthLeviSL [CharP K 2] (hr : 3 ≤ r) (l : Fin s)
    (B : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K) :
    orthResHom qA hd (orthLeviSL hd qA hr l B) = 1 :=
  LinearEquiv.ext fun u => by
    rw [orthResHom_apply, coe_orthLeviSL, orthResMat_orthLeviGL]
    rfl

end CFSG.AGLEmbedding.LeviBlock
