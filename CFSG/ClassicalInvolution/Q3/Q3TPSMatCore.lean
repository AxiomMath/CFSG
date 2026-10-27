module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.WeakCT (diagConj2)

variable {F : Type} [Field F]

private theorem mulVec_apply4 (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (v : Fin 2 ⊕ Fin 2 → F)
    (a : Fin 2 ⊕ Fin 2) :
    (M *ᵥ v) a = M a (Sum.inl 0) * v (Sum.inl 0) + M a (Sum.inl 1) * v (Sum.inl 1) +
      M a (Sum.inr 0) * v (Sum.inr 0) + M a (Sum.inr 1) * v (Sum.inr 1) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

private def planeVec (k : Fin 2) (x : Fin 2 → F) : Fin 2 ⊕ Fin 2 → F := fun a =>
  if a = Sum.inl k then x 0 else if a = Sum.inr k then x 1 else 0

private theorem planeVec_inl (k : Fin 2) (x : Fin 2 → F) : planeVec k x (Sum.inl k) = x 0 := by
  simp [planeVec]

private theorem planeVec_inr (k : Fin 2) (x : Fin 2 → F) : planeVec k x (Sum.inr k) = x 1 := by
  simp [planeVec]

private theorem planeVec_of_not_mem (k : Fin 2) (x : Fin 2 → F) {a : Fin 2 ⊕ Fin 2}
    (ha : a ∉ coords k) :
    planeVec k x a = 0 := by
  rw [mem_coords, not_or] at ha
  simp [planeVec, ha.1, ha.2]

private theorem planeVec_injective (k : Fin 2) : Function.Injective (planeVec (F := F) k) := by
  intro x y h
  funext i
  fin_cases i
  · simpa [planeVec_inl] using congrFun h (Sum.inl k)
  · simpa [planeVec_inr] using congrFun h (Sum.inr k)


private def IsPlaneVec (k : Fin 2) (v : Fin 2 ⊕ Fin 2 → F) : Prop := ∀ a, a ∉ coords k → v a = 0

private theorem isPlaneVec_planeVec (k : Fin 2) (x : Fin 2 → F) : IsPlaneVec k (planeVec k x) :=
  fun _ ha => planeVec_of_not_mem k x ha

private theorem eq_planeVec_of_isPlaneVec {k : Fin 2} {v : Fin 2 ⊕ Fin 2 → F}
    (hv : IsPlaneVec k v) :
    v = planeVec k ![v (Sum.inl k), v (Sum.inr k)] := by
  funext a
  by_cases ha : a ∈ coords k
  · rcases mem_coords.1 ha with rfl | rfl
    · simp [planeVec_inl]
    · simp [planeVec_inr]
  · rw [hv a ha, planeVec_of_not_mem k _ ha]

private theorem mulVec_blockMat_planeVec (k : Fin 2) (S : Matrix (Fin 2) (Fin 2) F)
    (y : Fin 2 → F) :
    (blockMat (Sum.inl k) (Sum.inr k) S : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
      planeVec k y = planeVec k (S *ᵥ y) := by
  funext a
  rw [mulVec_apply4]
  fin_cases k <;> rcases a with a | a <;> fin_cases a <;>
    simp [blockMat, planeVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]


abbrev Mat4 (F : Type) := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

private theorem form_apply4 (u v : Fin 2 ⊕ Fin 2 → F) :
    form u v = u (Sum.inl 0) * v (Sum.inr 0) + u (Sum.inl 1) * v (Sum.inr 1) -
      u (Sum.inr 0) * v (Sum.inl 0) - u (Sum.inr 1) * v (Sum.inl 1) := by
  rw [form_apply]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, sgn_inl, sgn_inr, par_inl, par_inr]
  ring

theorem form_mulVec_of_sim {M : Mat4 F} {m : F} (h : Mᵀ * gram F 2 * M = m • gram F 2)
    (u v : Fin 2 ⊕ Fin 2 → F) : form (M *ᵥ u) (M *ᵥ v) = m * form u v := by
  unfold form
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h, Matrix.smul_mulVec, dotProduct_smul]
  rfl

private theorem isPlaneVec_zero_iff {v : Fin 2 ⊕ Fin 2 → F} :
    IsPlaneVec 0 v ↔ v (Sum.inl 1) = 0 ∧ v (Sum.inr 1) = 0 := by
  constructor
  · intro h
    exact ⟨h _ (by simp [mem_coords]), h _ (by simp [mem_coords])⟩
  · rintro ⟨h1, h2⟩ a ha
    rcases a with a | a <;> fin_cases a <;> simp_all [mem_coords]

private theorem isPlaneVec_one_iff {v : Fin 2 ⊕ Fin 2 → F} :
    IsPlaneVec 1 v ↔ v (Sum.inl 0) = 0 ∧ v (Sum.inr 0) = 0 := by
  constructor
  · intro h
    exact ⟨h _ (by simp [mem_coords]), h _ (by simp [mem_coords])⟩
  · rintro ⟨h1, h2⟩ a ha
    rcases a with a | a <;> fin_cases a <;> simp_all [mem_coords]

private theorem mulVec_blockMat_inl (k : Fin 2) (S : Matrix (Fin 2) (Fin 2) F)
    (u : Fin 2 ⊕ Fin 2 → F) :
    ((blockMat (Sum.inl k) (Sum.inr k) S : Mat4 F) *ᵥ u) (Sum.inl k) =
      S 0 0 * u (Sum.inl k) + S 0 1 * u (Sum.inr k) := by
  rw [mulVec_apply4]
  fin_cases k <;> simp [blockMat]

private theorem mulVec_blockMat_inr (k : Fin 2) (S : Matrix (Fin 2) (Fin 2) F)
    (u : Fin 2 ⊕ Fin 2 → F) :
    ((blockMat (Sum.inl k) (Sum.inr k) S : Mat4 F) *ᵥ u) (Sum.inr k) =
      S 1 0 * u (Sum.inl k) + S 1 1 * u (Sum.inr k) := by
  rw [mulVec_apply4]
  fin_cases k <;> simp [blockMat]

private theorem mulVec_blockMat_of_not_mem (k : Fin 2) (S : Matrix (Fin 2) (Fin 2) F)
    (u : Fin 2 ⊕ Fin 2 → F) {a : Fin 2 ⊕ Fin 2} (ha : a ∉ coords k) :
    ((blockMat (Sum.inl k) (Sum.inr k) S : Mat4 F) *ᵥ u) a = u a := by
  rw [mulVec_apply4]
  rw [mem_coords, not_or] at ha
  fin_cases k <;> rcases a with a | a <;> fin_cases a <;> simp_all [blockMat]


theorem map_blockMat (σ : F ≃+* F) (k : Fin 2) (S : Matrix (Fin 2) (Fin 2) F) :
    (blockMat (Sum.inl k) (Sum.inr k) S : Mat4 F).map σ =
      blockMat (Sum.inl k) (Sum.inr k) (S.map σ) := by
  ext a b
  simp only [Matrix.map_apply, blockMat, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp [*]

private theorem blockMat_mulVec_eq_self_of_isPlaneVec_zero (S : Matrix (Fin 2) (Fin 2) F)
    {v : Fin 2 ⊕ Fin 2 → F} (hv : IsPlaneVec 0 v) :
    (blockMat (Sum.inl 1) (Sum.inr 1) S : Mat4 F) *ᵥ v = v :=
  mulVec_eq_self_of_isSupp (isSupp_blockMat 1 S) fun t ht => hv t (by
    rw [mem_coords] at ht
    rcases ht with rfl | rfl <;> simp [mem_coords])

private theorem isPlaneVec_zero_of_fix (σ : F ≃+* F) {u : Fin 2 ⊕ Fin 2 → F}
    (hup : (blockMat (Sum.inl 1) (Sum.inr 1)
      (((sl2Upper (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ) : Mat4 F) *ᵥ u = u)
    (hlo : (blockMat (Sum.inl 1) (Sum.inr 1)
      (((sl2Lower (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ) : Mat4 F) *ᵥ u = u) :
    IsPlaneVec 0 u := by
  rw [isPlaneVec_zero_iff]
  have h1 := congrFun hup (Sum.inl 1)
  have h2 := congrFun hlo (Sum.inr 1)
  rw [mulVec_blockMat_inl] at h1
  rw [mulVec_blockMat_inr] at h2
  simp [CFSG.LieType.Steinberg.coe_sl2Upper, CFSG.LieType.Steinberg.coe_sl2Lower] at h1 h2
  exact ⟨h2, h1⟩


private theorem isPlaneVec_zero_of_fix' {u : Fin 2 ⊕ Fin 2 → F} (S T : Matrix (Fin 2) (Fin 2) F)
    (hS : S = !![1, 1; 0, 1]) (hT : T = !![1, 0; 1, 1])
    (hup : (blockMat (Sum.inl 1) (Sum.inr 1) S : Mat4 F) *ᵥ u = u)
    (hlo : (blockMat (Sum.inl 1) (Sum.inr 1) T : Mat4 F) *ᵥ u = u) : IsPlaneVec 0 u := by
  rw [isPlaneVec_zero_iff]
  have h1 := congrFun hup (Sum.inl 1)
  have h2 := congrFun hlo (Sum.inr 1)
  rw [mulVec_blockMat_inl] at h1
  rw [mulVec_blockMat_inr] at h2
  subst hS hT
  simp at h1 h2
  exact ⟨h2, h1⟩

private theorem fix_of_conj {A B X : Mat4 F} (hBA : B * A = 1) {v : Fin 2 ⊕ Fin 2 → F}
    (h : (A * X * B) *ᵥ v = v) : X *ᵥ (B *ᵥ v) = B *ᵥ v := by
  calc X *ᵥ (B *ᵥ v) = (B * A) *ᵥ (X *ᵥ (B *ᵥ v)) := by rw [hBA, Matrix.one_mulVec]
    _ = B *ᵥ ((A * X * B) *ᵥ v) := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = B *ᵥ v := by rw [h]

private theorem conj_fix {A B X Y : Mat4 F} (hBA : B * A = 1) (hXY : A * X * B = Y)
    {v : Fin 2 ⊕ Fin 2 → F} (hv : X *ᵥ v = v) : Y *ᵥ (A *ᵥ v) = A *ᵥ v := by
  rw [← hXY]
  calc (A * X * B) *ᵥ (A *ᵥ v) = A *ᵥ (X *ᵥ ((B * A) *ᵥ v)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = A *ᵥ v := by rw [hBA, Matrix.one_mulVec, hv]

private theorem sl2Upper_one_map (σ : F ≃+* F) :
    ((sl2Upper (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ = !![1, 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Steinberg.coe_sl2Upper]

private theorem sl2Lower_one_map (σ : F ≃+* F) :
    ((sl2Lower (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ = !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Steinberg.coe_sl2Lower]

private theorem sl2Upper_one_coe :
    ((sl2Upper (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl

private theorem sl2Lower_one_coe :
    ((sl2Lower (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl


private theorem planes_preserved {A B : Mat4 F} (hAB : A * B = 1) (hBA : B * A = 1) (σ : F ≃+* F)
    {m : F} (hm : m ≠ 0) (hsim : ∀ u v, form (A *ᵥ u) (A *ᵥ v) = m * form u v)
    (hL : ∀ s : SL(2, F), ∃ s' : SL(2, F),
      A * blockMat (Sum.inl 1) (Sum.inr 1) ((s : Matrix (Fin 2) (Fin 2) F).map σ) * B =
        blockMat (Sum.inl 1) (Sum.inr 1) (s' : Matrix (Fin 2) (Fin 2) F))
    (hL' : ∀ s' : SL(2, F), ∃ s : SL(2, F),
      A * blockMat (Sum.inl 1) (Sum.inr 1) ((s : Matrix (Fin 2) (Fin 2) F).map σ) * B =
        blockMat (Sum.inl 1) (Sum.inr 1) (s' : Matrix (Fin 2) (Fin 2) F)) :
    (∀ v, IsPlaneVec 0 v → IsPlaneVec 0 (A *ᵥ v)) ∧ (∀ v, IsPlaneVec 0 v → IsPlaneVec 0 (B *ᵥ v)) ∧
      (∀ v, IsPlaneVec 1 v → IsPlaneVec 1 (A *ᵥ v)) ∧
      (∀ v, IsPlaneVec 1 v → IsPlaneVec 1 (B *ᵥ v)) := by
  have hB0 : ∀ v, IsPlaneVec 0 v → IsPlaneVec 0 (B *ᵥ v) := by
    intro v hv
    refine isPlaneVec_zero_of_fix' _ _ (sl2Upper_one_map σ) (sl2Lower_one_map σ) ?_ ?_
    · obtain ⟨s', hs'⟩ := hL (sl2Upper 1)
      refine fix_of_conj hBA ?_
      rw [hs']
      exact blockMat_mulVec_eq_self_of_isPlaneVec_zero _ hv
    · obtain ⟨s', hs'⟩ := hL (sl2Lower 1)
      refine fix_of_conj hBA ?_
      rw [hs']
      exact blockMat_mulVec_eq_self_of_isPlaneVec_zero _ hv
  have hA0 : ∀ v, IsPlaneVec 0 v → IsPlaneVec 0 (A *ᵥ v) := by
    intro v hv
    refine isPlaneVec_zero_of_fix' _ _ rfl rfl ?_ ?_
    · obtain ⟨s, hs⟩ := hL' (sl2Upper 1)
      exact conj_fix hBA hs (blockMat_mulVec_eq_self_of_isPlaneVec_zero _ hv)
    · obtain ⟨s, hs⟩ := hL' (sl2Lower 1)
      exact conj_fix hBA hs (blockMat_mulVec_eq_self_of_isPlaneVec_zero _ hv)
  have hsimB : ∀ u v, m * form (B *ᵥ u) (B *ᵥ v) = form u v := by
    intro u v
    have h := hsim (B *ᵥ u) (B *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec,
      Matrix.one_mulVec] at h
    exact h.symm
  have hsingle0 : ∀ b : Fin 2 ⊕ Fin 2, b ∈ coords 0 →
      IsPlaneVec 0 (Pi.single b (1 : F) : Fin 2 ⊕ Fin 2 → F) := by
    intro b hb a ha
    have : a ≠ b := fun h => ha (h ▸ hb)
    simp [this]
  have horth : ∀ u v : Fin 2 ⊕ Fin 2 → F, IsPlaneVec 0 u → IsPlaneVec 1 v → form u v = 0 := by
    intro u v hu hv
    refine form_eq_zero_of_supp (S := coords 1) (parClosed_coords 1) (fun a ha => hu a ?_)
      (fun a ha => hv a ha)
    intro h0
    rw [mem_coords] at ha h0
    rcases ha with rfl | rfl <;> simp_all
  refine ⟨hA0, hB0, ?_, ?_⟩
  · intro v hv
    rw [isPlaneVec_one_iff]
    have h1 : form (Pi.single (Sum.inl 0) 1) (A *ᵥ v) = 0 := by
      have hb := hB0 _ (hsingle0 (Sum.inl 0) (inl_mem_coords 0))
      calc form (Pi.single (Sum.inl 0) 1) (A *ᵥ v)
          = form (A *ᵥ (B *ᵥ Pi.single (Sum.inl 0) 1)) (A *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
        _ = m * form (B *ᵥ Pi.single (Sum.inl 0) 1) v := hsim _ _
        _ = 0 := by rw [horth _ _ hb hv, mul_zero]
    have h2 : form (Pi.single (Sum.inr 0) 1) (A *ᵥ v) = 0 := by
      have hb := hB0 _ (hsingle0 (Sum.inr 0) (inr_mem_coords 0))
      calc form (Pi.single (Sum.inr 0) 1) (A *ᵥ v)
          = form (A *ᵥ (B *ᵥ Pi.single (Sum.inr 0) 1)) (A *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
        _ = m * form (B *ᵥ Pi.single (Sum.inr 0) 1) v := hsim _ _
        _ = 0 := by rw [horth _ _ hb hv, mul_zero]
    rw [form_apply4] at h1 h2
    simp at h1 h2
    exact ⟨h2, h1⟩
  · intro v hv
    rw [isPlaneVec_one_iff]
    have key : ∀ b : Fin 2 ⊕ Fin 2, b ∈ coords 0 →
        form (Pi.single b 1) (B *ᵥ v) = 0 := by
      intro b hb
      have ha := hA0 _ (hsingle0 b hb)
      have h := hsimB (A *ᵥ Pi.single b 1) v
      rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec, horth _ _ ha hv] at h
      exact (mul_eq_zero.1 h).resolve_left hm
    have h1 := key (Sum.inl 0) (inl_mem_coords 0)
    have h2 := key (Sum.inr 0) (inr_mem_coords 0)
    rw [form_apply4] at h1 h2
    simp at h1 h2
    exact ⟨h2, h1⟩


private theorem coe_gsp_inv_matrix (A : gsp 2 F) :
    (((A⁻¹ : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) =
      (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := rfl

theorem mat_conjSp_fieldSp (A : gsp 2 F) (σ : F ≃+* F) (x : StatedSp 2 F) :
    mat 2 F (conjSp 2 F A (fieldSp 2 F σ x)) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) * (mat 2 F x).map σ *
        (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := by
  rw [mat_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp, mat_apply]

private theorem mulVec_planeVec_inl (M : Mat4 F) (k : Fin 2) (y : Fin 2 → F) :
    (M *ᵥ planeVec k y) (Sum.inl k) = M (Sum.inl k) (Sum.inl k) * y 0 +
      M (Sum.inl k) (Sum.inr k) * y 1 := by
  rw [mulVec_apply4]
  fin_cases k <;> simp [planeVec]

private theorem mulVec_planeVec_inr (M : Mat4 F) (k : Fin 2) (y : Fin 2 → F) :
    (M *ᵥ planeVec k y) (Sum.inr k) = M (Sum.inr k) (Sum.inl k) * y 0 +
      M (Sum.inr k) (Sum.inr k) * y 1 := by
  rw [mulVec_apply4]
  fin_cases k <;> simp [planeVec]

private theorem mulVec_planeVec_of_preserves {M : Mat4 F} (k : Fin 2)
    (hM : ∀ v, IsPlaneVec k v → IsPlaneVec k (M *ᵥ v)) (y : Fin 2 → F) :
    M *ᵥ planeVec k y = planeVec k (stdBlock k M *ᵥ y) := by
  refine (eq_planeVec_of_isPlaneVec (hM _ (isPlaneVec_planeVec k y))).trans
    (congrArg (planeVec k) ?_)
  funext i
  fin_cases i
  · show (M *ᵥ planeVec k y) (Sum.inl k) = _
    rw [mulVec_planeVec_inl]
    simp [stdBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · show (M *ᵥ planeVec k y) (Sum.inr k) = _
    rw [mulVec_planeVec_inr]
    simp [stdBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem mat2_eq_of_mulVec_eq {M N : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ y : Fin 2 → F, M *ᵥ y = N *ᵥ y) : M = N := by
  have : Matrix.toLin' M = Matrix.toLin' N := LinearMap.ext h
  exact Matrix.toLin'.injective this

private theorem mat4_eq_of_mulVec_eq {M N : Mat4 F} (h : ∀ y : Fin 2 ⊕ Fin 2 → F, M *ᵥ y = N *ᵥ y) :
    M = N := by
  have : Matrix.toLin' M = Matrix.toLin' N := LinearMap.ext h
  exact Matrix.toLin'.injective this


private theorem block_mul_inv {A B : Mat4 F} (hAB : A * B = 1) (k : Fin 2)
    (hA : ∀ v, IsPlaneVec k v → IsPlaneVec k (A *ᵥ v))
    (hB : ∀ v, IsPlaneVec k v → IsPlaneVec k (B *ᵥ v)) :
    stdBlock k A * stdBlock k B = 1 := by
  refine mat2_eq_of_mulVec_eq fun y => ?_
  apply planeVec_injective k
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← mulVec_planeVec_of_preserves k hA,
    ← mulVec_planeVec_of_preserves k hB, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

private theorem block_conj_relation {A B : Mat4 F}
    (hA : ∀ v, IsPlaneVec 1 v → IsPlaneVec 1 (A *ᵥ v))
    (hB : ∀ v, IsPlaneVec 1 v → IsPlaneVec 1 (B *ᵥ v)) {S S' : Matrix (Fin 2) (Fin 2) F}
    (h : A * blockMat (Sum.inl 1) (Sum.inr 1) S * B = blockMat (Sum.inl 1) (Sum.inr 1) S') :
    stdBlock 1 A * S * stdBlock 1 B = S' := by
  refine mat2_eq_of_mulVec_eq fun y => ?_
  apply planeVec_injective 1
  calc planeVec 1 ((stdBlock 1 A * S * stdBlock 1 B) *ᵥ y)
      = planeVec 1 (stdBlock 1 A *ᵥ (S *ᵥ (stdBlock 1 B *ᵥ y))) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = A *ᵥ planeVec 1 (S *ᵥ (stdBlock 1 B *ᵥ y)) := by
        rw [mulVec_planeVec_of_preserves 1 hA]
    _ = A *ᵥ ((blockMat (Sum.inl 1) (Sum.inr 1) S : Mat4 F) *ᵥ planeVec 1 (stdBlock 1 B *ᵥ y)) := by
        rw [mulVec_blockMat_planeVec]
    _ = A *ᵥ ((blockMat (Sum.inl 1) (Sum.inr 1) S : Mat4 F) *ᵥ (B *ᵥ planeVec 1 y)) := by
        rw [mulVec_planeVec_of_preserves 1 hB]
    _ = (A * blockMat (Sum.inl 1) (Sum.inr 1) S * B) *ᵥ planeVec 1 y := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = planeVec 1 (S' *ᵥ y) := by rw [h, mulVec_blockMat_planeVec]

private theorem map_fin_two (σ : F ≃+* F) (a b c d : F) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F).map σ = !![σ a, σ b; σ c, σ d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem scalar_of_twisted {C : Matrix (Fin 2) (Fin 2) F} (hC : IsUnit C.det) (σ : F ≃+* F)
    (h : ∀ t : SL(2, F), C * (t : Matrix (Fin 2) (Fin 2) F).map σ =
      (t : Matrix (Fin 2) (Fin 2) F) * C) :
    (∀ x, σ x = x) ∧ ∃ a : F, a ≠ 0 ∧ C = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c00, c01, c10, c11, rfl⟩ : ∃ c00 c01 c10 c11 : F, C = !![c00, c01; c10, c11] :=
    ⟨C 0 0, C 0 1, C 1 0, C 1 1, Matrix.eta_fin_two C⟩
  have hup : ∀ x : F, c10 * x = 0 ∧ c00 * σ x = x * c11 := fun x => by
    have := h (sl2Upper x)
    rw [CFSG.LieType.Steinberg.coe_sl2Upper, map_fin_two] at this
    simp only [map_one, map_zero, Matrix.mul_fin_two] at this
    have e1 := congrFun (congrFun this 0) 0
    have e2 := congrFun (congrFun this 0) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e2
    refine ⟨by linear_combination -e1, by linear_combination e2⟩
  have hlo : ∀ x : F, c01 * σ x = 0 := fun x => by
    have := h (sl2Lower x)
    rw [CFSG.LieType.Steinberg.coe_sl2Lower, map_fin_two] at this
    simp only [map_one, map_zero, Matrix.mul_fin_two] at this
    have e1 := congrFun (congrFun this 0) 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one] at e1
    linear_combination e1
  have h10 : c10 = 0 := by simpa using (hup 1).1
  have h01 : c01 = 0 := by simpa using hlo 1
  have h00 : c00 = c11 := by simpa using (hup 1).2
  have hdet : c00 * c11 ≠ 0 := by
    have := hC
    rw [Matrix.det_fin_two_of, h10, h01] at this
    simpa using this.ne_zero
  have hc0 : c00 ≠ 0 := left_ne_zero_of_mul hdet
  refine ⟨fun x => ?_, c00, hc0, ?_⟩
  · have := (hup x).2
    rw [← h00] at this
    have := mul_left_cancel₀ hc0 (this.trans (mul_comm x c00))
    exact this
  · rw [h10, h01, ← h00]
    ext i j
    fin_cases i <;> fin_cases j <;> simp


private theorem diagConj2_coe_neg_one (s : SL(2, F)) :
    ((diagConj2 (-1) 1 s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(-1 : F), 1] * (s : Matrix (Fin 2) (Fin 2) F) *
        Matrix.diagonal ![(-1 : F), 1] := by
  rw [CFSG.ClassicalInvolution.WeakCT.coe_diagConj2]
  simp

private theorem blockA2_shape [Finite F] {A₂ B₂ : Matrix (Fin 2) (Fin 2) F} (hAB : A₂ * B₂ = 1)
    (hBA : B₂ * A₂ = 1) (σ : F ≃+* F) (γ : SL(2, F) ≃* SL(2, F))
    (h : ∀ s : SL(2, F), A₂ * ((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ * B₂ =
        ((γ (diagConj2 (-1) 1 s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :
    (∀ x, σ x = x) ∧ ∃ a : F, a ≠ 0 ∧ A₂ * A₂ = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F) ∧
      ∃ p r : Fin 2 → F, A₂ *ᵥ p = (-a) • p ∧ A₂ *ᵥ r = a • r ∧ p 0 * r 1 - p 1 * r 0 ≠ 0 := by
  obtain ⟨G, κ, hG⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map γ
  set Gm : Matrix (Fin 2) (Fin 2) F := (G : Matrix (Fin 2) (Fin 2) F) with hGm
  set Gi : Matrix (Fin 2) (Fin 2) F := ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hGi
  have hGG : Gm * Gi = 1 := G.mul_inv
  have hGG' : Gi * Gm = 1 := G.inv_mul
  have hcoe : ∀ s : SL(2, F), ((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Gm * (s : Matrix (Fin 2) (Fin 2) F).map κ * Gi := by
    intro s
    have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hG s)
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h2
    exact h2
  set Dm : Matrix (Fin 2) (Fin 2) F := Matrix.diagonal ![(-1 : F), 1] with hDm
  have hDD : Dm * Dm = 1 := by
    rw [hDm, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hDκ : Dm.map κ = Dm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hDm]
  have hmapσ : ∀ M N : Matrix (Fin 2) (Fin 2) F, (M * N).map σ = M.map σ * N.map σ :=
    fun M N => CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.map_mul_ringEquiv σ M N
  have hmapκ : ∀ M N : Matrix (Fin 2) (Fin 2) F, (M * N).map κ = M.map κ * N.map κ :=
    fun M N => CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.map_mul_ringEquiv κ M N
  have hone : ∀ τ : F ≃+* F, (1 : Matrix (Fin 2) (Fin 2) F).map τ = 1 := fun τ => by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  set Nm : Matrix (Fin 2) (Fin 2) F := A₂ * Gm.map σ with hNm
  set N' : Matrix (Fin 2) (Fin 2) F := Gi.map σ * B₂ with hN'
  have hNN : Nm * N' = 1 := by
    rw [hNm, hN', Matrix.mul_assoc, ← Matrix.mul_assoc (Gm.map σ), ← hmapσ, hGG, hone,
      Matrix.one_mul, hAB]
  have hNN' : N' * Nm = 1 := by
    rw [hNm, hN', Matrix.mul_assoc, ← Matrix.mul_assoc B₂, hBA, Matrix.one_mul, ← hmapσ, hGG',
      hone]
  set P : Matrix (Fin 2) (Fin 2) F := Gm * Dm with hP
  set P' : Matrix (Fin 2) (Fin 2) F := Dm * Gi with hP'
  have hPP : P * P' = 1 := by
    calc P * P' = Gm * (Dm * Dm) * Gi := by simp only [hP, hP', Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hGG]
  have hPP' : P' * P = 1 := by
    calc P' * P = Dm * (Gi * Gm) * Dm := by simp only [hP, hP', Matrix.mul_assoc]
      _ = 1 := by rw [hGG', Matrix.mul_one, hDD]
  have hsurj : ∀ t : SL(2, F), ∃ s : SL(2, F),
      (s : Matrix (Fin 2) (Fin 2) F).map κ = (t : Matrix (Fin 2) (Fin 2) F) := by
    intro t
    refine ⟨Matrix.SpecialLinearGroup.map (κ.symm : F →+* F) t, ?_⟩
    ext i j
    simp
  have hmain : ∀ t : SL(2, F), Nm * (t : Matrix (Fin 2) (Fin 2) F).map σ * N' = P * t * P' := by
    intro t
    obtain ⟨s, hs⟩ := hsurj t
    have e := h s
    rw [hcoe s, hcoe (diagConj2 (-1) 1 s), diagConj2_coe_neg_one, hmapσ, hmapσ, hs] at e
    rw [hmapκ, hmapκ, hDκ, hs] at e
    rw [hNm, hN', hP, hP']
    calc A₂ * Gm.map σ * (t : Matrix (Fin 2) (Fin 2) F).map σ * (Gi.map σ * B₂)
        = A₂ * (Gm.map σ * (t : Matrix (Fin 2) (Fin 2) F).map σ * Gi.map σ) * B₂ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e]; simp only [Matrix.mul_assoc]
  have hC : IsUnit (P' * Nm).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.mul ⟨⟨P', P, hPP', hPP⟩, rfl⟩ ⟨⟨Nm, N', hNN, hNN'⟩, rfl⟩
  have hcomm : ∀ t : SL(2, F),
      (P' * Nm) * (t : Matrix (Fin 2) (Fin 2) F).map σ =
        (t : Matrix (Fin 2) (Fin 2) F) * (P' * Nm) := by
    intro t
    have e := hmain t
    calc P' * Nm * (t : Matrix (Fin 2) (Fin 2) F).map σ
        = P' * (Nm * (t : Matrix (Fin 2) (Fin 2) F).map σ * N' * Nm) := by
          rw [Matrix.mul_assoc (Nm * (t : Matrix (Fin 2) (Fin 2) F).map σ) N' Nm, hNN',
            Matrix.mul_one, Matrix.mul_assoc]
      _ = P' * (P * t * P' * Nm) := by rw [e]
      _ = (t : Matrix (Fin 2) (Fin 2) F) * (P' * Nm) := by
          calc P' * (P * (t : Matrix (Fin 2) (Fin 2) F) * P' * Nm)
              = (P' * P) * (t : Matrix (Fin 2) (Fin 2) F) * (P' * Nm) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [hPP', Matrix.one_mul]
  obtain ⟨hσ, a, ha, hCa⟩ := scalar_of_twisted hC σ hcomm
  refine ⟨hσ, a, ha, ?_⟩
  have hmapid : ∀ M : Matrix (Fin 2) (Fin 2) F, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hA₂ : A₂ = a • (Gm * Dm * Gi) := by
    have h1 : Dm * Gi * A₂ * Gm = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
      have := hCa
      rw [hNm, hmapid] at this
      simpa only [hP', Matrix.mul_assoc] using this
    have h2 : Gi * A₂ * Gm = a • Dm := by
      calc Gi * A₂ * Gm = (Dm * Dm) * (Gi * A₂ * Gm) := by rw [hDD, Matrix.one_mul]
        _ = Dm * (Dm * Gi * A₂ * Gm) := by simp only [Matrix.mul_assoc]
        _ = a • Dm := by rw [h1]; simp
    calc A₂ = (Gm * Gi) * A₂ * (Gm * Gi) := by rw [hGG, Matrix.one_mul, Matrix.mul_one]
      _ = Gm * (Gi * A₂ * Gm) * Gi := by simp only [Matrix.mul_assoc]
      _ = a • (Gm * Dm * Gi) := by
        rw [h2]
        simp [Matrix.mul_assoc]
  have hDe0 : Dm *ᵥ ![1, 0] = (-1 : F) • ![1, 0] := by
    ext i
    fin_cases i <;> simp [hDm, Matrix.mulVec_diagonal]
  have hDe1 : Dm *ᵥ ![0, 1] = (1 : F) • ![0, 1] := by
    ext i
    fin_cases i <;> simp [hDm, Matrix.mulVec_diagonal]
  have hAG : A₂ * Gm = a • (Gm * Dm) := by
    rw [hA₂, Matrix.smul_mul]
    congr 1
    calc Gm * Dm * Gi * Gm = Gm * Dm * (Gi * Gm) := by rw [Matrix.mul_assoc]
      _ = Gm * Dm := by rw [hGG', Matrix.mul_one]
  refine ⟨?_, Gm *ᵥ ![1, 0], Gm *ᵥ ![0, 1], ?_, ?_, ?_⟩
  · rw [hA₂]
    calc (a • (Gm * Dm * Gi)) * (a • (Gm * Dm * Gi)) = a ^ 2 • (Gm * (Dm * Dm) * Gi) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
          congr 1
          calc Gm * Dm * Gi * (Gm * Dm * Gi) = Gm * Dm * (Gi * Gm) * Dm * Gi := by
                simp only [Matrix.mul_assoc]
            _ = Gm * (Dm * Dm) * Gi := by rw [hGG', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = a ^ 2 • 1 := by rw [hDD, Matrix.mul_one, hGG]
  · rw [Matrix.mulVec_mulVec, hAG, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hDe0,
      Matrix.mulVec_smul, smul_smul, mul_neg_one]
  · rw [Matrix.mulVec_mulVec, hAG, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hDe1,
      Matrix.mulVec_smul, smul_smul, mul_one]
  · have hdet : Gm.det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det Gm).1 ⟨⟨Gm, Gi, hGG, hGG'⟩, rfl⟩
      exact this.ne_zero
    rw [Matrix.det_fin_two] at hdet
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    intro hh
    apply hdet
    linear_combination hh


private theorem form_planeVec (k : Fin 2) (x y : Fin 2 → F) :
    form (planeVec k x) (planeVec k y) = x 0 * y 1 - x 1 * y 0 := by
  rw [form_apply4]
  fin_cases k <;> simp [planeVec]

private theorem form_eq_zero_of_planes {u v : Fin 2 ⊕ Fin 2 → F} (hu : IsPlaneVec 0 u)
    (hv : IsPlaneVec 1 v) : form u v = 0 := by
  refine form_eq_zero_of_supp (S := coords 1) (parClosed_coords 1) (fun a ha => hu a ?_)
    (fun a ha => hv a ha)
  intro h0
  rw [mem_coords] at ha h0
  rcases ha with rfl | rfl <;> simp_all

private theorem planeVec_smul (k : Fin 2) (c : F) (y : Fin 2 → F) :
    planeVec k (c • y) = c • planeVec k y := by
  funext a
  simp only [planeVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem planeVec_add (k : Fin 2) (x y : Fin 2 → F) :
    planeVec k (x + y) = planeVec k x + planeVec k y := by
  funext a
  simp only [planeVec, Pi.add_apply]
  split_ifs <;> simp


private theorem eq_of_mulVec_carried {P Q : Mat4 F} {g : StatedSp 2 F}
    {u₁ w₁ u₂ w₂ : Fin 2 ⊕ Fin 2 → F} (hg : CarriesFrame g u₁ w₁ u₂ w₂)
    (h1 : P *ᵥ u₁ = Q *ᵥ u₁) (h2 : P *ᵥ w₁ = Q *ᵥ w₁) (h3 : P *ᵥ u₂ = Q *ᵥ u₂)
    (h4 : P *ᵥ w₂ = Q *ᵥ w₂) : P = Q := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  have key : P * mat 2 F g = Q * mat 2 F g := by
    ext i b
    have e : ∀ M : Mat4 F, M i b = (M *ᵥ Pi.single b 1) i := fun M =>
      (mulVec_single_one_apply M b i).symm
    rw [e (P * mat 2 F g), e (Q * mat 2 F g), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rcases b with b | b <;> fin_cases b
    · have := h1
      rw [← g1] at this
      exact congrFun this i
    · have := h3
      rw [← g3] at this
      exact congrFun this i
    · have := h2
      rw [← g2] at this
      exact congrFun this i
    · have := h4
      rw [← g4] at this
      exact congrFun this i
  have hgi : mat 2 F g * mat 2 F g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc P = P * (mat 2 F g * mat 2 F g⁻¹) := by rw [hgi, Matrix.mul_one]
    _ = Q * (mat 2 F g * mat 2 F g⁻¹) := by rw [← Matrix.mul_assoc, key, Matrix.mul_assoc]
    _ = Q := by rw [hgi, Matrix.mul_one]

private theorem frame_commutes {Am : Mat4 F} {a : F} {u₁ w₁ u₂ w₂ : Fin 2 ⊕ Fin 2 → F}
    {g : StatedSp 2 F} (hg : CarriesFrame g u₁ w₁ u₂ w₂)
    (hu₁ : Am *ᵥ u₁ = a • u₁) (hw₁ : Am *ᵥ w₁ = (-a) • w₁) (hu₂ : Am *ᵥ u₂ = a • u₂)
    (hw₂ : Am *ᵥ w₂ = (-a) • w₂) (h01 : (0 : Fin 2) ≠ 1) (s : SL(2, F)) :
    Am * mat 2 F (g * shortBlock F h01 s * g⁻¹) = mat 2 F (g * shortBlock F h01 s * g⁻¹) * Am := by
  obtain ⟨c1, c2, c3, c4⟩ := hg.mulVec_conj_shortBlock s
  set X : Mat4 F := mat 2 F (g * shortBlock F h01 s * g⁻¹) with hX
  have c1' : X *ᵥ u₁ = (s : Matrix (Fin 2) (Fin 2) F) 0 0 • u₁ +
      (s : Matrix (Fin 2) (Fin 2) F) 1 0 • u₂ := c1
  have c2' : X *ᵥ u₂ = (s : Matrix (Fin 2) (Fin 2) F) 0 1 • u₁ +
      (s : Matrix (Fin 2) (Fin 2) F) 1 1 • u₂ := c2
  have c3' : X *ᵥ w₁ = ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 • w₁ +
      ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 • w₂ := c3
  have c4' : X *ᵥ w₂ = ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 • w₁ +
      ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 • w₂ := c4
  refine eq_of_mulVec_carried hg ?_ ?_ ?_ ?_
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c1', hu₁, Matrix.mulVec_smul, c1',
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hu₁, hu₂]
    module
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c3', hw₁, Matrix.mulVec_smul, c3',
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hw₁, hw₂]
    module
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c2', hu₂, Matrix.mulVec_smul, c2',
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hu₁, hu₂]
    module
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c4', hw₂, Matrix.mulVec_smul, c4',
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hw₁, hw₂]
    module


private theorem exists_smul_of_det_eq_zero {p r : Fin 2 → F} (hp : p ≠ 0)
    (h : p 0 * r 1 - p 1 * r 0 = 0) : ∃ l : F, r = l • p := by
  by_cases h0 : p 0 = 0
  · have h1 : p 1 ≠ 0 := fun h1 => hp (by
      funext i
      fin_cases i <;> simp [h0, h1])
    have hr0 : r 0 = 0 := by
      rw [h0] at h
      have : p 1 * r 0 = 0 := by linear_combination -h
      exact (mul_eq_zero.1 this).resolve_left h1
    refine ⟨r 1 / p 1, ?_⟩
    funext i
    fin_cases i
    · simp [hr0, h0]
    · simp [h1]
  · refine ⟨r 0 / p 0, ?_⟩
    funext i
    fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

private theorem exists_eigenpair {B : Matrix (Fin 2) (Fin 2) F} {a : F} (h2 : (2 : F) ≠ 0)
    (ha : a ≠ 0)
    (hsq : B * B = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F)) (hdet : B.det = -a ^ 2) :
    ∃ p r : Fin 2 → F, B *ᵥ p = (-a) • p ∧ B *ᵥ r = a • r ∧ p 0 * r 1 - p 1 * r 0 ≠ 0 := by
  set Pp : Matrix (Fin 2) (Fin 2) F := B + a • 1 with hPp
  set Pm : Matrix (Fin 2) (Fin 2) F := B - a • 1 with hPm
  have hmp : Pm * Pp = 0 := by
    have : Pm * Pp = B * B - a ^ 2 • 1 := by
      rw [hPm, hPp]
      simp only [sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.one_mul, smul_smul, sq]
      abel
    rw [this, hsq, sub_self]
  have hpm : Pp * Pm = 0 := by
    have : Pp * Pm = B * B - a ^ 2 • 1 := by
      rw [hPm, hPp]
      simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.one_mul, smul_smul, sq]
      abel
    rw [this, hsq, sub_self]
  have hPp0 : Pp ≠ 0 := by
    intro h0
    have hB : B = (-a) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact h0
    rw [hB, Matrix.det_smul, Matrix.det_one] at hdet
    have : (2 : F) * a ^ 2 = 0 := by simp at hdet; linear_combination hdet
    exact (mul_ne_zero h2 (pow_ne_zero 2 ha)) this
  have hPm0 : Pm ≠ 0 := by
    intro h0
    have hB : B = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [sub_eq_zero] at h0
      exact h0
    rw [hB, Matrix.det_smul, Matrix.det_one] at hdet
    have : (2 : F) * a ^ 2 = 0 := by simp at hdet; linear_combination hdet
    exact (mul_ne_zero h2 (pow_ne_zero 2 ha)) this
  obtain ⟨z, hz⟩ : ∃ z : Fin 2 → F, Pp *ᵥ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hPp0 (mat2_eq_of_mulVec_eq fun y => by rw [hcon y, Matrix.zero_mulVec])
  obtain ⟨z', hz'⟩ : ∃ z : Fin 2 → F, Pm *ᵥ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hPm0 (mat2_eq_of_mulVec_eq fun y => by rw [hcon y, Matrix.zero_mulVec])
  have hr : B *ᵥ (Pp *ᵥ z) = a • (Pp *ᵥ z) := by
    have : Pm *ᵥ (Pp *ᵥ z) = 0 := by rw [Matrix.mulVec_mulVec, hmp, Matrix.zero_mulVec]
    rw [hPm, Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this
  have hp : B *ᵥ (Pm *ᵥ z') = (-a) • (Pm *ᵥ z') := by
    have : Pp *ᵥ (Pm *ᵥ z') = 0 := by rw [Matrix.mulVec_mulVec, hpm, Matrix.zero_mulVec]
    rw [hPp, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_eq_zero_iff_eq_neg,
      ← neg_smul] at this
    exact this
  refine ⟨Pm *ᵥ z', Pp *ᵥ z, hp, hr, fun hd => ?_⟩
  obtain ⟨l, hl⟩ := exists_smul_of_det_eq_zero hz' hd
  have h3 : B *ᵥ (Pp *ᵥ z) = (-(a * l)) • (Pm *ᵥ z') := by
    rw [hl, Matrix.mulVec_smul, hp]
    module
  rw [hr, hl] at h3
  have h4 : (2 * a * l) • (Pm *ᵥ z') = 0 := by
    have h5 := sub_eq_zero.2 h3
    convert h5 using 1
    module
  have h6 : 2 * a * l = 0 := (smul_eq_zero.1 h4).resolve_right hz'
  have hl0 : l = 0 := by
    have : (2 * a) * l = 0 := h6
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 ha)
  exact hz (by rw [hl, hl0, zero_smul])


private theorem single_inl_eq_planeVec (k : Fin 2) :
    (Pi.single (Sum.inl k) (1 : F) : Fin 2 ⊕ Fin 2 → F) = planeVec k ![1, 0] := by
  funext a
  rcases a with a | a
  · by_cases h : a = k <;> simp [planeVec, h]
  · simp [planeVec]

private theorem single_inr_eq_planeVec (k : Fin 2) :
    (Pi.single (Sum.inr k) (1 : F) : Fin 2 ⊕ Fin 2 → F) = planeVec k ![0, 1] := by
  funext a
  rcases a with a | a
  · simp [planeVec]
  · by_cases h : a = k <;> simp [planeVec, h]

private theorem mat4_eq_of_basis {M N : Mat4 F}
    (h : ∀ j : Fin 2 ⊕ Fin 2, M *ᵥ Pi.single j 1 = N *ᵥ Pi.single j 1) : M = N := by
  ext i j
  have := congrFun (h j) i
  rwa [mulVec_single_one_apply, mulVec_single_one_apply] at this

private theorem Asq_eq {Am : Mat4 F} {a : F}
    (hA1 : ∀ v, IsPlaneVec 1 v → IsPlaneVec 1 (Am *ᵥ v))
    (hA₂sq : stdBlock 1 Am * stdBlock 1 Am = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F))
    (hcomm : ∀ x : StatedSp 2 F, (Am * Am) * mat 2 F x = mat 2 F x * (Am * Am))
    (h01 : (0 : Fin 2) ≠ 1) : Am * Am = a ^ 2 • (1 : Mat4 F) := by
  have hpl1 : ∀ y : Fin 2 → F, (Am * Am) *ᵥ planeVec 1 y = a ^ 2 • planeVec 1 y := by
    intro y
    rw [← Matrix.mulVec_mulVec, mulVec_planeVec_of_preserves 1 hA1,
      mulVec_planeVec_of_preserves 1 hA1, Matrix.mulVec_mulVec, hA₂sq, Matrix.smul_mulVec,
      Matrix.one_mulVec, planeVec_smul]
  have he1 : (Am * Am) *ᵥ (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) =
      a ^ 2 • Pi.single (Sum.inl 1) 1 := by
    rw [single_inl_eq_planeVec]; exact hpl1 _
  have hf1 : (Am * Am) *ᵥ (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F) =
      a ^ 2 • Pi.single (Sum.inr 1) 1 := by
    rw [single_inr_eq_planeVec]; exact hpl1 _
  have he0 : (Am * Am) *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) =
      a ^ 2 • Pi.single (Sum.inl 0) 1 := by
    have hX : mat 2 F (shortBlock F h01 (sl2Upper 1)) *ᵥ
        (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) =
        Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inl 1) 1 := by
      rw [shortBlock_mulVec_inl_right]
      simp [sl2Upper_one_coe]
    have key : (Am * Am) *ᵥ (mat 2 F (shortBlock F h01 (sl2Upper 1)) *ᵥ
        (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F)) =
        mat 2 F (shortBlock F h01 (sl2Upper 1)) *ᵥ ((Am * Am) *ᵥ
          (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]
    rw [hX, he1, Matrix.mulVec_add, Matrix.mulVec_smul, hX, he1] at key
    calc (Am * Am) *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F)
        = ((Am * Am) *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) +
            a ^ 2 • (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F)) -
          a ^ 2 • (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) := by abel
      _ = a ^ 2 • ((Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) + Pi.single (Sum.inl 1) 1) -
          a ^ 2 • (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) := by rw [key]
      _ = a ^ 2 • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) := by module
  have hf0 : (Am * Am) *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) =
      a ^ 2 • Pi.single (Sum.inr 0) 1 := by
    have hX : mat 2 F (shortBlock F h01 (sl2Lower 1)) *ᵥ
        (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F) =
        (-1 : F) • Pi.single (Sum.inr 0) 1 + Pi.single (Sum.inr 1) 1 := by
      rw [shortBlock_mulVec_inr_right]
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, sl2Lower_one_coe]
    have key : (Am * Am) *ᵥ (mat 2 F (shortBlock F h01 (sl2Lower 1)) *ᵥ
        (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F)) =
        mat 2 F (shortBlock F h01 (sl2Lower 1)) *ᵥ ((Am * Am) *ᵥ
          (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]
    rw [hX, hf1, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hX, hf1] at key
    calc (Am * Am) *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F)
        = -(((-1 : F) • (Am * Am) *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) +
            a ^ 2 • (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F)) -
          a ^ 2 • (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F)) := by module
      _ = -(a ^ 2 • ((-1 : F) • (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) +
            Pi.single (Sum.inr 1) 1) - a ^ 2 • (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F)) := by
          rw [key]
      _ = a ^ 2 • (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) := by module
  refine mat4_eq_of_basis fun j => ?_
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rcases j with j | j <;> fin_cases j
  · exact he0
  · exact he1
  · exact hf0
  · exact hf1


private theorem planeVec_eq_comb (k : Fin 2) (y : Fin 2 → F) :
    planeVec k y = y 0 • (Pi.single (Sum.inl k) 1 : Fin 2 ⊕ Fin 2 → F) +
      y 1 • (Pi.single (Sum.inr k) 1 : Fin 2 ⊕ Fin 2 → F) := by
  funext a
  rcases a with a | a
  · by_cases h : a = k <;> simp [planeVec, h]
  · by_cases h : a = k <;> simp [planeVec, h]

private theorem span_planeVec_eq_stdPlane {p r : Fin 2 → F} (hd : p 0 * r 1 - p 1 * r 0 ≠ 0)
    (k : Fin 2) :
    Submodule.span F {planeVec k r, ((-(p 0 * r 1 - p 1 * r 0))⁻¹ : F) • planeVec k p} =
      stdPlane F 2 k := by
  set d : F := p 0 * r 1 - p 1 * r 0 with hdd
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro v hv
    rcases hv with rfl | rfl
    · rw [planeVec_eq_comb]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [planeVec_eq_comb]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  · refine Submodule.span_le.2 ?_
    intro v hv
    have hdne : -d ≠ 0 := neg_ne_zero.2 hd
    rcases hv with rfl | rfl
    · rw [single_inl_eq_planeVec]
      have h : planeVec k ![1, 0] = (-(p 1 / d)) • planeVec k r +
          (-r 1) • (((-d)⁻¹ : F) • planeVec k p) := by
        rw [← planeVec_smul, ← planeVec_smul, ← planeVec_smul, ← planeVec_add]
        congr 1
        ext i
        fin_cases i
        · simp only [Fin.zero_eta, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          simp
          ring
        · simp only [Fin.mk_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          simp
      rw [h]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [single_inr_eq_planeVec]
      have h : planeVec k ![0, 1] = (p 0 / d) • planeVec k r +
          (r 0) • (((-d)⁻¹ : F) • planeVec k p) := by
        rw [← planeVec_smul, ← planeVec_smul, ← planeVec_smul, ← planeVec_add]
        congr 1
        ext i
        fin_cases i
        · simp only [Fin.zero_eta, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          simp
        · simp only [Fin.mk_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          simp
          rw [hdd]
          ring
      rw [h]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))


private theorem exists_frame_of_eigen {Am : Mat4 F} {a : F}
    (hA0 : ∀ v, IsPlaneVec 0 v → IsPlaneVec 0 (Am *ᵥ v))
    (hA1 : ∀ v, IsPlaneVec 1 v → IsPlaneVec 1 (Am *ᵥ v)) {p₁ r₁ p r : Fin 2 → F}
    (hp₁ : stdBlock 0 Am *ᵥ p₁ = (-a) • p₁) (hr₁ : stdBlock 0 Am *ᵥ r₁ = a • r₁)
    (hd₁ : p₁ 0 * r₁ 1 - p₁ 1 * r₁ 0 ≠ 0) (hp : stdBlock 1 Am *ᵥ p = (-a) • p)
    (hr : stdBlock 1 Am *ᵥ r = a • r) (hd : p 0 * r 1 - p 1 * r 0 ≠ 0) (h01 : (0 : Fin 2) ≠ 1) :
    ∃ g : StatedSp 2 F, (longBlock F 2 1).range.map (MulAut.conj g).toMonoidHom =
        (longBlock F 2 1).range ∧
      ∀ s : SL(2, F), Am * mat 2 F (g * shortBlock F h01 s * g⁻¹) =
        mat 2 F (g * shortBlock F h01 s * g⁻¹) * Am := by
  set d₁ : F := p₁ 0 * r₁ 1 - p₁ 1 * r₁ 0 with hd₁def
  set d₂ : F := p 0 * r 1 - p 1 * r 0 with hd₂def
  have hn₁ : (-d₁)⁻¹ * (-d₁) = 1 := inv_mul_cancel₀ (neg_ne_zero.2 hd₁)
  have hn₂ : (-d₂)⁻¹ * (-d₂) = 1 := inv_mul_cancel₀ (neg_ne_zero.2 hd)
  set u₁ : Fin 2 ⊕ Fin 2 → F := planeVec 0 r₁ with hu₁def
  set w₁ : Fin 2 ⊕ Fin 2 → F := ((-d₁)⁻¹ : F) • planeVec 0 p₁ with hw₁def
  set u₂ : Fin 2 ⊕ Fin 2 → F := planeVec 1 r with hu₂def
  set w₂ : Fin 2 ⊕ Fin 2 → F := ((-d₂)⁻¹ : F) • planeVec 1 p with hw₂def
  have f1 : form u₁ w₁ = 1 := by
    rw [hu₁def, hw₁def, form_smul_right, form_planeVec]
    have : r₁ 0 * p₁ 1 - r₁ 1 * p₁ 0 = -d₁ := by rw [hd₁def]; ring
    rw [this, hn₁]
  have f2 : form u₂ w₂ = 1 := by
    rw [hu₂def, hw₂def, form_smul_right, form_planeVec]
    have : r 0 * p 1 - r 1 * p 0 = -d₂ := by rw [hd₂def]; ring
    rw [this, hn₂]
  have o1 : form u₁ u₂ = 0 :=
    form_eq_zero_of_planes (isPlaneVec_planeVec 0 _) (isPlaneVec_planeVec 1 _)
  have o2 : form u₁ w₂ = 0 := by
    rw [hw₂def, form_smul_right, form_eq_zero_of_planes (isPlaneVec_planeVec 0 _)
      (isPlaneVec_planeVec 1 _), mul_zero]
  have o3 : form w₁ u₂ = 0 := by
    rw [hw₁def, form_smul_left, form_eq_zero_of_planes (isPlaneVec_planeVec 0 _)
      (isPlaneVec_planeVec 1 _), mul_zero]
  have o4 : form w₁ w₂ = 0 := by
    rw [hw₁def, hw₂def, form_smul_left, form_smul_right, form_eq_zero_of_planes
      (isPlaneVec_planeVec 0 _) (isPlaneVec_planeVec 1 _), mul_zero, mul_zero]
  have hq : IsSymplecticFrame (K := F) (m := 0) u₁ w₁ u₂ w₂ := ⟨f1, f2, o1, o2, o3, o4⟩
  obtain ⟨g, hg⟩ := hq.exists_carries
  have hu₁ : Am *ᵥ u₁ = a • u₁ := by
    rw [hu₁def, mulVec_planeVec_of_preserves 0 hA0, hr₁, planeVec_smul]
  have hw₁ : Am *ᵥ w₁ = (-a) • w₁ := by
    rw [hw₁def, Matrix.mulVec_smul, mulVec_planeVec_of_preserves 0 hA0, hp₁, planeVec_smul]
    module
  have hu₂ : Am *ᵥ u₂ = a • u₂ := by
    rw [hu₂def, mulVec_planeVec_of_preserves 1 hA1, hr, planeVec_smul]
  have hw₂ : Am *ᵥ w₂ = (-a) • w₂ := by
    rw [hw₂def, Matrix.mulVec_smul, mulVec_planeVec_of_preserves 1 hA1, hp, planeVec_smul]
    module
  refine ⟨g, ?_, fun s => frame_commutes hg hu₁ hw₁ hu₂ hw₂ h01 s⟩
  have h := hg.planeGroup_pair_two
  have hspan : Submodule.span F {u₂, w₂} = stdPlane F 2 1 := span_planeVec_eq_stdPlane hd 1
  rw [hspan, planeGroup_stdPlane] at h
  exact h.symm


private theorem m_eq_neg_sq {Am : Mat4 F} {m a : F}
    (hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = m * form u v)
    (hA1 : ∀ v, IsPlaneVec 1 v → IsPlaneVec 1 (Am *ᵥ v)) {p r : Fin 2 → F}
    (hp : stdBlock 1 Am *ᵥ p = (-a) • p) (hr : stdBlock 1 Am *ᵥ r = a • r)
    (hd : p 0 * r 1 - p 1 * r 0 ≠ 0) : m = -a ^ 2 := by
  have h := hsim (planeVec 1 p) (planeVec 1 r)
  rw [mulVec_planeVec_of_preserves 1 hA1, mulVec_planeVec_of_preserves 1 hA1, hp, hr,
    planeVec_smul, planeVec_smul, form_smul_left, form_smul_right, form_planeVec] at h
  exact mul_right_cancel₀ hd (by linear_combination -h)

private theorem det_stdBlock_zero {Am : Mat4 F} {m : F}
    (hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = m * form u v)
    (hA0 : ∀ v, IsPlaneVec 0 v → IsPlaneVec 0 (Am *ᵥ v)) : (stdBlock 0 Am).det = m := by
  have h := hsim (planeVec 0 ![1, 0]) (planeVec 0 ![0, 1])
  rw [mulVec_planeVec_of_preserves 0 hA0, mulVec_planeVec_of_preserves 0 hA0, form_planeVec,
    form_planeVec] at h
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] at h ⊢
  linear_combination h

private theorem stdBlock_zero_sq {Am : Mat4 F} {a : F}
    (hA0 : ∀ v, IsPlaneVec 0 v → IsPlaneVec 0 (Am *ᵥ v))
    (hAsq : Am * Am = a ^ 2 • (1 : Mat4 F)) :
    stdBlock 0 Am * stdBlock 0 Am = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  refine mat2_eq_of_mulVec_eq fun y => ?_
  apply planeVec_injective 0
  rw [← Matrix.mulVec_mulVec, ← mulVec_planeVec_of_preserves 0 hA0,
    ← mulVec_planeVec_of_preserves 0 hA0, Matrix.mulVec_mulVec, hAsq, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, planeVec_smul]


theorem core_mat [Finite F] (h2 : (2 : F) ≠ 0) {Am Bm : Mat4 F} (hAB : Am * Bm = 1)
    (hBA : Bm * Am = 1) (σ : F ≃+* F) {m : F} (hm : m ≠ 0)
    (hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = m * form u v) (γ : SL(2, F) ≃* SL(2, F))
    (hγ : ∀ s : SL(2, F), Am * blockMat (Sum.inl 1) (Sum.inr 1)
        (((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ) * Bm =
      blockMat (Sum.inl 1) (Sum.inr 1)
        ((γ (diagConj2 (-1) 1 s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))
    (hρ : ∀ x : StatedSp 2 F, Am * (Am * (mat 2 F x).map σ * Bm).map σ * Bm = mat 2 F x)
    (h01 : (0 : Fin 2) ≠ 1) :
    (∀ x, σ x = x) ∧ ∃ g : StatedSp 2 F, (longBlock F 2 1).range.map (MulAut.conj g).toMonoidHom =
        (longBlock F 2 1).range ∧
      ∀ s : SL(2, F), Am * mat 2 F (g * shortBlock F h01 s * g⁻¹) =
        mat 2 F (g * shortBlock F h01 s * g⁻¹) * Am := by
  have hL : ∀ s : SL(2, F), ∃ s' : SL(2, F),
      Am * blockMat (Sum.inl 1) (Sum.inr 1) ((s : Matrix (Fin 2) (Fin 2) F).map σ) * Bm =
        blockMat (Sum.inl 1) (Sum.inr 1) (s' : Matrix (Fin 2) (Fin 2) F) := fun s => by
    refine ⟨γ (diagConj2 (-1) 1 (γ.symm s)), ?_⟩
    have := hγ (γ.symm s)
    rwa [MulEquiv.apply_symm_apply] at this
  have hL' : ∀ s' : SL(2, F), ∃ s : SL(2, F),
      Am * blockMat (Sum.inl 1) (Sum.inr 1) ((s : Matrix (Fin 2) (Fin 2) F).map σ) * Bm =
        blockMat (Sum.inl 1) (Sum.inr 1) (s' : Matrix (Fin 2) (Fin 2) F) := fun s' => by
    refine ⟨γ ((diagConj2 (-1) 1).symm (γ.symm s')), ?_⟩
    have := hγ ((diagConj2 (-1) 1).symm (γ.symm s'))
    rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  obtain ⟨hA0, hB0, hA1, hB1⟩ := planes_preserved hAB hBA σ hm hsim hL hL'
  have hA₂B₂ := block_mul_inv hAB 1 hA1 hB1
  have hB₂A₂ := block_mul_inv hBA 1 hB1 hA1
  have h₂ : ∀ s : SL(2, F), stdBlock 1 Am * ((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ *
      stdBlock 1 Bm = ((γ (diagConj2 (-1) 1 s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) :=
    fun s => block_conj_relation hA1 hB1 (hγ s)
  obtain ⟨hσ, a, ha, hA₂sq, p, r, hp, hr, hd⟩ := blockA2_shape hA₂B₂ hB₂A₂ σ γ h₂
  refine ⟨hσ, ?_⟩
  have hmeq : m = -a ^ 2 := m_eq_neg_sq hsim hA1 hp hr hd
  have hmapid : ∀ M : Mat4 F, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hcomm : ∀ x : StatedSp 2 F, (Am * Am) * mat 2 F x = mat 2 F x * (Am * Am) := by
    intro x
    have h := hρ x
    rw [hmapid, hmapid] at h
    have key : Bm * Bm * (Am * Am) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bm Am Am, hBA, Matrix.one_mul, hBA]
    calc Am * Am * mat 2 F x = Am * Am * mat 2 F x * (Bm * Bm * (Am * Am)) := by
          rw [key, Matrix.mul_one]
      _ = (Am * (Am * mat 2 F x * Bm) * Bm) * (Am * Am) := by simp only [Matrix.mul_assoc]
      _ = mat 2 F x * (Am * Am) := by rw [h]
  have hAsq := Asq_eq hA1 hA₂sq hcomm h01
  have hA₁sq := stdBlock_zero_sq hA0 hAsq
  have hA₁det : (stdBlock 0 Am).det = -a ^ 2 := by
    rw [det_stdBlock_zero hsim hA0, hmeq]
  obtain ⟨p₁, r₁, hp₁, hr₁, hd₁⟩ := exists_eigenpair h2 ha hA₁sq hA₁det
  exact exists_frame_of_eigen hA0 hA1 hp₁ hr₁ hd₁ hp hr hd h01



end CFSG.ClassicalInvolution.Q3.Q3TPS
