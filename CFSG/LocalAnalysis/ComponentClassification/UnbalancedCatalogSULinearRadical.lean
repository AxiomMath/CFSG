module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityPureGraph
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenLinearTwo

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical

namespace NonalternatingRadical

variable {K : Type} [Field K] {n : ℕ}

@[expose] def onesVec : Fin n → K := fun _ => 1

@[expose] def radicalW (i : Fin n) : Submodule K (Fin n → K) :=
  LinearMap.BilinForm.orthogonal (Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K))
    (Submodule.span K {onesVec, Pi.single i 1})

theorem toBilin'_one_apply (x y : Fin n → K) :
    Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K) x y = x ⬝ᵥ y := by
  rw [Matrix.toBilin'_apply', one_mulVec]

theorem mem_radicalW {i : Fin n} {w : Fin n → K} :
    w ∈ radicalW i ↔ onesVec ⬝ᵥ w = 0 ∧ w i = 0 := by
  rw [radicalW, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · have := hw onesVec (Submodule.subset_span (by simp))
      rwa [toBilin'_one_apply] at this
    · have := hw (Pi.single i 1) (Submodule.subset_span (by simp))
      rwa [toBilin'_one_apply, single_one_dotProduct] at this
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [toBilin'_one_apply, add_dotProduct, smul_dotProduct, smul_dotProduct, h1,
      single_one_dotProduct, h2, smul_zero, smul_zero, add_zero]

theorem onesVec_apply (j : Fin n) : (onesVec : Fin n → K) j = 1 := rfl

theorem onesVec_dotProduct_single (i : Fin n) :
    (onesVec : Fin n → K) ⬝ᵥ Pi.single i 1 = 1 := by
  rw [dotProduct_single_one, onesVec_apply]

theorem onesVec_dotProduct_onesVec [CharP K 2] (hn : Even n) :
    (onesVec : Fin n → K) ⬝ᵥ onesVec = 0 := by
  obtain ⟨m, rfl⟩ := hn
  simp only [dotProduct, onesVec, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Nat.cast_add, ← two_mul, CharTwo.two_eq_zero, zero_mul]

theorem dotProduct_self_eq_sq [CharP K 2] (x : Fin n → K) :
    x ⬝ᵥ x = (onesVec ⬝ᵥ x) ^ 2 := by
  simp only [dotProduct, onesVec, one_mul]
  rw [sum_pow_char]
  simp only [sq]

theorem decomp_mem_radicalW [CharP K 2] (hn : Even n) (i : Fin n) (x : Fin n → K) :
    x - (x i - onesVec ⬝ᵥ x) • onesVec - (onesVec ⬝ᵥ x) • Pi.single i 1 ∈ radicalW i := by
  rw [mem_radicalW]
  constructor
  · rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      onesVec_dotProduct_onesVec hn, onesVec_dotProduct_single, smul_eq_mul, smul_eq_mul]
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, onesVec_apply, Pi.single_eq_same]
    ring

theorem eq_decomp (i : Fin n) (x : Fin n → K) :
    x = (x i - onesVec ⬝ᵥ x) • onesVec +
      (x - (x i - onesVec ⬝ᵥ x) • onesVec - (onesVec ⬝ᵥ x) • Pi.single i 1) +
        (onesVec ⬝ᵥ x) • Pi.single i 1 := by
  abel

theorem decomp_unique [CharP K 2] (hn : Even n) {i : Fin n} {a b a' b' : K}
    {w w' : Fin n → K} (hw : w ∈ radicalW i) (hw' : w' ∈ radicalW i)
    (h : a • onesVec + w + b • Pi.single i 1 = a' • onesVec + w' + b' • Pi.single i 1) :
    a = a' ∧ w = w' ∧ b = b' := by
  rw [mem_radicalW] at hw hw'
  have hd := congrArg (onesVec ⬝ᵥ ·) h
  simp only [dotProduct_add, dotProduct_smul, onesVec_dotProduct_onesVec hn,
    onesVec_dotProduct_single, hw.1, hw'.1, smul_eq_mul] at hd
  have hb : b = b' := by linear_combination hd
  have he := congrFun h i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec_apply, Pi.single_eq_same, hw.2,
    hw'.2] at he
  have ha : a = a' := by linear_combination he - hd
  subst ha hb
  exact ⟨rfl, add_left_cancel (add_right_cancel h), rfl⟩

theorem existsUnique_decomp [CharP K 2] (hn : Even n) (i : Fin n) (x : Fin n → K) :
    ∃! p : K × radicalW i × K,
      x = p.1 • onesVec + p.2.1.1 + p.2.2 • Pi.single i 1 := by
  refine ⟨⟨x i - onesVec ⬝ᵥ x, ⟨_, decomp_mem_radicalW hn i x⟩, onesVec ⬝ᵥ x⟩,
    eq_decomp i x, ?_⟩
  rintro ⟨a, w, b⟩ hp
  obtain ⟨h1, h2, h3⟩ := decomp_unique hn w.2 (decomp_mem_radicalW hn i x)
    (hp.symm.trans (eq_decomp i x))
  exact Prod.ext h1 (Prod.ext (Subtype.ext h2) h3)

theorem radicalW_isAlt [CharP K 2] (i : Fin n) :
    ((Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).restrict (radicalW i)).IsAlt :=
  fun w => by
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, toBilin'_one_apply,
      dotProduct_self_eq_sq, (mem_radicalW.mp w.2).1, zero_pow two_ne_zero]

theorem radicalW_nondegenerate [CharP K 2] (hn : Even n) (i : Fin n) :
    ((Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).restrict (radicalW i)).Nondegenerate := by
  have key : ∀ w : radicalW (K := K) i, (∀ w' : radicalW (K := K) i, w.1 ⬝ᵥ w'.1 = 0) →
      w = 0 := by
    intro w hw
    apply Subtype.ext
    obtain ⟨hw1, hw2⟩ := mem_radicalW.mp w.2
    have hx : ∀ x : Fin n → K, w.1 ⬝ᵥ x = 0 := by
      intro x
      conv_lhs => rw [eq_decomp i x]
      rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
        dotProduct_comm _ onesVec, hw1, dotProduct_single_one, hw2, smul_zero, smul_zero,
        add_zero, zero_add]
      exact hw ⟨_, decomp_mem_radicalW hn i x⟩
    funext j
    have := hx (Pi.single j 1)
    rwa [dotProduct_single_one] at this
  refine ⟨fun w hw => key w fun w' => ?_, fun w hw => key w fun w' => ?_⟩
  · have := hw w'
    rwa [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      toBilin'_one_apply] at this
  · have := hw w'
    rwa [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, toBilin'_one_apply,
      dotProduct_comm] at this

@[expose] def radicalMatrix (v : Fin n → K) (c : K) : Matrix (Fin n) (Fin n) K :=
  1 + vecMulVec onesVec v + vecMulVec v onesVec + c • vecMulVec onesVec onesVec

theorem radicalMatrix_mulVec (v : Fin n → K) (c : K) (x : Fin n → K) :
    radicalMatrix v c *ᵥ x =
      x + (v ⬝ᵥ x) • onesVec + (onesVec ⬝ᵥ x) • v + (c * (onesVec ⬝ᵥ x)) • onesVec := by
  simp only [radicalMatrix, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]

theorem radicalMatrix_zero : radicalMatrix (0 : Fin n → K) 0 = 1 := by
  simp [radicalMatrix]

theorem radicalMatrix_mul {v v' : Fin n → K} (c c' : K)
    (hdd : (onesVec : Fin n → K) ⬝ᵥ onesVec = 0) (hv : onesVec ⬝ᵥ v = 0)
    (hv' : onesVec ⬝ᵥ v' = 0) :
    radicalMatrix v c * radicalMatrix v' c' = radicalMatrix (v + v') (c + c' + v ⬝ᵥ v') := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, radicalMatrix_mulVec, radicalMatrix_mulVec, radicalMatrix_mulVec]
  have hvd : v ⬝ᵥ onesVec = 0 := by rw [dotProduct_comm, hv]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hvd, hdd, hv', add_dotProduct,
    mul_zero, add_zero]
  module

theorem radicalMatrix_transpose (v : Fin n → K) (c : K) :
    (radicalMatrix v c)ᵀ = radicalMatrix v c := by
  simp only [radicalMatrix, transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]
  abel

theorem radicalMatrix_mul_self [CharP K 2] (hn : Even n) {v : Fin n → K}
    (hv : onesVec ⬝ᵥ v = 0) (c : K) : radicalMatrix v c * radicalMatrix v c = 1 := by
  have hvv : v + v = 0 := funext fun j => by
    rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
  rw [radicalMatrix_mul c c (onesVec_dotProduct_onesVec hn) hv hv, dotProduct_self_eq_sq, hv,
    zero_pow two_ne_zero, add_zero, hvv, CharTwo.add_self_eq_zero, radicalMatrix_zero]


theorem radicalMatrix_mulVec_onesVec [CharP K 2] (hn : Even n) {i : Fin n} {v : Fin n → K}
    (hv : v ∈ radicalW i) (c : K) : radicalMatrix v c *ᵥ onesVec = onesVec := by
  rw [radicalMatrix_mulVec, dotProduct_comm, (mem_radicalW.mp hv).1,
    onesVec_dotProduct_onesVec hn]
  simp

theorem radicalMatrix_mulVec_of_mem {i : Fin n} {v w : Fin n → K} (hw : w ∈ radicalW i)
    (c : K) : radicalMatrix v c *ᵥ w = w + (v ⬝ᵥ w) • onesVec := by
  rw [radicalMatrix_mulVec, (mem_radicalW.mp hw).1]
  simp

theorem radicalMatrix_mulVec_single {i : Fin n} {v : Fin n → K} (hv : v ∈ radicalW i) (c : K) :
    radicalMatrix v c *ᵥ Pi.single i 1 = Pi.single i 1 + v + c • onesVec := by
  rw [radicalMatrix_mulVec, dotProduct_single_one, (mem_radicalW.mp hv).2,
    onesVec_dotProduct_single]
  simp

theorem radicalMatrix_add_smul_onesVec [CharP K 2] (x : Fin n → K) (a c : K) :
    radicalMatrix (x + a • onesVec) c = radicalMatrix x c := by
  have h2 : ∀ M : Matrix (Fin n) (Fin n) K, M + M = 0 := fun M => by
    rw [← two_smul K M, CharTwo.two_eq_zero, zero_smul]
  simp only [radicalMatrix, vecMulVec_add, add_vecMulVec, vecMulVec_smul, smul_vecMulVec]
  calc 1 + (vecMulVec onesVec x + a • vecMulVec onesVec onesVec) +
        (vecMulVec x onesVec + a • vecMulVec onesVec onesVec) +
          c • vecMulVec (onesVec : Fin n → K) onesVec
      = 1 + vecMulVec onesVec x + vecMulVec x onesVec + c • vecMulVec onesVec onesVec +
          (a • vecMulVec (onesVec : Fin n → K) onesVec +
            a • vecMulVec (onesVec : Fin n → K) onesVec) := by abel
    _ = _ := by rw [h2, add_zero]

theorem radicalMatrix_map (φ : K →+* K) (x : Fin n → K) (c : K) :
    (radicalMatrix x c).map φ = radicalMatrix (fun j => φ (x j)) (φ c) := by
  ext a b
  simp only [radicalMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, onesVec_apply, smul_eq_mul, map_add, map_mul, map_one, Matrix.one_apply]
  split_ifs <;> simp

@[expose] def radicalSet (i : Fin n) : Set (GL (Fin n) K) :=
  {g | ∃ v ∈ radicalW i, ∃ c : K, (g : Matrix (Fin n) (Fin n) K) = radicalMatrix v c}

@[expose] def radicalGroup (i : Fin n) : Subgroup (GL (Fin n) K) :=
  Subgroup.closure (radicalSet i)

@[expose] def radicalGL [CharP K 2] (hn : Even n) {v : Fin n → K} (hv : onesVec ⬝ᵥ v = 0)
    (c : K) : GL (Fin n) K :=
  ⟨radicalMatrix v c, radicalMatrix v c, radicalMatrix_mul_self hn hv c,
    radicalMatrix_mul_self hn hv c⟩

@[expose] def radicalSubgroup [CharP K 2] (hn : Even n) (i : Fin n) : Subgroup (GL (Fin n) K) where
  carrier := radicalSet i
  mul_mem' := by
    rintro a b ⟨v, hv, c, hc⟩ ⟨v', hv', c', hc'⟩
    exact ⟨v + v', add_mem hv hv', c + c' + v ⬝ᵥ v', by
      rw [Units.val_mul, hc, hc', radicalMatrix_mul c c' (onesVec_dotProduct_onesVec hn)
        (mem_radicalW.mp hv).1 (mem_radicalW.mp hv').1]⟩
  one_mem' := ⟨0, zero_mem _, 0, by rw [Units.val_one, radicalMatrix_zero]⟩
  inv_mem' := by
    rintro a ⟨v, hv, c, hc⟩
    have haa : a * a = 1 := Units.ext (by
      rw [Units.val_mul, hc, radicalMatrix_mul_self hn (mem_radicalW.mp hv).1, Units.val_one])
    exact ⟨v, hv, c, by rw [inv_eq_of_mul_eq_one_right haa, hc]⟩

theorem radicalGroup_eq [CharP K 2] (hn : Even n) (i : Fin n) :
    radicalGroup (K := K) i = radicalSubgroup hn i :=
  le_antisymm ((Subgroup.closure_le _).mpr fun _ hg => hg) fun _ hg => Subgroup.subset_closure hg

theorem mem_radicalGroup [CharP K 2] (hn : Even n) {i : Fin n} {g : GL (Fin n) K} :
    g ∈ radicalGroup i ↔
      ∃ v ∈ radicalW i, ∃ c : K, (g : Matrix (Fin n) (Fin n) K) = radicalMatrix v c := by
  rw [radicalGroup_eq hn]
  rfl

theorem mem_radicalGroup_of_dotProduct [CharP K 2] (hn : Even n) {i : Fin n} {g : GL (Fin n) K}
    {x : Fin n → K} (hx : onesVec ⬝ᵥ x = 0) {c : K}
    (hg : (g : Matrix (Fin n) (Fin n) K) = radicalMatrix x c) : g ∈ radicalGroup i := by
  refine (mem_radicalGroup hn).mpr ⟨x - x i • onesVec, mem_radicalW.mpr ⟨?_, ?_⟩, c, ?_⟩
  · rw [dotProduct_sub, dotProduct_smul, hx, onesVec_dotProduct_onesVec hn, smul_zero, sub_zero]
  · simp [onesVec_apply]
  · rw [hg, ← radicalMatrix_add_smul_onesVec (x - x i • onesVec) (x i) c, sub_add_cancel]

theorem radicalGroup_le [CharP K 2] (hn : Even n) (i : Fin n) :
    radicalGroup (K := K) i ≤ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K) := by
  intro g hg
  obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp hg
  rw [mem_matrixIsometryGroup, hc, Matrix.mul_one, radicalMatrix_transpose,
    radicalMatrix_mul_self hn (mem_radicalW.mp hv).1]

theorem mul_self_of_mem_radicalGroup [CharP K 2] (hn : Even n) {i : Fin n} {g : GL (Fin n) K}
    (hg : g ∈ radicalGroup i) : g * g = 1 := by
  obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp hg
  exact Units.ext (by
    rw [Units.val_mul, hc, radicalMatrix_mul_self hn (mem_radicalW.mp hv).1, Units.val_one])

theorem radicalGroup_comm [CharP K 2] (hn : Even n) {i : Fin n} {g h : GL (Fin n) K}
    (hg : g ∈ radicalGroup i) (hh : h ∈ radicalGroup i) : g * h = h * g := by
  obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp hg
  obtain ⟨v', hv', c', hc'⟩ := (mem_radicalGroup hn).mp hh
  have hdd := onesVec_dotProduct_onesVec (K := K) hn
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hc, hc',
    radicalMatrix_mul c c' hdd (mem_radicalW.mp hv).1 (mem_radicalW.mp hv').1,
    radicalMatrix_mul c' c hdd (mem_radicalW.mp hv').1 (mem_radicalW.mp hv).1, add_comm v,
    add_comm c, dotProduct_comm]

theorem isElementaryAbelian_radicalGroup [CharP K 2] (hn : Even n) (i : Fin n) :
    CFSG.IsElementaryAbelian 2 (radicalGroup (K := K) i) where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (radicalGroup_comm hn a.2 b.2)⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, sq, mul_self_of_mem_radicalGroup hn g.2]; rfl)

section Isometry

variable {g : GL (Fin n) K} (hg : g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K))
include hg

theorem transpose_mul_self_of_mem : (g : Matrix (Fin n) (Fin n) K)ᵀ * g = 1 := by
  have := mem_matrixIsometryGroup.mp hg
  rwa [Matrix.mul_one] at this

theorem dotProduct_mulVec_of_mem (x y : Fin n → K) :
    ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ⬝ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, transpose_mul_self_of_mem hg,
    vecMul_one]

theorem inv_eq_transpose_of_mem :
    ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K)ᵀ := by
  calc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = (g : Matrix (Fin n) (Fin n) K)ᵀ * g * ((g⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by rw [transpose_mul_self_of_mem hg, Matrix.one_mul]
    _ = (g : Matrix (Fin n) (Fin n) K)ᵀ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

variable [CharP K 2]

theorem onesVec_dotProduct_mulVec_of_mem (x : Fin n → K) :
    onesVec ⬝ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) = onesVec ⬝ᵥ x :=
  sq_injective_of_charTwo (by
    rw [← dotProduct_self_eq_sq, ← dotProduct_self_eq_sq, dotProduct_mulVec_of_mem hg])

theorem mulVec_onesVec_of_mem : (g : Matrix (Fin n) (Fin n) K) *ᵥ onesVec = onesVec := by
  have hdgv : onesVec ᵥ* (g : Matrix (Fin n) (Fin n) K) = onesVec := by
    funext j
    have := onesVec_dotProduct_mulVec_of_mem hg (Pi.single j 1)
    rwa [dotProduct_mulVec, dotProduct_single_one, dotProduct_single_one] at this
  have h2 : (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ = 1 :=
    mul_eq_one_comm.mp (transpose_mul_self_of_mem hg)
  calc (g : Matrix (Fin n) (Fin n) K) *ᵥ onesVec
      = (g : Matrix (Fin n) (Fin n) K) *ᵥ (onesVec ᵥ* (g : Matrix (Fin n) (Fin n) K)) := by
        rw [hdgv]
    _ = ((g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ) *ᵥ onesVec := by
        rw [← mulVec_transpose, mulVec_mulVec]
    _ = onesVec := by rw [h2, one_mulVec]

theorem conj_radicalMatrix (x : Fin n → K) (c : K) :
    (g : Matrix (Fin n) (Fin n) K) * radicalMatrix x c *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      radicalMatrix ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) c := by
  rw [inv_eq_transpose_of_mem hg]
  have h2 : (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ = 1 :=
    mul_eq_one_comm.mp (transpose_mul_self_of_mem hg)
  simp only [radicalMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, vecMul_transpose, mulVec_onesVec_of_mem hg, h2]

end Isometry

theorem matrix_eq_of_decomp [CharP K 2] (hn : Even n) {i : Fin n}
    {M N : Matrix (Fin n) (Fin n) K} (hd : M *ᵥ onesVec = N *ᵥ onesVec)
    (hW : ∀ w ∈ radicalW i, M *ᵥ w = N *ᵥ w) (he : M *ᵥ Pi.single i 1 = N *ᵥ Pi.single i 1) :
    M = N := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [eq_decomp i x, mulVec_add, mulVec_add, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul,
    mulVec_smul, mulVec_smul, hd, he, hW _ (decomp_mem_radicalW hn i x)]

theorem card_radicalGroup [Finite K] [CharP K 2] (hn : Even n) (i : Fin n) :
    Nat.card (radicalGroup (K := K) i) = Nat.card K ^ (n - 1) := by
  set B := Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K) with hB
  set L := LinearMap.ker (B onesVec) with hL
  have hmem : ∀ g : radicalGroup (K := K) i,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 - Pi.single i 1 ∈ L := by
    intro g
    rw [hL, LinearMap.mem_ker, hB, toBilin'_one_apply, dotProduct_sub,
      onesVec_dotProduct_mulVec_of_mem (radicalGroup_le hn i g.2), sub_self]
  let F : radicalGroup (K := K) i → L := fun g => ⟨_, hmem g⟩
  have hF : Function.Bijective F := by
    constructor
    · intro g g' hgg
      have h1 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 =
          ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 :=
        sub_left_injective (congrArg Subtype.val hgg)
      obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp g.2
      obtain ⟨v', hv', c', hc'⟩ := (mem_radicalGroup hn).mp g'.2
      rw [hc, hc', radicalMatrix_mulVec_single hv, radicalMatrix_mulVec_single hv'] at h1
      have h3 : c • onesVec + v + (1 : K) • Pi.single i 1 =
          c' • onesVec + v' + (1 : K) • Pi.single i 1 := by
        rw [one_smul]
        calc c • onesVec + v + Pi.single i 1 = Pi.single i 1 + v + c • onesVec := by abel
          _ = Pi.single i 1 + v' + c' • onesVec := h1
          _ = c' • onesVec + v' + Pi.single i 1 := by abel
      obtain ⟨hcc, hvv, -⟩ := decomp_unique hn hv hv' h3
      exact Subtype.ext (Units.ext (by rw [hc, hc', hcc, hvv]))
    · rintro ⟨x, hx⟩
      have hx1 : onesVec ⬝ᵥ x = 0 := by
        rw [hL, LinearMap.mem_ker, hB, toBilin'_one_apply] at hx
        exact hx
      have hv : x - x i • onesVec ∈ radicalW i := mem_radicalW.mpr ⟨by
        rw [dotProduct_sub, dotProduct_smul, hx1, onesVec_dotProduct_onesVec hn, smul_zero,
          sub_zero], by simp [onesVec_apply]⟩
      refine ⟨⟨radicalGL hn (mem_radicalW.mp hv).1 (x i),
        (mem_radicalGroup hn).mpr ⟨_, hv, x i, rfl⟩⟩, Subtype.ext ?_⟩
      change radicalMatrix (x - x i • onesVec) (x i) *ᵥ Pi.single i 1 - Pi.single i 1 = x
      rw [radicalMatrix_mulVec_single hv]
      abel
  rw [Nat.card_congr (Equiv.ofBijective F hF), Module.natCard_eq_pow_finrank (K := K)]
  congr 1
  have hsurj : Function.Surjective (B onesVec) := fun a => ⟨a • Pi.single i 1, by
    rw [map_smul, hB, toBilin'_one_apply, onesVec_dotProduct_single, smul_eq_mul, mul_one]⟩
  have hrk : Module.finrank K (LinearMap.range (B onesVec)) + Module.finrank K L =
      Module.finrank K (Fin n → K) := LinearMap.finrank_range_add_finrank_ker (B onesVec)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at hrk
  omega


section Projective

variable [Finite K] [CharP K 2]

theorem commute_dualAut_conjAut_iff (hn3 : 3 ≤ n) (A : GL (Fin n) K) :
    Commute (dualAut n K) (conjAut n K A) ↔
      ∃ g ∈ (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K) : Set (GL (Fin n) K)),
        conjAut n K A = conjAut n K g := by
  have h := commute_pureGraph_conjAut_iff (C := (1 : GL (Fin n) K)) isCanonicalGram_one hn3 A
  rwa [map_one, one_mul] at h

theorem commute_dualAut_of_mem (hn3 : 3 ≤ n) {g : GL (Fin n) K}
    (hg : g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)) :
    Commute (dualAut n K) (conjAut n K g) :=
  (commute_dualAut_conjAut_iff hn3 g).mpr ⟨g, hg, rfl⟩

theorem centralizer_dualAut_eq (hn3 : 3 ≤ n) :
    (centralizer {dualAut n K} : Set (MulAut (projectiveSL n K))) =
      {α | ∃ g ∈ (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K) : Set (GL (Fin n) K)),
        ∃ (φ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧ α = conjAut n K g * fieldAut n K φ * dualAut n K ^ ε} :=
  centralizer_eq_of_conjAut_commute_iff hn3 (fun φ => (fieldAut_commute_dualAut φ).symm)
    (Commute.refl _) _ (commute_dualAut_conjAut_iff hn3)

variable (hn : Even n) (hn3 : 3 ≤ n) (i : Fin n)

omit [Finite K] in
include hn in
theorem radicalImage_le_inner :
    (radicalGroup (K := K) i).map (conjAut n K) ≤
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  rintro _ ⟨g, hg, rfl⟩
  let g' : SpecialLinearGroup (Fin n) K := ⟨(g : Matrix (Fin n) (Fin n) K),
    det_eq_one_of_mem_matrixIsometryGroup (C := 1) (radicalGroup_le hn i hg)⟩
  refine ⟨proj n K g', ?_⟩
  rw [← conjAut_toGL]
  exact congrArg (conjAut n K) (Units.ext rfl)

include hn hn3 in
theorem radicalImage_le_centralizer :
    (radicalGroup (K := K) i).map (conjAut n K) ≤ centralizer {dualAut n K} := by
  rintro _ ⟨g, hg, rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (commute_dualAut_of_mem hn3 (radicalGroup_le hn i hg)).eq.symm

include hn hn3 in
theorem dualAut_mem_centralizer_radicalImage :
    dualAut n K ∈ centralizer (((radicalGroup (K := K) i).map (conjAut n K) :
      Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K))) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨h, hh, rfl⟩
  exact (commute_dualAut_of_mem hn3 (radicalGroup_le hn i hh)).eq.symm

include hn hn3 in
theorem radicalImage_normal :
    (((radicalGroup (K := K) i).map (conjAut n K)).subgroupOf
      (centralizer {dualAut n K})).Normal := by
  refine normal_of_conjAut_closed hn3 (fun φ => (fieldAut_commute_dualAut φ).symm)
    (Commute.refl _) _ (commute_dualAut_conjAut_iff hn3) (radicalGroup i) ?_ ?_ ?_
  · intro B hB g hg
    obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp hg
    refine mem_radicalGroup_of_dotProduct hn (x := (B : Matrix (Fin n) (Fin n) K) *ᵥ v) (c := c)
      ?_ ?_
    · rw [onesVec_dotProduct_mulVec_of_mem hB, (mem_radicalW.mp hv).1]
    · rw [Units.val_mul, Units.val_mul, hc, conj_radicalMatrix hB]
  · intro φ g hg
    obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp hg
    refine mem_radicalGroup_of_dotProduct hn (x := fun j => (φ : K →+* K) (v j))
      (c := (φ : K →+* K) c) ?_ ?_
    · have h1 := congrArg (φ : K →+* K) (mem_radicalW.mp hv).1
      rw [map_zero] at h1
      rw [← h1]
      simp [dotProduct, onesVec_apply, map_sum]
    · rw [GeneralLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk]
      change ((g : Matrix (Fin n) (Fin n) K)).map (φ : K →+* K) = _
      rw [hc, radicalMatrix_map]
  · intro g hg
    have h1 := (mem_matrixIsometryGroup_iff_inverseTranspose 1 g).mp (radicalGroup_le hn i hg)
    rw [h1, inv_one, mul_one, one_mul]
    exact hg

include hn hn3 in
theorem eq_radical_of_centralizes {g : GL (Fin n) K}
    (hg : g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
    (hc : ∀ h ∈ radicalGroup (K := K) i, conjAut n K g * fieldAut n K φ * conjAut n K h *
      (conjAut n K g * fieldAut n K φ)⁻¹ = conjAut n K h) :
    φ = 1 ∧ g ∈ radicalGroup i := by
  have hdd := onesVec_dotProduct_onesVec (K := K) hn
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hunip : ∀ M : GL (Fin n) K, M * M = 1 →
      ((M : Matrix (Fin n) (Fin n) K) - 1) * ((M : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
    intro M hM
    have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
      rw [← Units.val_mul, hM, Units.val_one]
    have h2 : ∀ X : Matrix (Fin n) (Fin n) K, X + X = 0 := fun X => by
      rw [← two_smul K X, h22, zero_smul]
    calc ((M : Matrix (Fin n) (Fin n) K) - 1) * ((M : Matrix (Fin n) (Fin n) K) - 1)
        = (M : Matrix (Fin n) (Fin n) K) * M + 1 - ((M : Matrix (Fin n) (Fin n) K) + M) := by
          noncomm_ring
      _ = 0 := by rw [hMM, h2, h2, sub_zero]
  have hmat : ∀ v ∈ radicalW i, ∀ c : K,
      radicalMatrix ((g : Matrix (Fin n) (Fin n) K) *ᵥ fun j => (φ : K →+* K) (v j))
        ((φ : K →+* K) c) = radicalMatrix v c := by
    intro v hv c
    have hv1 := (mem_radicalW.mp hv).1
    have hh : radicalGL hn hv1 c ∈ radicalGroup i := (mem_radicalGroup hn).mpr ⟨v, hv, c, rfl⟩
    have h1 := hc _ hh
    rw [conj_conjAut_fieldAut] at h1
    have hu := hunip _ (mul_self_of_mem_radicalGroup hn hh)
    have h2 := eq_of_conjAut_eq_of_unipotent hn3 (unipotent_conj (unipotent_map _ hu)) hu h1
    have h3 := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) h2
    simp only [Units.val_mul] at h3
    rw [← conj_radicalMatrix hg, ← radicalMatrix_map]
    exact h3
  have hφ : ∀ a : K, φ a = a := by
    intro a
    have h0 : (fun j => (φ : K →+* K) ((0 : Fin n → K) j)) = 0 := funext fun j => by simp
    have h1 := hmat 0 (zero_mem _) a
    rw [h0, mulVec_zero] at h1
    have h2 := congrFun (congrFun h1 i) i
    simp only [radicalMatrix, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
      onesVec_apply, Pi.zero_apply, mul_zero, add_zero, smul_eq_mul, mul_one,
      Matrix.one_apply_eq] at h2
    exact add_left_cancel h2
  have hφ' : ∀ x : K, (φ : K →+* K) x = x := hφ
  have hstar : ∀ w ∈ radicalW i, (g : Matrix (Fin n) (Fin n) K) *ᵥ w +
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) i • onesVec = w := by
    intro w hw
    have hwφ : (fun j => (φ : K →+* K) (w j)) = w := funext fun j => hφ' _
    have h1 := hmat w hw 0
    rw [hwφ, hφ' 0] at h1
    have h2 : radicalMatrix ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) 0 *ᵥ Pi.single i 1 =
        radicalMatrix w 0 *ᵥ Pi.single i 1 := by rw [h1]
    rw [radicalMatrix_mulVec, radicalMatrix_mulVec] at h2
    simp only [dotProduct_single_one, onesVec_apply, (mem_radicalW.mp hw).2, one_smul,
      zero_mul, zero_smul, add_zero] at h2
    rw [add_assoc] at h2
    rw [add_comm]
    exact add_left_cancel h2
  obtain ⟨ge, hge⟩ : ∃ x, x = (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 := ⟨_, rfl⟩
  have hdge : onesVec ⬝ᵥ ge = 1 := by
    rw [hge, onesVec_dotProduct_mulVec_of_mem hg, onesVec_dotProduct_single]
  obtain ⟨a₀, ha₀⟩ : ∃ a, a = ge i - onesVec ⬝ᵥ ge := ⟨_, rfl⟩
  have hv₀W : ge - a₀ • onesVec - (onesVec ⬝ᵥ ge) • Pi.single i 1 ∈ radicalW i := by
    rw [ha₀]
    exact decomp_mem_radicalW hn i ge
  obtain ⟨v₀, hv₀⟩ : ∃ v, v = ge - a₀ • onesVec - (onesVec ⬝ᵥ ge) • Pi.single i 1 := ⟨_, rfl⟩
  rw [← hv₀] at hv₀W
  have hge' : ge = Pi.single i 1 + v₀ + a₀ • onesVec := by
    rw [hv₀, hdge, one_smul]
    abel
  have hv₀1 := (mem_radicalW.mp hv₀W).1
  have hgw : ∀ w ∈ radicalW i,
      (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w + (v₀ ⬝ᵥ w) • onesVec := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_radicalW.mp hw
    obtain ⟨l, hl⟩ : ∃ l, l = ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) i := ⟨_, rfl⟩
    have hs := hstar w hw
    rw [← hl] at hs
    have hgw' : (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w + l • onesVec := by
      calc (g : Matrix (Fin n) (Fin n) K) *ᵥ w
          = ((g : Matrix (Fin n) (Fin n) K) *ᵥ w + l • onesVec) + l • onesVec := by
            rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero l, zero_smul, add_zero]
        _ = w + l • onesVec := by rw [hs]
    have hiso := dotProduct_mulVec_of_mem hg w (Pi.single i 1)
    rw [dotProduct_single_one, hw2, ← hge, hge', hgw'] at hiso
    have hwd : w ⬝ᵥ onesVec = 0 := by rw [dotProduct_comm, hw1]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      dotProduct_single_one, Pi.add_apply, Pi.smul_apply, onesVec_apply, hw2, hwd, hv₀1, hdd,
      smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at hiso
    have hl' : l = v₀ ⬝ᵥ w := by
      rw [dotProduct_comm]
      linear_combination hiso - (w ⬝ᵥ v₀) * h22
    rw [hgw', hl']
  have hgR : (g : Matrix (Fin n) (Fin n) K) = radicalMatrix v₀ a₀ := by
    refine matrix_eq_of_decomp hn (i := i) ?_ ?_ ?_
    · rw [mulVec_onesVec_of_mem hg, radicalMatrix_mulVec_onesVec hn hv₀W]
    · intro w hw
      rw [hgw w hw, radicalMatrix_mulVec_of_mem hw]
    · rw [← hge, hge', radicalMatrix_mulVec_single hv₀W]
  exact ⟨RingEquiv.ext hφ, (mem_radicalGroup hn).mpr ⟨v₀, hv₀W, a₀, hgR⟩⟩

include hn hn3 in
theorem exists_of_mem_centralizer_radicalImage {α : MulAut (projectiveSL n K)}
    (hα : α ∈ centralizer {dualAut n K} ⊓ centralizer (((radicalGroup (K := K) i).map
      (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K)))) :
    ∃ g ∈ radicalGroup (K := K) i, ∃ ε : ℕ, ε ≤ 1 ∧ α = conjAut n K g * dualAut n K ^ ε := by
  obtain ⟨hαM, hαR⟩ := mem_inf.mp hα
  have hα' : α ∈ (centralizer {dualAut n K} : Set (MulAut (projectiveSL n K))) := hαM
  rw [centralizer_dualAut_eq hn3] at hα'
  obtain ⟨g, hg, φ, ε, hε, rfl⟩ := hα'
  have hδR := dualAut_mem_centralizer_radicalImage (K := K) hn hn3 i
  have hx : conjAut n K g * fieldAut n K φ ∈ centralizer (((radicalGroup (K := K) i).map
      (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K))) := by
    have := mul_mem hαR (inv_mem (pow_mem hδR ε))
    rwa [mul_inv_cancel_right] at this
  obtain ⟨hφ, hgR⟩ := eq_radical_of_centralizes hn hn3 i hg φ fun h hh => by
    have := mem_centralizer_iff.mp hx (conjAut n K h) (mem_map_of_mem _ hh)
    rw [← this, mul_inv_cancel_right]
  exact ⟨g, hgR, ε, hε, by rw [hφ, map_one, mul_one]⟩

include hn hn3 in
theorem sq_eq_one_of_mem_centralizer_radicalImage {α : MulAut (projectiveSL n K)}
    (hα : α ∈ centralizer {dualAut n K} ⊓ centralizer (((radicalGroup (K := K) i).map
      (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K)))) :
    α ^ 2 = 1 := by
  obtain ⟨g, hg, ε, -, rfl⟩ := exists_of_mem_centralizer_radicalImage hn hn3 i hα
  obtain ⟨-, -, -, hdd, -⟩ := standard_automorphism_transport (n := n) (K := K)
  have hc : Commute (conjAut n K g) (dualAut n K ^ ε) :=
    ((commute_dualAut_of_mem hn3 (radicalGroup_le hn i hg)).pow_left ε).symm
  rw [hc.mul_pow, ← pow_mul, mul_comm ε 2, pow_mul, sq (dualAut n K), hdd, one_pow, mul_one, sq,
    ← map_mul, mul_self_of_mem_radicalGroup hn hg, map_one]

include hn hn3 in
theorem centralizer_radicalImage_eq :
    centralizer {dualAut n K} ⊓ centralizer (((radicalGroup (K := K) i).map (conjAut n K) :
      Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K))) =
        (radicalGroup (K := K) i).map (conjAut n K) ⊔ zpowers (dualAut n K) := by
  apply le_antisymm
  · intro α hα
    obtain ⟨g, hg, ε, -, rfl⟩ := exists_of_mem_centralizer_radicalImage hn hn3 i hα
    exact mul_mem (mem_sup_left (mem_map_of_mem _ hg))
      (mem_sup_right (pow_mem (mem_zpowers _) ε))
  · refine sup_le (le_inf (radicalImage_le_centralizer hn hn3 i) ?_) ?_
    · rintro _ ⟨g, hg, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨h, hh, rfl⟩
      rw [← map_mul, ← map_mul, radicalGroup_comm hn hh hg]
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
        dualAut_mem_centralizer_radicalImage hn hn3 i⟩

include hn hn3 in
theorem oddCore_inf_centralizer_dualAut {H : Subgroup (MulAut (projectiveSL n K))}
    (hH : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ H) :
    CFSG.oddCore ↥(H ⊓ centralizer {dualAut n K}) = ⊥ := by
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL
  have i : Fin n := ⟨0, by omega⟩
  refine EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer
    (R := (radicalGroup (K := K) i).map (conjAut n K))
    (le_inf ((radicalImage_le_inner hn i).trans hH) (radicalImage_le_centralizer hn hn3 i))
    ?_ ?_ ?_
  · intro x hx r hr
    have hxM : x ∈ centralizer {dualAut n K} := (mem_inf.mp hx).2
    have hrM := radicalImage_le_centralizer hn hn3 i hr
    have := (radicalImage_normal hn hn3 i).conj_mem ⟨r, hrM⟩ (mem_subgroupOf.mpr hr) ⟨x, hxM⟩
    rw [mem_subgroupOf] at this
    exact this
  · refine EvenCatalog.oddCore_eq_bot_of_forall_two_pow fun r => ⟨1, ?_⟩
    obtain ⟨g, hg, hgr⟩ := mem_map.mp r.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hgr, pow_one, sq, ← map_mul, mul_self_of_mem_radicalGroup hn hg,
      map_one]
    rfl
  · intro x hx hcx
    refine ⟨1, ?_⟩
    rw [pow_one]
    refine sq_eq_one_of_mem_centralizer_radicalImage hn hn3 i
      (mem_inf.mpr ⟨(mem_inf.mp hx).2, ?_⟩)
    rw [mem_centralizer_iff]
    intro r hr
    exact (hcx r hr).symm

end Projective

end NonalternatingRadical

open NonalternatingRadical

theorem even_linear_nonalternating_graph_radical {K : Type} [Field K] {f n r : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hr : n = 2 * r) (hn : 4 ≤ n) (i : Fin n) :
    (∀ v ∈ radicalW (K := K) i, ∀ c : K,
      radicalMatrix v c *ᵥ onesVec = onesVec ∧
      (∀ w ∈ radicalW i, radicalMatrix v c *ᵥ w = w + (v ⬝ᵥ w) • onesVec) ∧
      radicalMatrix v c *ᵥ Pi.single i 1 = Pi.single i 1 + v + c • onesVec ∧
      ∀ T : Matrix (Fin n) (Fin n) K, T *ᵥ onesVec = onesVec →
        (∀ w ∈ radicalW i, T *ᵥ w = w + (v ⬝ᵥ w) • onesVec) →
          T *ᵥ Pi.single i 1 = Pi.single i 1 + v + c • onesVec → T = radicalMatrix v c) ∧
    (∀ x : Fin n → K, ∃! p : K × radicalW (K := K) i × K,
      x = p.1 • onesVec + p.2.1.1 + p.2.2 • Pi.single i 1) ∧
    ((Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).restrict (radicalW i)).IsAlt ∧
    ((Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).restrict (radicalW i)).Nondegenerate ∧
    (∀ g : GL (Fin n) K, g ∈ radicalGroup i ↔
      ∃ v ∈ radicalW i, ∃ c : K, (g : Matrix (Fin n) (Fin n) K) = radicalMatrix v c) ∧
    (∀ v ∈ radicalW (K := K) i, ∀ c : K, radicalMatrix v c * radicalMatrix v c = 1) ∧
    radicalGroup (K := K) i ≤ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K) ∧
    CFSG.IsElementaryAbelian 2 (radicalGroup (K := K) i) ∧
    Nat.card (radicalGroup (K := K) i) = Nat.card K ^ (n - 1) ∧
    (radicalGroup (K := K) i).map (conjAut n K) ≤
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ∧
    (radicalGroup (K := K) i).map (conjAut n K) ≤ centralizer {dualAut n K} ∧
    (((radicalGroup (K := K) i).map (conjAut n K)).subgroupOf
      (centralizer {dualAut n K})).Normal ∧
    centralizer {dualAut n K} ⊓ centralizer (((radicalGroup (K := K) i).map (conjAut n K) :
      Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K))) =
        (radicalGroup (K := K) i).map (conjAut n K) ⊔ zpowers (dualAut n K) ∧
    IsPGroup 2 ↥((radicalGroup (K := K) i).map (conjAut n K) ⊔ zpowers (dualAut n K)) ∧
    ∀ H : Subgroup (MulAut (projectiveSL n K)),
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ H →
        CFSG.oddCore ↥(H ⊓ centralizer {dualAut n K}) = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hev : Even n := ⟨r, by omega⟩
  have hn3 : 3 ≤ n := by omega
  have hCM := centralizer_radicalImage_eq (K := K) hev hn3 i
  refine ⟨fun v hv c => ⟨radicalMatrix_mulVec_onesVec hev hv c,
    fun w hw => radicalMatrix_mulVec_of_mem hw c, radicalMatrix_mulVec_single hv c,
    fun T h1 h2 h3 => matrix_eq_of_decomp hev
      (h1.trans (radicalMatrix_mulVec_onesVec hev hv c).symm)
      (fun w hw => (h2 w hw).trans (radicalMatrix_mulVec_of_mem hw c).symm)
      (h3.trans (radicalMatrix_mulVec_single hv c).symm)⟩,
    existsUnique_decomp hev i, radicalW_isAlt i, radicalW_nondegenerate hev i,
    fun g => mem_radicalGroup hev,
    fun v hv c => radicalMatrix_mul_self hev (mem_radicalW.mp hv).1 c, radicalGroup_le hev i,
    isElementaryAbelian_radicalGroup hev i, card_radicalGroup hev i, radicalImage_le_inner hev i,
    radicalImage_le_centralizer hev hn3 i, radicalImage_normal hev hn3 i, hCM, fun x => ⟨1, ?_⟩,
    fun H hH => oddCore_inf_centralizer_dualAut hev hn3 hH⟩
  have hx : (x : MulAut (projectiveSL n K)) ∈ centralizer {dualAut n K} ⊓
      centralizer (((radicalGroup (K := K) i).map (conjAut n K) :
        Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K))) := by
    rw [hCM]
    exact x.2
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, pow_one]
  exact sq_eq_one_of_mem_centralizer_radicalImage hev hn3 i hx

end CFSG.ComponentClassification.UnbalancedCatalog
