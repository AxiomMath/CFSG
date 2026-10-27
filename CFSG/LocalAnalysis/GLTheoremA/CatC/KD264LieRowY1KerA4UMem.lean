module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Block
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

theorem pow_succ_of_mem_mu3 {Q : ℕ} (hdiv : 3 ∣ Q + 1) {d : Kˣ} (hd : d ∈ mu3 K) :
    d ^ (Q + 1) = 1 := by
  obtain ⟨m, hm⟩ := hdiv
  have h3 : d ^ 3 = 1 := (mem_rootsOfUnity 3 d).mp hd
  rw [hm, pow_mul, h3, one_pow]

@[expose] def diagUnit (d : Fin 4 → Kˣ) : GL (Fin 4) K :=
  ⟨diagM K d, diagM K (fun i => (d i)⁻¹), by
    rw [← diagM_mul K, ← diagM_one K]
    congr 1
    funext i
    simp, by
    rw [← diagM_mul K, ← diagM_one K]
    congr 1
    funext i
    simp⟩

theorem diagUnit_val (d : Fin 4 → Kˣ) : (diagUnit d : Matrix (Fin 4) (Fin 4) K) = diagM K d :=
  rfl

theorem diagUnit_mul (a b : Fin 4 → Kˣ) : diagUnit (a * b) = diagUnit a * diagUnit b := by
  apply Units.ext
  rw [Units.val_mul, diagUnit_val, diagUnit_val, diagUnit_val, diagM_mul]

theorem diagUnit_one : diagUnit (1 : Fin 4 → Kˣ) = 1 := by
  apply Units.ext
  rw [diagUnit_val, Units.val_one, diagM_one]

theorem diagUnit_mem {p f : ℕ} (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1)
    {d : Fin 4 → Kˣ} (hd : d ∈ dGroup K) : diagUnit d ∈ unitarySU p f K 4 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [diagUnit_val]
    exact det_diagM K hd.2
  · rw [diagUnit_val]
    unfold diagM
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h1 := pow_succ_of_mem_mu3 (K := K) hdiv (hd.1 i)
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at h2
    simp only [Function.comp, Pi.mul_apply, Pi.one_apply, h.bar_apply]
    exact h2

@[expose] def diagHomU (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) :
    dGroup K →* unitarySU p f K 4 where
  toFun d := ⟨diagUnit d.1, diagUnit_mem h hdiv d.2⟩
  map_one' := Subtype.ext diagUnit_one
  map_mul' a b := Subtype.ext (diagUnit_mul a.1 b.1)

theorem embM_mul (A B : Matrix (Fin 2) (Fin 2) K) : embM (A * B) = embM A * embM B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embM, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem embM_one : embM (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embM]

theorem embM_map (f' : K →+* K) (A : Matrix (Fin 2) (Fin 2) K) :
    (embM A).map f' = embM (A.map f') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embM]

theorem embM_transpose (A : Matrix (Fin 2) (Fin 2) K) : (embM A)ᵀ = embM Aᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embM]

theorem embM_unitary (f' : K →+* K) (A : Matrix (Fin 2) (Fin 2) K)
    (hA : (A.map f')ᵀ * A = 1) : ((embM A).map f')ᵀ * embM A = 1 := by
  rw [embM_map, embM_transpose, ← embM_mul, hA, embM_one]

theorem eq_one_of_embM_eq_one {X : Matrix (Fin 2) (Fin 2) K} (h : embM X = 1) : X = 1 := by
  ext i j
  have := congrFun (congrFun h (Fin.castLE (by norm_num) i)) (Fin.castLE (by norm_num) j)
  fin_cases i <;> fin_cases j <;> simp_all [embM]

@[expose] def embGL (A : GL (Fin 2) K) : GL (Fin 4) K :=
  ⟨embM (A : Matrix (Fin 2) (Fin 2) K), embM ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
    by rw [← embM_mul, Units.mul_inv, embM_one],
    by rw [← embM_mul, Units.inv_mul, embM_one]⟩

theorem embGL_val (A : GL (Fin 2) K) :
    (embGL A : Matrix (Fin 4) (Fin 4) K) = embM (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem embGL_mul (A B : GL (Fin 2) K) : embGL (A * B) = embGL A * embGL B :=
  Units.ext (by rw [embGL_val, Units.val_mul, embM_mul, Units.val_mul, embGL_val, embGL_val])

theorem embGL_one : embGL (1 : GL (Fin 2) K) = 1 :=
  Units.ext (by rw [embGL_val, Units.val_one, embM_one, Units.val_one])

theorem embGL_mem {p f : ℕ} (h : UnitaryFieldData p f K) {A : GL (Fin 2) K}
    (hA : A ∈ unitarySU p f K 2) : embGL A ∈ unitarySU p f K 4 := by
  rw [mem_unitarySU_iff h] at hA ⊢
  refine ⟨?_, ?_⟩
  · rw [embGL_val, det_embM]
    exact hA.1
  · rw [embGL_val]
    exact embM_unitary h.bar _ hA.2

@[expose] def embU {p f : ℕ} (h : UnitaryFieldData p f K) :
    unitarySU p f K 2 →* unitarySU p f K 4 where
  toFun A := ⟨embGL A.1, embGL_mem h A.2⟩
  map_one' := Subtype.ext embGL_one
  map_mul' a b := Subtype.ext (embGL_mul a.1 b.1)

theorem exists_embU_eq_of_isBlock {p f : ℕ} (h : UnitaryFieldData p f K) (g : GL (Fin 4) K)
    (hg : g ∈ unitarySU p f K 4) (hblock : IsBlock (g : Matrix (Fin 4) (Fin 4) K)) :
    ∃ B : unitarySU p f K 2, (embU h B : GL (Fin 4) K) = g := by
  rw [mem_unitarySU_iff h] at hg
  have hEq : embM !![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
      (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1] =
      (g : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    by_cases hij : i.val < 2 ∧ j.val < 2
    · fin_cases i <;> fin_cases j <;> simp_all [embM]
    · rw [hblock i j hij]
      fin_cases i <;> fin_cases j <;> simp_all [embM]
  have hdetB : (!![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
      (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1] :
      Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h1 := det_embM (!![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
      (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1] :
      Matrix (Fin 2) (Fin 2) K)
    rw [hEq, hg.1] at h1
    exact h1.symm
  have hunitB : ((!![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
      (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1] :
      Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * !![(g : Matrix (Fin 4) (Fin 4) K) 0 0,
      (g : Matrix (Fin 4) (Fin 4) K) 0 1; (g : Matrix (Fin 4) (Fin 4) K) 1 0,
      (g : Matrix (Fin 4) (Fin 4) K) 1 1] = 1 := by
    have h1 : ((embM !![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
        (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1]).map h.bar)ᵀ *
        embM !![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
        (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1] = 1 := by
      rw [hEq]
      exact hg.2
    rw [embM_map, embM_transpose, ← embM_mul] at h1
    exact eq_one_of_embM_eq_one h1
  generalize hBm : (!![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
      (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1] :
      Matrix (Fin 2) (Fin 2) K) = Bm at hEq hdetB hunitB
  have hu : IsUnit Bm.det := by
    rw [hdetB]
    exact isUnit_one
  let Bg : GL (Fin 2) K := ⟨Bm, Bm⁻¹, Matrix.mul_nonsing_inv Bm hu, Matrix.nonsing_inv_mul Bm hu⟩
  have hBgmem : Bg ∈ unitarySU p f K 2 := by
    rw [mem_unitarySU_iff h]
    exact ⟨hdetB, hunitB⟩
  refine ⟨⟨Bg, hBgmem⟩, ?_⟩
  apply Units.ext
  show (embGL Bg : Matrix (Fin 4) (Fin 4) K) = (g : Matrix (Fin 4) (Fin 4) K)
  rw [embGL_val]
  exact hEq

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
